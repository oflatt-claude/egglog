//! Joint inference and completion of deferred calls.
use super::*;
use crate::constraint::{self, Constraint, TypeConstraint};

#[derive(Clone, Debug)]
pub(crate) struct DeferredCall {
    pub(super) name: String,
    pub(super) span: Span,
    pub(super) space: Space,
    pub(super) deferred: Deferred,
}

impl Primitive for DeferredCall {
    fn name(&self) -> &str {
        &self.name
    }
    fn get_type_constraints(&self, _span: &Span) -> Box<dyn TypeConstraint> {
        Box::new(self.clone())
    }
}

impl TypeConstraint for DeferredCall {
    fn get(
        &self,
        args: &[AtomTerm],
        _types: &TypeInfo,
    ) -> Vec<Box<dyn Constraint<AtomTerm, ArcSort>>> {
        if args.len() != self.deferred.operands.len() + 1 {
            return vec![constraint::impossible(
                constraint::ImpossibleConstraint::ArityMismatch {
                    atom: Atom {
                        span: self.span.clone(),
                        head: self.name.clone(),
                        args: args.to_vec(),
                    },
                    expected: self.deferred.operands.len() + 1,
                },
            )];
        }
        let mut constraints = Vec::new();
        for constraint in &self.deferred.constraints {
            constraints.push(match constraint {
                SortConstraint::Same(a, b) => constraint::eq(args[*a].clone(), args[*b].clone()),
                SortConstraint::Is(a, sort) => constraint::assign(args[*a].clone(), sort.clone()),
                SortConstraint::EqSort(a) => {
                    constraint::sort_predicate(args[*a].clone(), "an equality sort", |sort| {
                        sort.is_eq_sort()
                    })
                }
            });
        }
        if self.space == Space::Action {
            constraints.push(constraint::assign(
                args.last().unwrap().clone(),
                UnitSort.to_arcsort(),
            ));
        }
        constraints
    }
}

/// The inference boundary is an entire normalized rule, or one top-level action.
/// Synthetic calls exist only in this temporary environment; they never acquire
/// runtime implementations or appear in the emitted program.
pub(crate) fn check_deferred(
    types: &mut TypeInfo,
    parser: &mut Parser,
    command: &NCommand,
) -> Result<Option<Vec<ResolvedNCommand>>, Error> {
    let mut calls = IndexMap::default();
    command.clone().visit_exprs(&mut |expr| {
        if let Expr::Call(_, name, _) = &expr
            && let Some(call) = parser.deferred.get(name)
        {
            calls.insert(name.clone(), call.clone());
        }
        expr
    });
    if let NCommand::UserDefined(_, _, args) = command {
        for arg in args {
            arg.walk(
                &mut |expr| {
                    if let Expr::Call(_, name, _) = expr
                        && let Some(call) = parser.deferred.get(name)
                    {
                        calls.insert(name.clone(), call.clone());
                    }
                },
                &mut |_| {},
            );
        }
    }
    if calls.is_empty() {
        return Ok(None);
    }
    let fail = |span: Span, message: &str| Error::ParseError(ParseError(span, message.into()));
    let span = calls.values().next().unwrap().span.clone();
    if !matches!(command, NCommand::NormRule { .. } | NCommand::CoreAction(_)) {
        return Err(fail(
            span,
            "deferred macros require a rule head or top-level action; add an explicit declaration before this use",
        ));
    }
    if let NCommand::NormRule { rule } = command {
        for fact in &rule.body {
            let mut found = false;
            fact.clone().visit_exprs(&mut |expr| {
                if let Expr::Call(_, name, _) = &expr {
                    found |= calls.contains_key(name);
                }
                expr
            });
            if found {
                return Err(fail(
                    span,
                    "deferred macros in rule queries are not supported; move the declaration before the rule",
                ));
            }
        }
    }
    let mut working = types.clone();
    for call in calls.values() {
        working.add_deferred(call.clone());
    }
    let resolved = working.typecheck_command(&mut parser.symbol_gen, command).map_err(|error| {
        fail(span.clone(), &format!("could not infer deferred macro expansion: {error}\nadd a sort annotation or a constraining use in the same rule"))
    })?;
    // Eliminate constraint-only definitions before checking completion output.
    for name in calls.keys() {
        working.remove_deferred(name);
    }
    let mut query_vars = IndexMap::default();
    let mut bindings = IndexMap::default();
    let context = match &resolved {
        ResolvedNCommand::NormRule { rule } => {
            for fact in &rule.body {
                fact.visit_vars(&mut |span, var| {
                    if !var.is_global_ref {
                        query_vars.entry(var.name.clone()).or_insert(var.clone());
                        bindings.insert(var.name.clone(), (span.clone(), var.sort.clone()));
                    }
                });
            }
            rule.head.visit_vars(&mut |span, var| {
                if !var.is_global_ref {
                    bindings.insert(var.name.clone(), (span.clone(), var.sort.clone()));
                }
            });
            working.rule_contexts(rule.eval_mode).1
        }
        ResolvedNCommand::CoreAction(action) => {
            action.visit_vars(&mut |span, var| {
                if !var.is_global_ref {
                    bindings.insert(var.name.clone(), (span.clone(), var.sort.clone()));
                }
            });
            Context::Full
        }
        _ => unreachable!(),
    };
    let query_vars = query_vars.into_values().collect::<Vec<_>>();
    let mut declarations = Vec::new();
    let mut cx = FinishContext {
        span,
        query_bindings: &query_vars,
        context,
        is_rule: matches!(resolved, ResolvedNCommand::NormRule { .. }),
        types: &mut working,
        parser,
        declarations: &mut declarations,
    };
    let mut engine = CompletionEngine {
        cx: &mut cx,
        calls: &calls,
        bindings,
    };
    let completed = match resolved {
        ResolvedNCommand::NormRule { mut rule } => {
            let mut head = Vec::new();
            for action in rule.head.0 {
                engine.action(action, &mut head)?;
            }
            rule.head = ResolvedActions::new(head);
            if calls.keys().any(|name| rule.name.contains(name)) {
                rule.name.clear();
                rule.name = rule.to_string().replace('"', "'");
            }
            if context == Context::Write {
                engine
                    .cx
                    .types
                    .check_no_function_lookups_in_actions(&rule.head)?;
            }
            vec![ResolvedNCommand::NormRule { rule }]
        }
        ResolvedNCommand::CoreAction(action) => {
            let mut actions = Vec::new();
            engine.action(action, &mut actions)?;
            // Generated top-level temporary bindings are globals too.
            for action in &actions {
                if let ResolvedAction::Let(_, var, _) = action {
                    engine
                        .cx
                        .types
                        .global_sorts
                        .insert(var.name.clone(), var.sort.clone());
                }
            }
            actions
                .into_iter()
                .map(ResolvedNCommand::CoreAction)
                .collect()
        }
        _ => unreachable!(),
    };
    declarations.extend(completed);
    *types = working;
    Ok(Some(declarations))
}

struct CompletionEngine<'a, 'b, 'c> {
    cx: &'a mut FinishContext<'b>,
    calls: &'c IndexMap<String, DeferredCall>,
    bindings: IndexMap<String, (Span, ArcSort)>,
}

impl CompletionEngine<'_, '_, '_> {
    fn bind_operand(
        &mut self,
        expr: ResolvedExpr,
        actions: &mut Vec<ResolvedAction>,
    ) -> ResolvedExpr {
        if !matches!(expr, ResolvedExpr::Call(..)) {
            return expr;
        }
        let span = expr.span();
        let var = ResolvedVar {
            name: self.cx.fresh("macro_operand"),
            sort: expr.output_type(),
            is_global_ref: !self.cx.is_rule,
        };
        if var.is_global_ref {
            self.cx
                .types
                .global_sorts
                .insert(var.name.clone(), var.sort.clone());
        }
        self.bindings
            .insert(var.name.clone(), (span.clone(), var.sort.clone()));
        actions.push(ResolvedAction::Let(span.clone(), var.clone(), expr));
        ResolvedExpr::Var(span, var)
    }

    fn operands(
        &mut self,
        args: Vec<ResolvedExpr>,
        actions: &mut Vec<ResolvedAction>,
    ) -> Result<Vec<ResolvedExpr>, Error> {
        let mut result = Vec::new();
        for arg in args {
            let expanded = self.expr(arg, actions)?;
            result.push(self.bind_operand(expanded, actions));
        }
        Ok(result)
    }

    fn expr(
        &mut self,
        expr: ResolvedExpr,
        actions: &mut Vec<ResolvedAction>,
    ) -> Result<ResolvedExpr, Error> {
        let ResolvedExpr::Call(span, head, args) = expr else {
            return Ok(expr);
        };
        let args = self.operands(args, actions)?;
        let Some(call) = self.calls.get(head.name()) else {
            return Ok(ResolvedExpr::Call(span, head, args));
        };
        if call.space != Space::Expr {
            return Err(
                ParseError(span, "an action macro was used as an expression".into()).into(),
            );
        }
        self.cx.span = call.span.clone();
        let Completion::Expr(result) =
            (call.deferred.finish)(self.cx, &args, head.output().clone())?
        else {
            return Err(ParseError(
                span,
                "expression macro must finish with an expression".into(),
            )
            .into());
        };
        let binding = self
            .bindings
            .iter()
            .map(|(name, value)| (name.as_str(), value.clone()))
            .collect();
        let source = result
            .clone()
            .map_symbols(&mut |head| head.name().to_owned(), &mut |var| {
                var.name.clone()
            });
        let checked = self.cx.types.typecheck_expr_with_output(
            &mut self.cx.parser.symbol_gen,
            &source,
            &binding,
            head.output().clone(),
            self.cx.context,
        )?;
        if checked != result {
            return Err(ParseError(
                span.clone(),
                "macro completion changed a resolved type or overload".into(),
            )
            .into());
        }
        Ok(result)
    }

    fn action(
        &mut self,
        action: ResolvedAction,
        output: &mut Vec<ResolvedAction>,
    ) -> Result<(), Error> {
        if let ResolvedAction::Expr(_, ResolvedExpr::Call(ref span, ref head, ref args)) = action
            && let Some(call) = self.calls.get(head.name())
            && call.space == Space::Action
        {
            let operands = self.operands(args.clone(), output)?;
            self.cx.span = call.span.clone();
            let Completion::Actions(actions) =
                (call.deferred.finish)(self.cx, &operands, head.output().clone())?
            else {
                return Err(ParseError(
                    span.clone(),
                    "action macro must finish with actions".into(),
                )
                .into());
            };
            let binding = self
                .bindings
                .iter()
                .map(|(name, value)| (name.as_str(), value.clone()))
                .collect();
            let source = actions
                .clone()
                .map_symbols(&mut |head| head.name().to_owned(), &mut |var| {
                    var.name.clone()
                });
            let checked = self.cx.types.typecheck_standalone_actions(
                &mut self.cx.parser.symbol_gen,
                &source,
                &binding,
                self.cx.context,
            )?;
            if checked != actions {
                return Err(ParseError(
                    span.clone(),
                    "macro completion changed a resolved type or overload".into(),
                )
                .into());
            }
            for action in &actions.0 {
                if let ResolvedAction::Let(span, var, _) = action {
                    self.bindings
                        .insert(var.name.clone(), (span.clone(), var.sort.clone()));
                }
            }
            output.extend(actions.0);
        } else {
            let mut error = None;
            let action = action.map_exprs(&mut |expr| match self.expr(expr.clone(), output) {
                Ok(expr) => expr,
                Err(err) => {
                    error = Some(err);
                    expr.clone()
                }
            });
            if let Some(error) = error {
                return Err(error);
            }
            output.push(action);
        }
        Ok(())
    }
}
