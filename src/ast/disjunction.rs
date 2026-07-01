//! Lowering of `OR` disjunctions in rule bodies (materialized-union strategy).
//!
//! A body `C ∧ (D₁ ∨ … ∨ Dₙ)` is compiled by materializing the disjunction as an
//! internal relation `R(V)` keyed on the branches' common variables
//! `V = ⋂ᵢ vars(Dᵢ)`: one auxiliary rule per branch inserts `V` into `R`, and the
//! `OR` in the body is replaced by the single atom `R(V)`. The rest of the rule then
//! joins against `R` as an ordinary relation.
//!
//! Because a materialized relation is a set, this avoids the rule blowup and
//! redundant firing of naive rule-splitting; the cost is one extra derivation step
//! of latency (the branches populate `R` in one iteration, the main rule reads it in
//! the next), so programs must be run to fixpoint.
//!
//! Lowering runs after desugaring but before typechecking. Sorts for `V` are looked
//! up on demand via [`TypeInfo::typecheck_facts`], so no changes to the core query
//! pipeline are needed: everything downstream sees ordinary relations and rules.

use crate::ast::{Action, Actions, Command, Expr, Fact, Rule};
use crate::typechecking::{TypeError, TypeInfo};
use crate::util::{FreshGen, HashMap, HashSet, SymbolGen};
use crate::{ArcSort, Error};
use egglog_ast::generic_ast::{GenericActions, GenericExpr};
use egglog_ast::span::Span;
use indexmap::IndexSet;

/// Rewrites a command so that any `OR` in a rule body is replaced by a
/// materialized-union relation plus per-branch auxiliary rules. Commands without
/// disjunctions (and non-rule commands) are returned unchanged.
pub(crate) fn lower_disjunctions(
    type_info: &TypeInfo,
    symbol_gen: &mut SymbolGen,
    command: Command,
) -> Result<Vec<Command>, Error> {
    match command {
        Command::Rule { rule } if body_has_or(&rule.body) => {
            lower_rule(type_info, symbol_gen, rule)
        }
        Command::Fail(span, inner) => {
            // A subcommand may expand into several commands; mirror the desugaring
            // of `fail` and assert only the last of them fails.
            let mut lowered = lower_disjunctions(type_info, symbol_gen, *inner)?;
            let last = lowered
                .pop()
                .expect("lowering a command yields at least one command");
            lowered.push(Command::Fail(span, Box::new(last)));
            Ok(lowered)
        }
        other => Ok(vec![other]),
    }
}

fn body_has_or(body: &[Fact]) -> bool {
    body.iter().any(|f| matches!(f, Fact::Or(..)))
}

fn lower_rule(
    type_info: &TypeInfo,
    symbol_gen: &mut SymbolGen,
    rule: Rule,
) -> Result<Vec<Command>, Error> {
    // Infer a sort for every variable in the rule by typechecking the body with all
    // disjunctions flattened into a conjunction (an over-approximation that is fine
    // for typing).
    let flattened = flatten_for_typing(&rule.body);
    let resolved = type_info
        .typecheck_facts(symbol_gen, &flattened)
        .map_err(Error::TypeError)?;
    let mut var_sorts = HashMap::default();
    for fact in &resolved {
        fact.map_exprs(&mut |expr| {
            collect_resolved_var_sorts(expr, &mut var_sorts);
            expr.clone()
        });
    }

    let action_vars = actions_vars(&rule.head);
    let mut aux = Vec::new();
    let new_body = lower_fact_list(
        rule.body,
        &action_vars,
        &rule.ruleset,
        &var_sorts,
        symbol_gen,
        &mut aux,
    )?;

    aux.push(Command::Rule {
        rule: Rule {
            body: new_body,
            ..rule
        },
    });
    Ok(aux)
}

/// Lowers every `OR` in a list of facts, pushing the generated relations and
/// auxiliary rules onto `aux` and returning the disjunction-free facts.
///
/// `external` is the set of variables visible outside this fact list (the enclosing
/// scope and the actions); a branch-local variable must not appear there.
fn lower_fact_list(
    facts: Vec<Fact>,
    external: &HashSet<String>,
    ruleset: &str,
    var_sorts: &HashMap<String, ArcSort>,
    symbol_gen: &mut SymbolGen,
    aux: &mut Vec<Command>,
) -> Result<Vec<Fact>, Error> {
    let fact_vars: Vec<HashSet<String>> = facts.iter().map(fact_vars).collect();
    let mut new_facts = Vec::with_capacity(facts.len());
    for (i, fact) in facts.into_iter().enumerate() {
        match fact {
            Fact::Or(span, branches) => {
                // Everything outside this OR: the enclosing scope plus the other
                // facts of this list.
                let mut outside = external.clone();
                for (j, vars) in fact_vars.iter().enumerate() {
                    if j != i {
                        outside.extend(vars.iter().cloned());
                    }
                }
                new_facts.push(lower_or(
                    span, branches, &outside, ruleset, var_sorts, symbol_gen, aux,
                )?);
            }
            other => new_facts.push(other),
        }
    }
    Ok(new_facts)
}

fn lower_or(
    span: Span,
    branches: Vec<Vec<Fact>>,
    outside: &HashSet<String>,
    ruleset: &str,
    var_sorts: &HashMap<String, ArcSort>,
    symbol_gen: &mut SymbolGen,
    aux: &mut Vec<Command>,
) -> Result<Fact, Error> {
    // Lower any nested disjunctions inside each branch first (bottom-up), so the
    // relations they need are declared before the rules that reference them.
    let mut lowered_branches = Vec::with_capacity(branches.len());
    for branch in branches {
        if branch.is_empty() {
            return Err(Error::TypeError(TypeError::EmptyOrBranch(span.clone())));
        }
        lowered_branches.push(lower_fact_list(
            branch, outside, ruleset, var_sorts, symbol_gen, aux,
        )?);
    }

    // Common variables = intersection of the branches' variables, in the order they
    // first appear in the first branch.
    let branch_var_sets: Vec<HashSet<String>> =
        lowered_branches.iter().map(|b| fact_list_vars(b)).collect();
    let mut common: IndexSet<String> = ordered_vars(&lowered_branches[0]);
    common.retain(|v| branch_var_sets.iter().all(|s| s.contains(v.as_str())));

    // A variable local to some branch must not be used outside the OR: otherwise the
    // materialized relation, keyed only on the common variables, would drop a join.
    for vars in &branch_var_sets {
        for v in vars {
            if !common.contains(v) && outside.contains(v) {
                return Err(Error::TypeError(TypeError::OrBranchLocalEscapes(
                    v.clone(),
                    span.clone(),
                )));
            }
        }
    }

    let common: Vec<String> = common.into_iter().collect();
    let inputs: Vec<String> = common
        .iter()
        .map(|v| {
            var_sorts
                .get(v)
                .expect("common variable was typechecked")
                .name()
                .to_string()
        })
        .collect();

    let relation = symbol_gen.fresh("or_union");
    aux.push(Command::Relation {
        span: span.clone(),
        name: relation.clone(),
        inputs,
    });

    let insert = |sp: &Span| {
        Expr::Call(
            sp.clone(),
            relation.clone(),
            common
                .iter()
                .map(|v| Expr::Var(sp.clone(), v.clone()))
                .collect(),
        )
    };
    for branch in lowered_branches {
        aux.push(Command::Rule {
            rule: Rule {
                span: span.clone(),
                head: GenericActions(vec![Action::Expr(span.clone(), insert(&span))]),
                body: branch,
                name: symbol_gen.fresh("or_branch"),
                ruleset: ruleset.to_owned(),
                eval_mode: Default::default(),
                no_decomp: false,
                include_subsumed: false,
            },
        });
    }

    Ok(Fact::Fact(insert(&span)))
}

/// Replaces every `OR` with the conjunction of all its branches. The result binds a
/// superset of the real variables, which is all typechecking needs.
fn flatten_for_typing(body: &[Fact]) -> Vec<Fact> {
    let mut out = Vec::new();
    for fact in body {
        match fact {
            Fact::Or(_, branches) => {
                for branch in branches {
                    out.extend(flatten_for_typing(branch));
                }
            }
            other => out.push(other.clone()),
        }
    }
    out
}

fn collect_resolved_var_sorts(expr: &crate::ast::ResolvedExpr, out: &mut HashMap<String, ArcSort>) {
    match expr {
        GenericExpr::Var(_, v) => {
            out.entry(v.name.clone()).or_insert_with(|| v.sort.clone());
        }
        GenericExpr::Call(_, _, args) => {
            for arg in args {
                collect_resolved_var_sorts(arg, out);
            }
        }
        GenericExpr::Lit(..) => {}
    }
}

fn expr_vars(expr: &Expr, out: &mut HashSet<String>) {
    match expr {
        GenericExpr::Var(_, v) => {
            // Globals (`$`-prefixed) are always in scope and never branch-local.
            if !v.starts_with('$') {
                out.insert(v.clone());
            }
        }
        GenericExpr::Call(_, _, args) => args.iter().for_each(|a| expr_vars(a, out)),
        GenericExpr::Lit(..) => {}
    }
}

fn fact_vars(fact: &Fact) -> HashSet<String> {
    let mut out = HashSet::default();
    accumulate_fact_vars(fact, &mut out);
    out
}

fn accumulate_fact_vars(fact: &Fact, out: &mut HashSet<String>) {
    match fact {
        Fact::Eq(_, e1, e2) => {
            expr_vars(e1, out);
            expr_vars(e2, out);
        }
        Fact::Fact(e) => expr_vars(e, out),
        Fact::Or(_, branches) => branches
            .iter()
            .flatten()
            .for_each(|f| accumulate_fact_vars(f, out)),
    }
}

fn fact_list_vars(facts: &[Fact]) -> HashSet<String> {
    let mut out = HashSet::default();
    for fact in facts {
        accumulate_fact_vars(fact, &mut out);
    }
    out
}

/// Variables of a fact list in first-appearance order.
fn ordered_vars(facts: &[Fact]) -> IndexSet<String> {
    let mut out = IndexSet::new();
    for fact in facts {
        accumulate_fact_vars_ordered(fact, &mut out);
    }
    out
}

fn accumulate_fact_vars_ordered(fact: &Fact, out: &mut IndexSet<String>) {
    match fact {
        Fact::Eq(_, e1, e2) => {
            expr_vars_ordered(e1, out);
            expr_vars_ordered(e2, out);
        }
        Fact::Fact(e) => expr_vars_ordered(e, out),
        Fact::Or(_, branches) => branches
            .iter()
            .flatten()
            .for_each(|f| accumulate_fact_vars_ordered(f, out)),
    }
}

fn expr_vars_ordered(expr: &Expr, out: &mut IndexSet<String>) {
    match expr {
        GenericExpr::Var(_, v) => {
            if !v.starts_with('$') {
                out.insert(v.clone());
            }
        }
        GenericExpr::Call(_, _, args) => args.iter().for_each(|a| expr_vars_ordered(a, out)),
        GenericExpr::Lit(..) => {}
    }
}

fn actions_vars(actions: &Actions) -> HashSet<String> {
    let mut out = HashSet::default();
    for action in &actions.0 {
        action_exprs(action, &mut |e| expr_vars(e, &mut out));
    }
    out
}

fn action_exprs(action: &Action, f: &mut impl FnMut(&Expr)) {
    match action {
        Action::Let(_, _, e) => f(e),
        Action::Set(_, _, args, e) => {
            args.iter().for_each(&mut *f);
            f(e);
        }
        Action::Change(_, _, _, args) => args.iter().for_each(f),
        Action::Union(_, e1, e2) => {
            f(e1);
            f(e2);
        }
        Action::Panic(..) => {}
        Action::Expr(_, e) => f(e),
    }
}
