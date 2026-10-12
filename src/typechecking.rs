use std::hash::Hasher;

use crate::Context;
use crate::proofs::proof_container_rebuild::register_container_rebuild_from_spec;
use crate::{
    core::{CoreActionContext, GenericActionsExt, ResolvedCall},
    *,
};
use ast::{
    MappedExprExt, ResolvedAction, ResolvedExpr, ResolvedFact, ResolvedRule, ResolvedVar, Rule,
    RuleEvalMode,
};
use core_relations::ExternalFunction;
use egglog_ast::generic_ast::GenericAction;
use egglog_bridge::ActionRegistry;
use enum_map::EnumMap;
use std::sync::{Arc, RwLock};

// `ExternalFunction` wrapper for `PurePrim`. Holds the primitive
// directly so the dispatch chain `external_funcs[id].invoke(...)` →
// `T::apply(...)` is just one vtable hop plus a direct call — no
// closure indirection that defeats inlining.
#[derive(Clone)]
struct PurePrimWrapper<T> {
    prim: T,
    /// The call-site [`Context`] this wrapper stamps onto the
    /// `PureState` before dispatching. `register_per_context` commits
    /// one wrapper per valid `Context` for the trait, so the
    /// typechecker's pick at each call site is encoded directly here.
    ctx: Context,
}

impl<T: PurePrim + Clone> ExternalFunction for PurePrimWrapper<T> {
    fn invoke(&self, exec_state: &mut ExecutionState, args: &[Value]) -> Option<Value> {
        self.prim.apply(PureState::wrap(exec_state, self.ctx), args)
    }
}

// `ExternalFunction` wrapper for primitives that need the
// `ActionRegistry` (`ReadPrim`, `WritePrim`, `FullPrim`). One generic
// over the `Wrap` strategy that knows how to construct the right
// state type and dispatch to the primitive's `apply`.
#[derive(Clone)]
struct RegistryPrimWrapper<T, S> {
    prim: T,
    registry: Arc<RwLock<ActionRegistry>>,
    /// Stamped onto the state wrapper.
    ctx: Context,
    _wrap: std::marker::PhantomData<fn() -> S>,
}

trait RegistryWrap<T>: Clone + Send + Sync {
    fn invoke(
        prim: &T,
        exec_state: &mut ExecutionState,
        ctx: Context,
        args: &[Value],
        registry: &ActionRegistry,
    ) -> Option<Value>;
}

#[derive(Clone)]
struct WrapRead;
impl<T: ReadPrim> RegistryWrap<T> for WrapRead {
    #[inline]
    fn invoke(
        prim: &T,
        exec_state: &mut ExecutionState,
        ctx: Context,
        args: &[Value],
        registry: &ActionRegistry,
    ) -> Option<Value> {
        prim.apply(ReadState::wrap(exec_state, registry, ctx), args)
    }
}
#[derive(Clone)]
struct WrapWrite;
impl<T: WritePrim> RegistryWrap<T> for WrapWrite {
    #[inline]
    fn invoke(
        prim: &T,
        exec_state: &mut ExecutionState,
        ctx: Context,
        args: &[Value],
        registry: &ActionRegistry,
    ) -> Option<Value> {
        prim.apply(WriteState::wrap(exec_state, registry, ctx), args)
    }
}
#[derive(Clone)]
struct WrapFull;
impl<T: FullPrim> RegistryWrap<T> for WrapFull {
    #[inline]
    fn invoke(
        prim: &T,
        exec_state: &mut ExecutionState,
        ctx: Context,
        args: &[Value],
        registry: &ActionRegistry,
    ) -> Option<Value> {
        prim.apply(FullState::wrap(exec_state, registry, ctx), args)
    }
}

impl<T: Clone + Send + Sync + 'static, S: RegistryWrap<T> + 'static> ExternalFunction
    for RegistryPrimWrapper<T, S>
{
    fn invoke(&self, exec_state: &mut ExecutionState, args: &[Value]) -> Option<Value> {
        let registry = self.registry.read().unwrap();
        S::invoke(&self.prim, exec_state, self.ctx, args, &registry)
    }
}

#[derive(Clone, Debug)]
pub struct FuncType {
    pub name: String,
    pub subtype: FunctionSubtype,
    pub input: Vec<ArcSort>,
    pub output: ArcSort,
}

impl PartialEq for FuncType {
    fn eq(&self, other: &Self) -> bool {
        if self.name == other.name
            && self.subtype == other.subtype
            && self.output.name() == other.output.name()
        {
            if self.input.len() != other.input.len() {
                return false;
            }
            for (a, b) in self.input.iter().zip(other.input.iter()) {
                if a.name() != b.name() {
                    return false;
                }
            }
            true
        } else {
            false
        }
    }
}

impl Eq for FuncType {}

impl Hash for FuncType {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.name.hash(state);
        self.subtype.hash(state);
        self.output.name().hash(state);
        for inp in &self.input {
            inp.name().hash(state);
        }
    }
}
/// Validators take a termdag and arguments (as TermIds) and return
/// a newly computed TermId if the primitive application is valid,
/// or None if it is invalid.
pub(crate) type PrimitiveRuntime = EnumMap<Context, Option<ExternalFunctionId>>;
pub(crate) type PrimitiveRuntimes = HashMap<usize, PrimitiveRuntime>;

pub type PrimitiveValidator = Arc<dyn Fn(&mut TermDag, &[TermId]) -> Option<TermId> + Send + Sync>;

#[derive(Clone)]
pub struct PrimitiveDefinition {
    pub(crate) primitive: Arc<dyn Primitive>,
    pub(crate) validator: Option<PrimitiveValidator>,
    pub(crate) id: usize,
    pub(crate) valid_contexts: Vec<Context>,
    pub(crate) install:
        Option<Arc<dyn Fn(&mut egglog_bridge::EGraph) -> PrimitiveRuntime + Send + Sync>>,
}

impl PrimitiveDefinition {
    /// Takes the full signature of a primitive (both input and output types).
    /// Returns whether the primitive is compatible with this signature.
    pub fn accept(&self, tys: &[Arc<dyn Sort>], typeinfo: &TypeInfo) -> bool {
        let mut constraints = vec![];
        let lits: Vec<_> = (0..tys.len())
            .map(|i| AtomTerm::Literal(Span::Panic, Literal::Int(i as i64)))
            .collect();
        for (lit, ty) in lits.iter().zip(tys.iter()) {
            constraints.push(constraint::assign(lit.clone(), ty.clone()))
        }
        constraints.extend(
            self.primitive
                .get_type_constraints(&Span::Panic)
                .get(&lits, typeinfo),
        );
        let problem = Problem {
            constraints,
            range: HashSet::default(),
        };
        problem.solve(|sort| sort.name()).is_ok()
    }

    /// Returns whether this primitive has a runtime entrypoint for `context`.
    pub fn is_valid_in_context(&self, context: Context) -> bool {
        self.valid_contexts.contains(&context)
    }
}

impl Debug for PrimitiveDefinition {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Prim({})", self.primitive.name())
    }
}

/// Stores resolved typechecking information.
#[derive(Clone)]
pub struct TypeInfo {
    /// Whether default rules use seminaive evaluation. Also determines inference contexts.
    pub seminaive: bool,
    mksorts: HashMap<String, MkSort>,
    // TODO(yz): I want to get rid of this as now we have user-defined primitives and constraint based type checking
    reserved_primitives: HashSet<&'static str>,
    pub(crate) sorts: HashMap<String, Arc<dyn Sort>>,
    primitives: HashMap<String, Vec<PrimitiveDefinition>>,
    func_types: HashMap<String, Arc<FuncType>>,
    pub(crate) global_sorts: HashMap<String, ArcSort>,
    /// Sorts that do not allow union (e.g., from `:no-union` sorts or relations).
    pub(crate) non_unionable_sorts: HashSet<String>,
    /// Function declarations hidden from user-facing table listings.
    pub(crate) hidden_functions: HashSet<String>,
}

impl TypeInfo {
    /// Add a user-defined sort to the e-graph.
    ///
    /// Also look at [`prelude::add_base_sort`] for a convenience method for adding user-defined sorts
    pub fn add_sort<S: Sort + 'static>(&mut self, sort: S, span: Span) -> Result<(), TypeError> {
        self.add_arcsort(Arc::new(sort), span)
    }

    /// Declare a sort. This corresponds to the `sort` keyword in egglog.
    /// It can either declares a new [`EqSort`] if `presort_and_args` is not provided,
    /// or an instantiation of a presort (e.g., containers like `Vec`).
    pub fn declare_sort(
        &mut self,
        name: impl Into<String>,
        presort_and_args: &Option<(String, Vec<Expr>)>,
        span: Span,
    ) -> Result<(), TypeError> {
        let name = name.into();
        if self.func_types.contains_key(&name) {
            return Err(TypeError::FunctionAlreadyBound(name, span));
        }

        let sort = match presort_and_args {
            None => Arc::new(EqSort { name }),
            Some((presort, args)) => {
                if let Some(mksort) = self.mksorts.get(presort) {
                    mksort(self, name, args, span.clone())?
                } else {
                    return Err(TypeError::PresortNotFound(presort.clone(), span));
                }
            }
        };

        self.add_arcsort(sort, span)
    }

    /// Add a user-defined sort to the e-graph.
    pub fn add_arcsort(&mut self, sort: ArcSort, span: Span) -> Result<(), TypeError> {
        let name = sort.name();
        match self.sorts.entry(name.to_owned()) {
            HEntry::Occupied(_) => Err(TypeError::SortAlreadyBound(name.to_owned(), span)),
            HEntry::Vacant(e) => {
                e.insert(sort.clone());
                sort.register_primitives(self);
                Ok(())
            }
        }
    }

    /// Register a [`PurePrim`]. Pass `None` for the validator if not
    /// using the proof checker.
    ///
    /// Pick the trait whose state wrapper matches the body's needs:
    /// [`PurePrim`] for pure ops, [`WritePrim`] for writes,
    /// [`ReadPrim`] for table reads, [`FullPrim`] for both. The Rust
    /// type checker enforces the body only uses methods the chosen
    /// state allows.
    pub fn add_pure_primitive<T>(&mut self, x: T, validator: Option<PrimitiveValidator>)
    where
        T: PurePrim + Clone,
    {
        self.register_per_context(x, validator, PureState::valid_contexts(), |x, ctx, _| {
            Box::new(PurePrimWrapper { prim: x, ctx })
        });
    }

    /// Register a [`WritePrim`]. Pass `None` for the validator if not
    /// using the proof checker.
    pub fn add_write_primitive<T>(&mut self, x: T, validator: Option<PrimitiveValidator>)
    where
        T: WritePrim + Clone,
    {
        self.register_registry_primitive::<T, WrapWrite>(
            x,
            validator,
            WriteState::valid_contexts(),
        );
    }

    /// Register a [`ReadPrim`]. Pass `None` for the validator if not
    /// using the proof checker.
    pub fn add_read_primitive<T>(&mut self, x: T, validator: Option<PrimitiveValidator>)
    where
        T: ReadPrim + Clone,
    {
        self.register_registry_primitive::<T, WrapRead>(x, validator, ReadState::valid_contexts());
    }

    /// Register a [`FullPrim`]. Pass `None` for the validator if not
    /// using the proof checker.
    pub fn add_full_primitive<T>(&mut self, x: T, validator: Option<PrimitiveValidator>)
    where
        T: FullPrim + Clone,
    {
        self.register_registry_primitive::<T, WrapFull>(x, validator, FullState::valid_contexts());
    }

    fn register_registry_primitive<T, S>(
        &mut self,
        x: T,
        validator: Option<PrimitiveValidator>,
        valid_ctxs: &[Context],
    ) where
        T: Primitive + Clone,
        S: RegistryWrap<T> + 'static,
    {
        self.register_per_context(x, validator, valid_ctxs, move |x, ctx, backend| {
            let registry = backend.action_registry().clone();
            Box::new(RegistryPrimWrapper::<T, S> {
                prim: x,
                registry: registry.clone(),
                ctx,
                _wrap: std::marker::PhantomData,
            })
        });
    }

    /// Record a definition and a backend installer. Installation allocates one
    /// runtime entry point per valid context, carrying that call-site context.
    ///
    /// The typechecker filters by the declared context mask at each call site;
    /// an `unstable-fn` value built around the primitive bakes *all*
    /// signature-matching context ids, and `FunctionContainer::apply`
    /// picks the one whose context matches the application ctx — so
    /// values flow freely across contexts.
    fn register_per_context<T, F>(
        &mut self,
        x: T,
        validator: Option<PrimitiveValidator>,
        valid_ctxs: &[Context],
        build_wrapper: F,
    ) where
        T: Primitive + Clone,
        F: Fn(T, Context, &egglog_bridge::EGraph) -> Box<dyn ExternalFunction>
            + Send
            + Sync
            + 'static,
    {
        let primitive: Arc<dyn Primitive> = Arc::new(x.clone());
        let name = primitive.name().to_owned();
        let valid_contexts = valid_ctxs.to_vec();
        let contexts = valid_contexts.clone();
        let install = Arc::new(move |backend: &mut egglog_bridge::EGraph| {
            EnumMap::from_fn(|ctx| {
                contexts.contains(&ctx).then(|| {
                    let wrapper = build_wrapper(x.clone(), ctx, backend);
                    backend.register_external_func(wrapper)
                })
            })
        });
        let entries = self.primitives.entry(name).or_default();
        let pending = entries
            .iter()
            .position(|definition| definition.install.is_none());
        let id = pending
            .map(|index| entries.remove(index).id)
            .unwrap_or_else(next_primitive_id);
        entries.push(PrimitiveDefinition {
            primitive,
            validator,
            valid_contexts,
            install: Some(install),
            id,
        });
    }
}

impl TypeInfo {
    pub fn typecheck_program(
        &mut self,
        symbol_gen: &mut SymbolGen,
        program: &[NCommand],
    ) -> Result<Vec<ResolvedNCommand>, TypeError> {
        let mut result = vec![];
        for command in program {
            result.push(self.typecheck_command(symbol_gen, command)?);
        }
        Ok(result)
    }

    pub fn typecheck_command(
        &mut self,
        symbol_gen: &mut SymbolGen,
        command: &NCommand,
    ) -> Result<ResolvedNCommand, TypeError> {
        let command: ResolvedNCommand = match command {
            NCommand::Function(fdecl) => {
                let resolved = self.typecheck_function(symbol_gen, fdecl)?;
                // If this is a let binding, add it to global_sorts
                // This preserves bahavior for lets after desugaring
                if resolved.internal_let {
                    let output_sort = self.sorts.get(&fdecl.schema.output).unwrap();
                    self.global_sorts
                        .insert(fdecl.name.clone(), output_sort.clone());
                }
                ResolvedNCommand::Function(resolved)
            }
            NCommand::NormRule { rule } => ResolvedNCommand::NormRule {
                rule: self.typecheck_rule(symbol_gen, rule)?,
            },
            NCommand::Sort {
                span,
                name,
                presort_and_args,
                uf,
                proof_func,
                container_rebuild,
                proof_constructors,
                unionable,
            } => {
                // Note this is bad since typechecking should be pure and idempotent
                // Otherwise typechecking the same program twice will fail
                self.declare_sort(name.clone(), presort_and_args, span.clone())?;
                // Mark as non-unionable if the sort declaration says so
                if !unionable {
                    self.non_unionable_sorts.insert(name.clone());
                }
                ResolvedNCommand::Sort {
                    span: span.clone(),
                    name: name.clone(),
                    presort_and_args: presort_and_args.clone(),
                    uf: uf.clone(),
                    proof_func: proof_func.clone(),
                    container_rebuild: container_rebuild.clone(),
                    proof_constructors: proof_constructors.clone(),
                    unionable: *unionable,
                }
            }
            NCommand::CoreAction(action @ Action::Let(_, _, _)) => {
                let action = self.typecheck_standalone_action(
                    symbol_gen,
                    action,
                    &Default::default(),
                    Context::Full,
                )?;
                let ResolvedAction::Let(_, resolved_var, _) = &action else {
                    unreachable!("typechecking an Action::Let should return ResolvedAction::Let")
                };
                self.global_sorts
                    .insert(resolved_var.name.clone(), resolved_var.sort.clone());
                ResolvedNCommand::CoreAction(action)
            }
            NCommand::CoreAction(action) => {
                ResolvedNCommand::CoreAction(self.typecheck_standalone_action(
                    symbol_gen,
                    action,
                    &Default::default(),
                    Context::Full,
                )?)
            }
            NCommand::Extract(span, expr, variants) => {
                let res_expr = self.typecheck_standalone_expr(
                    symbol_gen,
                    expr,
                    &Default::default(),
                    Context::Full,
                )?;

                let res_variants = self.typecheck_standalone_expr(
                    symbol_gen,
                    variants,
                    &Default::default(),
                    Context::Full,
                )?;
                if res_variants.output_type().name() != I64Sort.name() {
                    return Err(TypeError::Mismatch {
                        expr: variants.clone(),
                        expected: I64Sort.to_arcsort(),
                        actual: res_variants.output_type(),
                    });
                }

                ResolvedNCommand::Extract(span.clone(), res_expr, res_variants)
            }
            NCommand::Check(span, facts) => {
                ResolvedNCommand::Check(span.clone(), self.typecheck_facts(symbol_gen, facts)?)
            }
            NCommand::Fail(span, cmd) => ResolvedNCommand::Fail(
                span.clone(),
                Box::new(self.typecheck_command(symbol_gen, cmd)?),
            ),
            NCommand::RunSchedule(schedule) => {
                ResolvedNCommand::RunSchedule(self.typecheck_schedule(symbol_gen, schedule)?)
            }
            NCommand::Pop(span, n) => ResolvedNCommand::Pop(span.clone(), *n),
            NCommand::Push(n) => ResolvedNCommand::Push(*n),
            NCommand::AddRuleset(span, ruleset) => {
                ResolvedNCommand::AddRuleset(span.clone(), ruleset.clone())
            }
            NCommand::UnstableCombinedRuleset(span, name, sub_rulesets) => {
                ResolvedNCommand::UnstableCombinedRuleset(
                    span.clone(),
                    name.clone(),
                    sub_rulesets.clone(),
                )
            }
            NCommand::PrintOverallStatistics(span, file) => {
                ResolvedNCommand::PrintOverallStatistics(span.clone(), file.clone())
            }
            NCommand::PrintFunction(span, table, size, file, mode) => {
                ResolvedNCommand::PrintFunction(
                    span.clone(),
                    table.clone(),
                    *size,
                    file.clone(),
                    *mode,
                )
            }
            NCommand::PrintSize(span, n) => {
                // Should probably also resolve the function symbol here
                ResolvedNCommand::PrintSize(span.clone(), n.clone())
            }
            NCommand::ProveExists(span, constructor) => {
                let func_type = self
                    .get_func_type(constructor)
                    .ok_or_else(|| TypeError::UnboundFunction(constructor.clone(), span.clone()))?;
                if func_type.subtype != FunctionSubtype::Constructor {
                    return Err(TypeError::ProveExistsRequiresConstructor(
                        constructor.clone(),
                        span.clone(),
                    ));
                }
                ResolvedNCommand::ProveExists(span.clone(), ResolvedCall::Func(func_type.clone()))
            }
            NCommand::Output { span, file, exprs } => {
                let exprs = exprs
                    .iter()
                    .map(|expr| {
                        self.typecheck_standalone_expr(
                            symbol_gen,
                            expr,
                            &Default::default(),
                            Context::Full,
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                ResolvedNCommand::Output {
                    span: span.clone(),
                    file: file.clone(),
                    exprs,
                }
            }
            NCommand::Input { span, name, file } => ResolvedNCommand::Input {
                span: span.clone(),
                name: name.clone(),
                file: file.clone(),
            },
            NCommand::UserDefined(span, name, exprs) => {
                ResolvedNCommand::UserDefined(span.clone(), name.clone(), exprs.clone())
            }
        };
        Ok(command)
    }
}

impl EGraph {
    pub(crate) fn typecheck_program(
        &mut self,
        program: &[NCommand],
    ) -> Result<Vec<ResolvedNCommand>, TypeError> {
        let mut result = Vec::new();
        for command in program {
            if let NCommand::CoreAction(Action::Let(span, var, _)) = command {
                self.ensure_global_name_prefix(span, var)?;
            }
            if let Some(expanded) =
                crate::macros::check_deferred(&mut self.type_info, &mut self.parser, command)
                    .map_err(|error| TypeError::MacroExpansion(error.to_string()))?
            {
                self.install_type_info();
                for command in expanded {
                    if let ResolvedNCommand::NormRule { rule } = &command {
                        self.warn_for_prefixed_non_globals_in_rule(rule)?;
                    }
                    result.push(self.bind_command_primitives(command));
                }
                continue;
            }
            let resolved = self
                .type_info
                .typecheck_command(&mut self.parser.symbol_gen, command)?;
            self.install_type_info();
            if let NCommand::Sort {
                name,
                uf,
                proof_func,
                proof_constructors,
                container_rebuild,
                ..
            } = command
            {
                // Record this sort's UF / proof tables in proof_state (as
                // run_command also does) so the container rebuild registration
                // below can recover them — including this container's own proof
                // table, which has not run yet.
                if let Some((uf_ctor, uf_index)) = uf {
                    self.proof_state
                        .uf_parent
                        .insert(name.clone(), uf_ctor.clone());
                    if let Some(uf_index) = uf_index {
                        self.proof_state
                            .uf_function
                            .insert(name.clone(), uf_index.clone());
                    }
                }
                if let Some(pf) = proof_func {
                    self.proof_state
                        .proof_func_parent
                        .insert(name.clone(), pf.clone());
                }
                // The Proof sort records the global proof constructors; restore
                // them into proof_state so container rebuild can recover them
                // (the `Proof` datatype name is this sort's own name).
                if let Some(pc) = proof_constructors {
                    let names = &mut self.proof_state.proof_names;
                    names.proof_datatype = name.clone();
                    names.congr_constructor = pc.congr.clone();
                    names.eq_trans_constructor = pc.trans.clone();
                    names.eq_sym_constructor = pc.sym.clone();
                    names.container_normalize_constructor = pc.normalize.clone();
                }
                // A container sort under the term/proof encoding carries a spec
                // for its rebuild primitives; register them here so they are
                // available both during encoding and when the desugared program
                // is re-parsed.
                if let Some(spec) = container_rebuild {
                    register_container_rebuild_from_spec(self, name, spec);
                }
            }
            if let ResolvedNCommand::NormRule { rule } = &resolved {
                self.warn_for_prefixed_non_globals_in_rule(rule)?;
            }
            result.push(self.bind_command_primitives(resolved));
        }
        Ok(result)
    }

    fn warn_for_prefixed_non_globals_in_var(
        &mut self,
        span: &Span,
        var: &ResolvedVar,
    ) -> Result<(), TypeError> {
        if var.is_global_ref {
            return Ok(());
        }
        if var.name.starts_with(crate::GLOBAL_NAME_PREFIX) {
            self.warn_prefixed_non_globals(span, &var.name)?;
        }
        Ok(())
    }

    fn warn_for_prefixed_non_globals_in_rule(
        &mut self,
        rule: &ResolvedRule,
    ) -> Result<(), TypeError> {
        let mut res: Result<(), TypeError> = Ok(());

        for fact in &rule.body {
            fact.visit_vars(&mut |span, var| {
                if res.is_ok() {
                    res = self.warn_for_prefixed_non_globals_in_var(span, var);
                }
            });
        }

        rule.head.visit_vars(&mut |span, var| {
            if res.is_ok() {
                res = self.warn_for_prefixed_non_globals_in_var(span, var);
            }
        });
        res
    }
}

impl TypeInfo {
    /// Adds a sort constructor to the typechecker's known set of types.
    pub fn add_presort<S: Presort>(&mut self, span: Span) -> Result<(), TypeError> {
        let name = S::presort_name();
        match self.mksorts.entry(name.to_owned()) {
            HEntry::Occupied(_) => Err(TypeError::SortAlreadyBound(name.to_owned(), span)),
            HEntry::Vacant(e) => {
                e.insert(S::make_sort);
                self.reserved_primitives.extend(S::reserved_primitives());
                Ok(())
            }
        }
    }

    /// Returns all sorts that satisfy the type and predicate.
    pub fn get_sorts_by<S: Sort>(&self, pred: impl Fn(&Arc<S>) -> bool) -> Vec<Arc<S>> {
        let mut results = Vec::new();
        for sort in self.sorts.values() {
            let sort = sort.clone().as_arc_any();
            if let Ok(sort) = Arc::downcast(sort)
                && pred(&sort)
            {
                results.push(sort);
            }
        }
        results
    }

    /// Returns all sorts based on the type.
    pub fn get_sorts<S: Sort>(&self) -> Vec<Arc<S>> {
        self.get_sorts_by(|_| true)
    }

    /// Returns a sort that satisfies the type and predicate.
    pub fn get_sort_by<S: Sort>(&self, pred: impl Fn(&Arc<S>) -> bool) -> Arc<S> {
        let results = self.get_sorts_by(pred);
        assert_eq!(
            results.len(),
            1,
            "Expected exactly one sort for type {}",
            std::any::type_name::<S>()
        );
        results.into_iter().next().unwrap()
    }

    /// Returns a sort based on the type.
    pub fn get_sort<S: Sort>(&self) -> Arc<S> {
        self.get_sort_by(|_| true)
    }

    /// Returns all sorts that satisfy the predicate.
    pub fn get_arcsorts_by(&self, f: impl Fn(&ArcSort) -> bool) -> Vec<ArcSort> {
        self.sorts.values().filter(|&x| f(x)).cloned().collect()
    }

    /// Returns a sort based on the predicate.
    pub fn get_arcsort_by(&self, f: impl Fn(&ArcSort) -> bool) -> ArcSort {
        let results = self.get_arcsorts_by(f);
        assert_eq!(
            results.len(),
            1,
            "Expected exactly one sort matching the given predicate"
        );
        results.into_iter().next().unwrap()
    }

    /// Returns the unique sort whose runtime values have Rust type `T`.
    pub fn get_arcsort_for_value_type<T: 'static>(&self) -> ArcSort {
        let results = self.get_arcsorts_by(|s| s.value_type() == Some(std::any::TypeId::of::<T>()));
        assert_eq!(
            results.len(),
            1,
            "Expected exactly one sort for type `{}`",
            std::any::type_name::<T>()
        );
        results.into_iter().next().unwrap()
    }

    /// Check if a sort allows union operations.
    /// A sort is unionable if it's an eq_sort and not marked as non-unionable
    /// (e.g., from `(sort Foo :no-union)` or relation desugaring).
    pub fn is_sort_unionable(&self, sort: &ArcSort) -> bool {
        sort.is_eq_sort() && !self.non_unionable_sorts.contains(sort.name())
    }

    fn function_to_functype(&self, func: &FunctionDecl) -> Result<FuncType, TypeError> {
        let input = func
            .schema
            .input
            .iter()
            .map(|name| {
                if let Some(sort) = self.sorts.get(name) {
                    Ok(sort.clone())
                } else {
                    Err(TypeError::UndefinedSort(name.clone(), func.span.clone()))
                }
            })
            .collect::<Result<Vec<_>, _>>()?;
        let output = if let Some(sort) = self.sorts.get(&func.schema.output) {
            Ok(sort.clone())
        } else {
            Err(TypeError::UndefinedSort(
                func.schema.output.clone(),
                func.span.clone(),
            ))
        }?;

        Ok(FuncType {
            name: func.name.clone(),
            subtype: func.subtype,
            input,
            output: output.clone(),
        })
    }

    fn typecheck_function(
        &mut self,
        symbol_gen: &mut SymbolGen,
        fdecl: &FunctionDecl,
    ) -> Result<ResolvedFunctionDecl, TypeError> {
        if self.sorts.contains_key(&fdecl.name) {
            return Err(TypeError::SortAlreadyBound(
                fdecl.name.clone(),
                fdecl.span.clone(),
            ));
        }
        if self.is_primitive(&fdecl.name) {
            return Err(TypeError::PrimitiveAlreadyBound(
                fdecl.name.clone(),
                fdecl.span.clone(),
            ));
        }
        // View tables (with term_constructor) must have at least one input (the e-class)
        if fdecl.term_constructor.is_some() && fdecl.schema.input.is_empty() {
            return Err(TypeError::TermConstructorNoInputs(
                fdecl.name.clone(),
                fdecl.span.clone(),
            ));
        }
        let ftype = self.function_to_functype(fdecl)?;
        if self
            .func_types
            .insert(fdecl.name.clone(), Arc::new(ftype))
            .is_some()
        {
            return Err(TypeError::FunctionAlreadyBound(
                fdecl.name.clone(),
                fdecl.span.clone(),
            ));
        }
        let mut bound_vars = IndexMap::default();
        let output_type = self.sorts.get(&fdecl.schema.output).unwrap();
        if fdecl.subtype == FunctionSubtype::Constructor && !output_type.is_eq_sort() {
            return Err(TypeError::ConstructorOutputNotSort(
                fdecl.name.clone(),
                fdecl.span.clone(),
            ));
        }
        bound_vars.insert("old", (fdecl.span.clone(), output_type.clone()));
        bound_vars.insert("new", (fdecl.span.clone(), output_type.clone()));

        Ok(ResolvedFunctionDecl {
            name: fdecl.name.clone(),
            subtype: fdecl.subtype,
            schema: fdecl.schema.clone(),
            merge: match &fdecl.merge {
                // Merge expressions run as part of action-side table updates:
                // writes are allowed, but live DB reads would be untracked by
                // seminaive rule execution.
                Some(merge) => Some(self.typecheck_standalone_expr(
                    symbol_gen,
                    merge,
                    &bound_vars,
                    Context::Write,
                )?),
                None => None,
            },
            cost: fdecl.cost,
            unextractable: fdecl.unextractable,
            internal_hidden: fdecl.internal_hidden,
            internal_let: fdecl.internal_let,
            span: fdecl.span.clone(),
            term_constructor: fdecl.term_constructor.clone(),
        })
    }

    fn typecheck_schedule(
        &self,
        symbol_gen: &mut SymbolGen,
        schedule: &Schedule,
    ) -> Result<ResolvedSchedule, TypeError> {
        let schedule = match schedule {
            Schedule::Repeat(span, times, schedule) => ResolvedSchedule::Repeat(
                span.clone(),
                *times,
                Box::new(self.typecheck_schedule(symbol_gen, schedule)?),
            ),
            Schedule::Sequence(span, schedules) => {
                let schedules = schedules
                    .iter()
                    .map(|schedule| self.typecheck_schedule(symbol_gen, schedule))
                    .collect::<Result<Vec<_>, _>>()?;
                ResolvedSchedule::Sequence(span.clone(), schedules)
            }
            Schedule::Saturate(span, schedule) => ResolvedSchedule::Saturate(
                span.clone(),
                Box::new(self.typecheck_schedule(symbol_gen, schedule)?),
            ),
            Schedule::Run(span, RunConfig { ruleset, until }) => {
                let until = until
                    .as_ref()
                    .map(|facts| self.typecheck_facts(symbol_gen, facts))
                    .transpose()?;
                ResolvedSchedule::Run(
                    span.clone(),
                    ResolvedRunConfig {
                        ruleset: ruleset.clone(),
                        until,
                    },
                )
            }
        };

        Result::Ok(schedule)
    }

    pub fn typecheck_rule(
        &self,
        symbol_gen: &mut SymbolGen,
        rule: &Rule,
    ) -> Result<ResolvedRule, TypeError> {
        let Rule {
            span,
            head,
            body,
            name,
            ruleset,
            eval_mode,
            no_decomp,
            include_subsumed,
        } = rule;
        // Compile with the permissive Read/Full primitive contexts (so the RHS
        // can read the database) when the whole EGraph is non-seminaive, or the
        // rule's own mode requires it (`:naive` / `:unsafe-seminaive`).
        let (query_ctx, action_ctx) = self.rule_contexts(*eval_mode);
        let read_contexts = action_ctx == Context::Full;

        let (query, mapped_query) = Facts(body.clone()).to_query(self, symbol_gen);
        let mut problem = Problem::default();
        problem.add_query(&query, self, query_ctx)?;

        let mut binding = query.get_vars();
        // We lower to core actions with `union_to_set_optimization`
        // later in the pipeline. For typechecking we do not need it.
        let mut ctx = CoreActionContext::new(self, &mut binding, symbol_gen, false);
        let (actions, mapped_action) = head.to_core_actions(&mut ctx)?;
        problem.add_actions(&actions, self, symbol_gen, action_ctx)?;

        let assignment = problem
            .solve(|sort: &ArcSort| sort.name())
            .map_err(|e| e.to_type_error())?;

        let body: Vec<ResolvedFact> = assignment.annotate_facts(&mapped_query, self, query_ctx)?;
        let actions: ResolvedActions =
            assignment.annotate_actions(&mapped_action, self, action_ctx)?;

        // Function lookups in actions need the `Full` action context; the
        // `Write` context (`!read_contexts`) can't express them.
        if !read_contexts {
            self.check_no_function_lookups_in_actions(&actions)?;
        }

        Ok(ResolvedRule {
            span: span.clone(),
            body,
            head: actions,
            name: name.clone(),
            ruleset: ruleset.clone(),
            eval_mode: *eval_mode,
            no_decomp: *no_decomp,
            include_subsumed: *include_subsumed,
        })
    }

    fn check_lookup_expr(&self, expr: &ResolvedExpr) -> Result<(), TypeError> {
        if let Some(span) = self.expr_has_function_lookup(expr) {
            return Err(TypeError::LookupInRuleDisallowed(
                "function".to_string(),
                span,
            ));
        }
        Ok(())
    }

    pub(crate) fn check_no_function_lookups_in_actions(
        &self,
        actions: &ResolvedActions,
    ) -> Result<(), TypeError> {
        for action in actions.iter() {
            match action {
                GenericAction::Let(_, _, rhs) => self.check_lookup_expr(rhs)?,
                GenericAction::Set(_, _, args, rhs) => {
                    for arg in args.iter() {
                        self.check_lookup_expr(arg)?;
                    }
                    self.check_lookup_expr(rhs)?;
                }
                GenericAction::Union(_, lhs, rhs) => {
                    self.check_lookup_expr(lhs)?;
                    self.check_lookup_expr(rhs)?;
                }
                GenericAction::Change(_, _, _, args) => {
                    for arg in args.iter() {
                        self.check_lookup_expr(arg)?;
                    }
                }
                GenericAction::Panic(..) => {}
                GenericAction::Expr(_, expr) => self.check_lookup_expr(expr)?,
            }
        }
        Ok(())
    }

    pub fn typecheck_facts(
        &self,
        symbol_gen: &mut SymbolGen,
        facts: &[Fact],
    ) -> Result<Vec<ResolvedFact>, TypeError> {
        let (query, mapped_facts) = Facts(facts.to_vec()).to_query(self, symbol_gen);
        let mut problem = Problem::default();
        // Top-level query-shaped commands (e.g. `check`) are read-only:
        // primitives may inspect the database but not write to it.
        problem.add_query(&query, self, Context::Read)?;
        let assignment = problem
            .solve(|sort: &ArcSort| sort.name())
            .map_err(|e| e.to_type_error())?;
        let annotated_facts = assignment.annotate_facts(&mapped_facts, self, Context::Read)?;
        Ok(annotated_facts)
    }

    // Standalone expressions/actions use action lowering. Top-level commands
    // pass `Full`; function `:merge` reuses this path with `Write` because
    // merge expressions run during table updates.
    pub(crate) fn typecheck_standalone_actions(
        &self,
        symbol_gen: &mut SymbolGen,
        actions: &Actions,
        binding: &IndexMap<&str, (Span, ArcSort)>,
        context: Context,
    ) -> Result<ResolvedActions, TypeError> {
        let mut binding_set: IndexSet<String> =
            binding.keys().copied().map(str::to_string).collect();
        // We lower to core actions with `union_to_set_optimization`
        // later in the pipeline. For typechecking we do not need it.
        let mut ctx = CoreActionContext::new(self, &mut binding_set, symbol_gen, false);
        let (actions, mapped_action) = actions.to_core_actions(&mut ctx)?;
        let mut problem = Problem::default();

        problem.add_actions(&actions, self, symbol_gen, context)?;

        // add bindings from the context
        for (var, (span, sort)) in binding {
            problem.assign_local_var_type(var, span.clone(), sort.clone())?;
        }

        let assignment = problem
            .solve(|sort: &ArcSort| sort.name())
            .map_err(|e| e.to_type_error())?;

        let annotated_actions = assignment.annotate_actions(&mapped_action, self, context)?;
        Ok(annotated_actions)
    }

    pub fn typecheck_standalone_expr(
        &self,
        symbol_gen: &mut SymbolGen,
        expr: &Expr,
        binding: &IndexMap<&str, (Span, ArcSort)>,
        context: Context,
    ) -> Result<ResolvedExpr, TypeError> {
        let action = Action::Expr(expr.span(), expr.clone());
        let typechecked_action =
            self.typecheck_standalone_action(symbol_gen, &action, binding, context)?;
        match typechecked_action {
            ResolvedAction::Expr(_, expr) => Ok(expr),
            _ => unreachable!(),
        }
    }

    pub fn typecheck_expr_with_output(
        &self,
        symbol_gen: &mut SymbolGen,
        expr: &Expr,
        binding: &IndexMap<&str, (Span, ArcSort)>,
        output_sort: ArcSort,
        context: Context,
    ) -> Result<ResolvedExpr, TypeError> {
        let action = Action::Expr(expr.span(), expr.clone());
        let mut binding_set: IndexSet<String> =
            binding.keys().copied().map(str::to_string).collect();
        let mut ctx = CoreActionContext::new(self, &mut binding_set, symbol_gen, false);
        let (actions, mapped_action) = Actions::singleton(action).to_core_actions(&mut ctx)?;
        let mut problem = Problem::default();

        problem.add_actions(&actions, self, symbol_gen, context)?;

        for (var, (span, sort)) in binding {
            problem.assign_local_var_type(var, span.clone(), sort.clone())?;
        }

        let [GenericAction::Expr(_, mapped_expr)] = mapped_action.0.as_slice() else {
            unreachable!("typechecking an expression should produce one expression action")
        };
        let output_atom = mapped_expr.get_corresponding_var_or_lit(self);
        problem.add_binding(output_atom, output_sort.clone());

        let assignment = problem
            .solve(|sort: &ArcSort| sort.name())
            .map_err(|e| e.to_type_error())?;

        let annotated_actions = assignment.annotate_actions(&mapped_action, self, context)?;
        match annotated_actions.0.into_iter().next().unwrap() {
            ResolvedAction::Expr(_, resolved_expr) => {
                let actual = resolved_expr.output_type();
                if actual.name() != output_sort.name() {
                    return Err(TypeError::Mismatch {
                        expr: expr.clone(),
                        expected: output_sort,
                        actual,
                    });
                }
                Ok(resolved_expr)
            }
            _ => unreachable!(),
        }
    }

    pub fn typecheck_standalone_action(
        &self,
        symbol_gen: &mut SymbolGen,
        action: &Action,
        binding: &IndexMap<&str, (Span, ArcSort)>,
        context: Context,
    ) -> Result<ResolvedAction, TypeError> {
        self.typecheck_standalone_actions(
            symbol_gen,
            &Actions::singleton(action.clone()),
            binding,
            context,
        )
        .map(|v| {
            assert_eq!(v.len(), 1);
            v.0.into_iter().next().unwrap()
        })
    }

    pub fn get_sort_by_name(&self, sym: &str) -> Option<&ArcSort> {
        self.sorts.get(sym)
    }

    pub fn get_prims(&self, sym: &str) -> Option<&[PrimitiveDefinition]> {
        self.primitives.get(sym).map(Vec::as_slice)
    }

    pub fn is_primitive(&self, sym: &str) -> bool {
        self.primitives.contains_key(sym) || self.reserved_primitives.contains(sym)
    }

    /// Function and constructor signatures in stable name order. This exposes
    /// declaration metadata to macros without consulting runtime tables.
    pub fn get_func_types(&self) -> Vec<Arc<FuncType>> {
        let mut functions: Vec<_> = self.func_types.values().cloned().collect();
        functions.sort_by(|a, b| a.name.cmp(&b.name));
        functions
    }

    /// The shared signature declared for `sym`, or `None` if no function with
    /// that name is declared. Clone it to keep it past the borrow.
    pub fn get_func_type(&self, sym: &str) -> Option<&Arc<FuncType>> {
        self.func_types.get(sym)
    }

    /// Record a signature for a function that did not come through
    /// typechecking — desugaring generates some (global bindings, proof
    /// tables) directly.
    pub(crate) fn declare_func_type(&mut self, func_type: Arc<FuncType>) {
        self.func_types.insert(func_type.name.clone(), func_type);
    }

    pub fn is_constructor(&self, sym: &str) -> bool {
        self.get_func_type(sym)
            .is_some_and(|f| f.subtype == FunctionSubtype::Constructor)
    }

    pub fn get_global_sort(&self, sym: &str) -> Option<&ArcSort> {
        self.global_sorts.get(sym)
    }

    pub fn is_global(&self, sym: &str) -> bool {
        self.global_sorts.contains_key(sym)
    }

    /// Check if an expression contains non-global function lookups (FunctionSubtype::Custom calls).
    /// Global function calls are allowed since they get desugared to constructors.
    /// Returns Some(span) if a lookup is found, None otherwise.
    pub fn expr_has_function_lookup(&self, expr: &ResolvedExpr) -> Option<Span> {
        use ast::GenericExpr;

        expr.find(&mut |e| {
            if let GenericExpr::Call(span, ResolvedCall::Func(func_type), _) = e
                && func_type.subtype == FunctionSubtype::Custom
                && !self.is_global(&func_type.name)
            {
                return Some(span.clone());
            }
            None
        })
    }
}

#[derive(Debug, Clone, Error)]
pub enum TypeError {
    #[error("{0}")]
    MacroExpansion(String),
    #[error("{expr}: expected {description}, got {}", .actual.name())]
    SortPredicate {
        expr: Expr,
        description: String,
        actual: ArcSort,
    },
    #[error("{}\nArity mismatch, expected {expected} args: {expr}", .expr.span())]
    Arity { expr: Expr, expected: usize },
    #[error(
        "{}\n Expect expression {expr} to have type {}, but get type {}",
        .expr.span(), .expected.name(), .actual.name(),
    )]
    Mismatch {
        expr: Expr,
        expected: ArcSort,
        actual: ArcSort,
    },
    #[error("{1}\nUnbound symbol {0}")]
    Unbound(String, Span),
    #[error(
        "{1}\nVariable {0} is ungrounded. A variable is grounded when it appears as an argument to a constructor or function in the query, not just under primitives or equalities."
    )]
    Ungrounded(String, Span),
    #[error("{1}\nUndefined sort {0}")]
    UndefinedSort(String, Span),
    #[error("{1}\nUnbound function {0}")]
    UnboundFunction(String, Span),
    #[error("{1}\nprove-exists requires constructor function, but {0} is not a constructor")]
    ProveExistsRequiresConstructor(String, Span),
    #[error("{1}\nFunction already bound {0}")]
    FunctionAlreadyBound(String, Span),
    #[error("{1}\nSort {0} already declared.")]
    SortAlreadyBound(String, Span),
    #[error("{1}\nPrimitive {0} already declared.")]
    PrimitiveAlreadyBound(String, Span),
    #[error("Function type mismatch: expected {} => {}, actual {} => {}", .1.iter().map(|s| s.name().to_string()).collect::<Vec<_>>().join(", "), .0.name(), .3.iter().map(|s| s.name().to_string()).collect::<Vec<_>>().join(", "), .2.name())]
    FunctionTypeMismatch(ArcSort, Vec<ArcSort>, ArcSort, Vec<ArcSort>),
    #[error("{1}\nPresort {0} not found.")]
    PresortNotFound(String, Span),
    #[error("{1}\nInvalid arguments to sort constructor `{0}`")]
    BadPresortArguments(String, Span),
    #[error("{}\nFailed to infer a type for: {}", .0.span(), .0)]
    InferenceFailure(Expr),
    #[error("{1}\nVariable {0} was already defined")]
    AlreadyDefined(String, Span),
    #[error("{1}\nThe output type of constructor function {0} must be sort")]
    ConstructorOutputNotSort(String, Span),
    #[error("{1}\nValue lookup of non-constructor function {0} in rule is disallowed.")]
    LookupInRuleDisallowed(String, Span),
    #[error("{1}\nCannot set constructor {0}. Use `union` instead or declare {0} as a function.")]
    SetConstructorDisallowed(String, Span),
    #[error("All alternative definitions considered failed\n{}", .0.iter().map(|e| format!("  {e}\n")).collect::<Vec<_>>().join(""))]
    AllAlternativeFailed(Vec<TypeError>),
    #[error("{}\nCannot union values of sort {}", .1, .0.name())]
    NonEqsortUnion(ArcSort, Span),
    #[error("{}\nCannot union values of sort {} because it is marked as non-unionable (e.g. from a relation)", .1, .0.name())]
    NonUnionableSort(ArcSort, Span),
    #[error(
        "{1}\nView table {0} with :internal-term-constructor must have at least one input (the e-class)."
    )]
    TermConstructorNoInputs(String, Span),
    #[error(
        "{span}\nNon-global variable `{name}` must not start with `{}`.",
        crate::GLOBAL_NAME_PREFIX
    )]
    NonGlobalPrefixed { name: String, span: Span },
    #[error(
        "{span}\nGlobal `{name}` must start with `{}`.",
        crate::GLOBAL_NAME_PREFIX
    )]
    GlobalMissingPrefix { name: String, span: Span },
    #[error(
        "{span}\nAmbiguous primitive resolution for `{name}` in {ctx:?} context: multiple registered primitives match the same signature."
    )]
    AmbiguousPrimitive {
        name: String,
        ctx: crate::Context,
        span: Span,
    },
    #[error("{span}\nNo resolution for `{name}` in {ctx:?} context.")]
    UnresolvedPrimitive {
        name: String,
        ctx: crate::Context,
        span: Span,
    },
}

impl Default for TypeInfo {
    fn default() -> Self {
        let mut eg = Self {
            seminaive: true,
            mksorts: Default::default(),
            reserved_primitives: Default::default(),
            sorts: Default::default(),
            primitives: Default::default(),
            func_types: Default::default(),
            global_sorts: Default::default(),
            non_unionable_sorts: Default::default(),
            hidden_functions: Default::default(),
        };
        eg.add_base_sort(UnitSort, span!()).unwrap();
        eg.add_base_sort(StringSort, span!()).unwrap();
        eg.add_base_sort(BoolSort, span!()).unwrap();
        eg.add_base_sort(I64Sort, span!()).unwrap();
        eg.add_base_sort(F64Sort, span!()).unwrap();
        eg.add_base_sort(BigIntSort, span!()).unwrap();
        eg.add_base_sort(BigRatSort, span!()).unwrap();
        eg.add_presort::<MapSort>(span!()).unwrap();
        eg.add_presort::<SetSort>(span!()).unwrap();
        eg.add_presort::<VecSort>(span!()).unwrap();
        eg.add_presort::<FunctionSort>(span!()).unwrap();
        eg.add_presort::<MultiSetSort>(span!()).unwrap();
        eg.add_presort::<PairSort>(span!()).unwrap();

        // Add != with a validator that computes inequality result
        let neq_validator = |termdag: &mut TermDag, args: &[TermId]| -> Option<TermId> {
            if args.len() == 2 && args[0] != args[1] {
                // Return unit literal for successful inequality
                Some(termdag.lit(Literal::Unit))
            } else {
                None
            }
        };
        add_primitive_with_validator!(
            &mut eg,
            "!=" = |a: #, b: #| -?> () {
                (a != b).then_some(())
            },
            neq_validator
        );

        add_primitive_with_validator!(
            &mut eg,
            "bool-!=" = |a: #, b: #| -> bool {
                (a != b)
            },
            |termdag: &mut TermDag, args: &[TermId]| -> Option<TermId> {
                if args.len() == 2 {
                    Some(termdag.lit(Literal::Bool(args[0] != args[1])))
                } else {
                    None
                }
            }
        );

        add_primitive!(&mut eg, "value-eq" = |a: #, b: #| -?> () {
            (a == b).then_some(())
        });
        add_primitive!(&mut eg, "ordering-min" = |a: #, b: #| -> # {
            if a < b { a } else { b }
        });
        add_primitive!(&mut eg, "ordering-max" = |a: #, b: #| -> # {
            if a > b { a } else { b }
        });

        eg
    }
}

impl TypeInfo {
    /// Register a base sort and its primitive signatures without allocating backend state.
    pub fn add_base_sort(
        &mut self,
        sort: impl prelude::BaseSort,
        span: Span,
    ) -> Result<(), TypeError> {
        self.add_arcsort(sort.to_arcsort(), span)
    }

    /// Register a container sort and its primitive signatures.
    pub fn add_container_sort(
        &mut self,
        sort: impl prelude::ContainerSort,
        span: Span,
    ) -> Result<(), TypeError> {
        self.add_arcsort(sort.to_arcsort(), span)
    }

    /// Access the declaration environment when using shared primitive-registration helpers.
    pub fn type_info(&mut self) -> &mut Self {
        self
    }
}

impl EGraph {
    /// Set the rule evaluation and inference policy together.
    pub fn set_seminaive(&mut self, enabled: bool) {
        self.type_info.seminaive = enabled;
        if let Some(source) = &mut self.proof_state.original_typechecking {
            source.seminaive = enabled;
        }
    }

    pub fn with_seminaive(mut self, enabled: bool) -> Self {
        self.set_seminaive(enabled);
        self
    }

    pub fn seminaive(&self) -> bool {
        self.type_info.seminaive
    }

    pub fn add_sort<S: Sort + 'static>(&mut self, sort: S, span: Span) -> Result<(), TypeError> {
        self.add_arcsort(Arc::new(sort), span)
    }

    pub fn add_arcsort(&mut self, sort: ArcSort, span: Span) -> Result<(), TypeError> {
        self.type_info.add_arcsort(sort, span)?;
        self.install_type_info();
        Ok(())
    }

    pub fn declare_sort(
        &mut self,
        name: impl Into<String>,
        presort_and_args: &Option<(String, Vec<Expr>)>,
        span: Span,
    ) -> Result<(), TypeError> {
        self.type_info.declare_sort(name, presort_and_args, span)?;
        self.install_type_info();
        Ok(())
    }

    pub fn add_pure_primitive<T: PurePrim + Clone>(
        &mut self,
        primitive: T,
        validator: Option<PrimitiveValidator>,
    ) {
        self.type_info.add_pure_primitive(primitive, validator);
        self.install_type_info();
    }
    pub fn add_read_primitive<T: ReadPrim + Clone>(
        &mut self,
        primitive: T,
        validator: Option<PrimitiveValidator>,
    ) {
        self.type_info.add_read_primitive(primitive, validator);
        self.install_type_info();
    }
    pub fn add_write_primitive<T: WritePrim + Clone>(
        &mut self,
        primitive: T,
        validator: Option<PrimitiveValidator>,
    ) {
        self.type_info.add_write_primitive(primitive, validator);
        self.install_type_info();
    }
    pub fn add_full_primitive<T: FullPrim + Clone>(
        &mut self,
        primitive: T,
        validator: Option<PrimitiveValidator>,
    ) {
        self.type_info.add_full_primitive(primitive, validator);
        self.install_type_info();
    }

    // Backend identities belong to this EGraph, never to TypeInfo. Cloned source
    // environments can therefore be checked without constructing a database.
    pub(crate) fn install_type_info(&mut self) {
        let mut sorts: Vec<_> = self.type_info.sorts.values().collect();
        sorts.sort_by_key(|sort| sort.name());
        for sort in sorts {
            if self.installed_sorts.insert(sort.name().to_owned()) {
                sort.register_type(&mut self.backend);
            }
        }
        let mut primitives: Vec<_> = self.type_info.primitives.values().flatten().collect();
        primitives.sort_by_key(|primitive| primitive.id);
        for primitive in primitives {
            if let Some(install) = &primitive.install {
                self.primitive_runtimes
                    .entry(primitive.id)
                    .or_insert_with(|| install(&mut self.backend));
            }
        }
    }

    pub(crate) fn bind_expr_primitives(&self, expr: ResolvedExpr) -> ResolvedExpr {
        expr.visit_exprs(&mut |mut expr| {
            if let ResolvedExpr::Call(_, ResolvedCall::Primitive(primitive), _) = &mut expr {
                primitive.bind_runtime(&self.primitive_runtimes);
            }
            expr
        })
    }

    pub(crate) fn bind_command_primitives(&self, command: ResolvedNCommand) -> ResolvedNCommand {
        command.visit_exprs(&mut |mut expr| {
            if let ResolvedExpr::Call(_, ResolvedCall::Primitive(primitive), _) = &mut expr {
                primitive.bind_runtime(&self.primitive_runtimes);
            }
            expr
        })
    }
}

impl TypeInfo {
    pub(crate) fn add_deferred(&mut self, call: impl Primitive) {
        let name = call.name().to_owned();
        self.primitives.insert(
            name,
            vec![PrimitiveDefinition {
                primitive: Arc::new(call),
                validator: None,
                id: next_primitive_id(),
                valid_contexts: vec![Context::Write, Context::Full],
                install: None,
            }],
        );
    }
    pub(crate) fn remove_deferred(&mut self, name: &str) {
        self.primitives.remove(name);
    }
}

fn next_primitive_id() -> usize {
    static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
}

impl TypeInfo {
    /// Declare a primitive's constraints before its runtime implementation is
    /// installed. Registering that implementation completes this declaration.
    pub fn declare_primitive(&mut self, primitive: impl Primitive, contexts: &[Context]) {
        self.primitives
            .entry(primitive.name().to_owned())
            .or_default()
            .push(PrimitiveDefinition {
                primitive: Arc::new(primitive),
                validator: None,
                id: next_primitive_id(),
                valid_contexts: contexts.to_vec(),
                install: None,
            });
    }

    /// Check an expression in a standalone environment, retaining the exact
    /// overload choices and rewriting globals for subsequent evaluation.
    pub fn typecheck_expr_with_bindings_and_output(
        &self,
        symbols: &mut SymbolGen,
        expr: &Expr,
        bindings: &[(String, Span, ArcSort)],
        output: ArcSort,
        context: Context,
    ) -> Result<ResolvedExpr, TypeError> {
        let mut scope = IndexMap::default();
        for (name, span, sort) in bindings {
            if scope
                .insert(name.as_str(), (span.clone(), sort.clone()))
                .is_some()
            {
                return Err(TypeError::AlreadyDefined(name.clone(), span.clone()));
            }
        }
        Ok(remove_globals::remove_globals_expr(
            self.typecheck_expr_with_output(symbols, expr, &scope, output, context)?,
        ))
    }
}

impl TypeInfo {
    /// Shared inference and runtime capability policy for a rule.
    pub fn rule_contexts(&self, mode: RuleEvalMode) -> (Context, Context) {
        if !self.seminaive || matches!(mode, RuleEvalMode::Naive | RuleEvalMode::UnsafeSeminaive) {
            (Context::Read, Context::Full)
        } else {
            (Context::Pure, Context::Write)
        }
    }
}

#[cfg(test)]
mod test {
    use crate::{EGraph, Error, typechecking::TypeError};

    #[test]
    fn test_arity_mismatch() {
        let mut egraph = EGraph::default();

        let prog = "
            (relation f (i64 i64))
            (rule ((f a b c)) ())
       ";
        let res = egraph.parse_and_run_program(None, prog);
        match res {
            Err(Error::TypeError(TypeError::Arity {
                expected: 2,
                expr: e,
            })) => {
                assert_eq!(e.span().string(), "(f a b c)");
            }
            _ => panic!("Expected arity mismatch, got: {res:?}"),
        }
    }
}
