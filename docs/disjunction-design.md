# Disjunction (`or`) in rule bodies

## Surface syntax

A rule body may contain a disjunction fact:

```
(rule (C
       (or (branch-1-fact ...)
           (branch-2-fact ...)
           ...))
      (action ...))
```

Each branch is either a parenthesized *list of facts* (a conjunction,
`((A x) (B x))`) or a single bare fact (`(= a d)`, `(A x)`). Both the lowercase
`or` and uppercase `OR` spellings are accepted. The body `C ∧ (D₁ ∨ … ∨ Dₙ)`
matches when the surrounding conjunction `C` holds and at least one branch `Dᵢ`
holds.

## Semantics

- **Common variables.** `V = ⋂ᵢ vars(Dᵢ)` — the variables that appear in every
  branch. Only `V`, together with the variables bound by the surrounding
  conjunction `C`, are visible in the action and elsewhere outside the `or`.
- **Correlated branches.** A branch may reference a variable bound by the
  surrounding conjunction `C` (even one not common to every branch), e.g.
  `(= col d)` where `col` and `d` come from `C`. Such a reference is left
  untouched during typechecking; it is *not* treated as branch-local.
- **Branch-local variables.** A variable that appears in some branch but is
  neither in `V` nor bound by `C` is *branch-local*. Branch-locals in different
  branches are independent: during typechecking they are renamed to fresh names
  so their sorts are not conflated. A branch-local variable that is used outside
  its `or` is a type error (`TypeError::OrBranchLocalEscapes`).
- **Empty branch.** A branch with no facts is a type error
  (`TypeError::EmptyOrBranch`).
- **Scope.** `or` is only supported inside rule bodies (including the `:when`
  conditions of a `rewrite`, which desugar to rules). It is rejected in
  query-shaped commands like `check` and `query`
  (`TypeError::OrOutsideRule`). It is allowed under the term encoding without
  proofs; with proofs it is unsupported.

## Frontend pipeline

1. **AST** — `egglog-ast/src/generic_ast.rs`: `GenericFact::Or(Span,
   Vec<Vec<GenericFact<Head, Leaf>>>)`. `Display`, `visit_exprs`, `map_exprs`,
   and `map_symbols` recurse into the branches
   (`egglog-ast/src/generic_ast_helpers.rs`).
2. **Parsing** — `src/ast/parse.rs`: `parse_fact` recognises the `OR_HEAD`
   (`"or"`) / `OR_HEAD_UPPER` (`"OR"`) head. Each argument is parsed as a list
   of facts if it is an empty list or its first element is itself a list;
   otherwise it is a single bare fact.
3. **Typechecking** — `src/typechecking.rs` `typecheck_rule`:
   - `rename_or_locals` renames each branch's branch-local variables to fresh
     names (independently per branch) and enforces the interface rule
     (branch-locals may not escape their `or`). It takes both `outside_vars`
     (all variables visible outside every `or`: conjunctive-fact variables,
     action variables, and each `or`'s common variables) and `conj_vars` (the
     subset bound by the surrounding conjunction); a branch reference to a
     `conj_var` is a correlation and is left as-is rather than renamed.
   - `Facts::to_query` (`src/ast/mod.rs`) flattens every branch's atoms into one
     shared constraint `Query` so the constraint solver assigns a sort to every
     variable — common variables (whose sort is thereby unified across branches
     and with `C`) and the already-renamed branch-locals.
   - `Assignment::annotate_fact` (`src/constraint.rs`) reconstructs a
     `ResolvedFact::Or` with the resolved branches.
   - `src/ast/check_shadowing.rs` recurses into `or` branches when collecting
     pattern variable names.

## Backend compilation

`add_rule` dispatches `or`-containing rules to `add_or_rule`, which picks one of
two strategies (returning one `(name, core rule, backend rule id)` per compiled
backend rule):

- **Strategy C — fused union node.** Used when the rule is naive *and* every
  disjunct is *self-groundable* (`branch_self_groundable`: every non-global
  variable the disjunct references is bound by one of its own table atoms). One
  backend rule with a fused union node; `C` is scanned once.
- **Strategy D — splitting.** Used otherwise — a *correlated* disjunct (which
  references a `C`-bound variable it does not bind itself) or a seminaive rule.
  See "Strategy D" below.

## Strategy C — a fused union node in the free-join engine

The `or`-containing rule compiles to **one** backend rule with a fused union
node in the free-join engine. The surrounding conjunction `C` is scanned
**once**; the branches are enumerated additively (never a `∏` of separate
rules). `add_or_rule` (Strategy-C path):

1. Splits the body into the conjunction `C` (non-`or` facts) and the `or`s, and
   forms the union's **branches** as the cartesian product of every `or`'s
   disjuncts (`expand_or_branch` expands nested `or`s the same way). One `or`
   gives one branch per disjunct; multiple/nested `or`s give `∏` *branches* (but
   still one rule, and `C` is still scanned once).
2. Computes the union's **output variables** (`common_branch_vars`): the
   variables common to every branch — exactly the variables an `or` shares
   across its disjuncts, which are the only branch variables visible to `C` and
   the action.
3. Compiles `C`'s query and the rule's actions together
   (`to_canonicalized_core_rule_extra_binding`) so their flattened
   (fresh-`gensym`) variables agree, adding the output variables to the action
   binding (they are bound by the union at runtime, not by `C`'s atoms).
4. Compiles each branch's query on its own
   (`to_canonicalized_core_rule_ungrounded`; the grounded check is skipped since
   a branch variable may be grounded by `C`).
5. Builds one backend rule: adds `C`'s atoms (`BackendRule::query`), then each
   branch's atoms (`query_union_branch`, recording their `AtomId`s), calls
   `set_union_branches`, and adds the actions. The rule is compiled in **naive**
   mode (seminaive delta through a union is unsupported). Branch atoms must be
   table atoms; a primitive inside a branch is rejected.

### Bridge (`egglog-bridge/src/rule.rs`)

`RuleBuilder::set_union_branches(branch_atoms, output_vars)` records the branch
atom groups and output variables on the bridge `Query`. `Query::build_cached_plan`
translates the high-level atom indices / variable ids into the core-relations
`AtomId`s / `Variable`s allocated when the atoms were added, and calls
`QueryBuilder::set_union`.

### core-relations (`query.rs`, `free_join/plan.rs`, `free_join/execute.rs`)

- `Query` gains an optional `union: Option<UnionSpec>` (`branch_atoms`,
  `output_vars`), set by `QueryBuilder::set_union` (which also forces
  single-bag planning).
- `plan.rs` adds `JoinStage::Union { branches: Vec<UnionBranch> }`, where each
  `UnionBranch` is a self-contained sub-plan (its own atoms, header, and
  stages). `plan_union` produces a **`DecomposedPlan`**:
  - **Block 0** is the lone `Union` stage. `plan_union` plans each branch over
    its own atoms (`restrict_context` + `plan_stages`), marking the output
    variables `used_in_rhs` so the branch binds them. The block's `MatSpec`
    keys on the output variables.
  - The **result block** is the continuation: the atoms of `C`, planned with
    `plan_single_bag` treating the output variables as message variables coming
    from block 0. This reuses the tree-decomposition message-passing machinery:
    a `FusedIntersectMat { mode: KeyOnly }` prologue iterates the distinct
    output tuples and probes `C`'s atoms by them via their indexes, then the
    rest of `C` is joined and the action fires.
  - The plan's `atoms` are `C`'s atoms only; each branch carries its own atoms,
    so an empty branch relation cannot abort the whole rule.
- `execute.rs` handles `JoinStage::Union` in `run_plan`: for each branch it
  seeds a fresh `BindingInfo` from the branch's atoms, applies the branch
  header, and runs the branch's stages via `run_join_stages` with the enclosing
  block's `action`/`action_buf`. Because block 0 runs with the block's
  `InPlaceMaterializer`, each branch match is written into one materialization
  keyed on the output variables — **deduplicated on the key**, in memory, with
  no temporary database table. The result block then joins `C` once against
  that materialization.

This shares `C`: it is evaluated a single time in the result block, joined by
index against the deduplicated union of the branch outputs — never re-scanned per
branch and never producing `∏` separate rules.

### Strategy-C tradeoffs / restrictions

- **Naive only.** Strategy C runs in naive mode; a seminaive rule uses Strategy
  D instead.
- **Primitives in branches** are rejected (a branch must be a conjunction of
  table atoms). Primitives in the surrounding conjunction `C` are fine.
- **`∏` branches for multiple/nested `or`s.** `k` disjunctions produce `∏`
  union *branches* (enumerated additively into one materialization), but still a
  single rule with `C` scanned once. A single `or` (the common case) is linear.
- **No cross-branch dedup of firings beyond the output key.** The union
  deduplicates output tuples; like every egglog rule, the action still fires per
  full match otherwise. This matches egglog's normal non-dedup semantics and is
  invisible for idempotent actions.

## Strategy D — splitting (correlated / seminaive `or`s)

Strategy C's fused union requires each branch to bind the union's output
variables *itself* (its branches run first, materializing those variables), and
it forces naive mode. Neither holds for a **correlated** `or` such as the
e-graph rebuild pattern

```
(rule ((MulView c0 c1 c2) (UF_Math d e) (!= d e)
       (OR (= c0 d) (= c1 d) (= c2 d)))
      (...)
      :ruleset rebuilding :unsafe-seminaive)
```

where each disjunct only *constrains* variables (`c0`/`d`) bound by the
surrounding conjunction, and where per-disjunct variable merging (`c0 = d` in
one branch, `c1 = d` in another) must propagate into the shared action.

`add_or_rule` (via `add_or_rule_split` in `src/lib.rs`) therefore compiles a
correlated or seminaive `or` by **splitting**: the disjuncts are expanded into
the cartesian product of the `or`s (`expand_or_branch`), and for each combined
disjunct one ordinary backend rule is emitted, with body `C ∧ disjunct` and the
rule's shared action. Extra split rules get synthetic names `{name}__or{i}` so
they coexist in the ruleset (`add_rule` inserts one ruleset entry per split).

Each split rule is a plain conjunctive rule, so the existing machinery does the
right thing with no changes to the free-join engine or seminaive evaluation:

- **Per-disjunct canonicalization** merges each disjunct's equalities
  independently. `(= c0 d)` substitutes `c0 → d`, so `MulView(c0,c1,c2)` becomes
  `MulView(d,c1,c2)` sharing variable `d` with `UF_Math(d,e)`. A join on a
  shared variable is an **index probe**, never a cartesian product — even in
  naive mode. The merge propagates into the action, so a correlated variable
  resolves correctly there too.
- **Seminaive** (`:unsafe-seminaive`) runs normally per split rule. A delta on
  the outer atom (`UF_Math`) drives an index probe of the correlated atom
  (`MulView`) by the new key; a delta on `MulView` probes `UF_Math`. The
  `Read`/`Full` RHS contexts of `:unsafe-seminaive` let the action perform
  lookups (e.g. `(UF_Mathf c0)`).
- **Primitives** in the surrounding conjunction (e.g. `(!= d e)`) are ordinary
  RHS-context checks in each split rule.

### Strategy-D tradeoffs / restrictions

- **`k` backend rules per `or`.** A `k`-way `or` (or `∏` over several `or`s)
  becomes `k` (or `∏`) backend rules. In seminaive mode this is cheap — each
  processes only the delta and probes by index — so the cartesian-product
  blow-up the fused union avoids does not reappear.
- **Split rule names.** Extra disjuncts occupy synthetic `{name}__or{i}`
  ruleset entries, which show up separately in run reports.

## Proofs and the term encoding

`or` is allowed under the term encoding **without** proofs: `proof_form`
normalizes each branch independently, and `instrument_fact` rewrites each
branch's atoms to view-table lookups and re-emits an `(or (branch...) ...)`
fact, which is then compiled by the strategies above. With proofs enabled the
instrumentation panics (`or` is unsupported with proofs). `:unsafe-seminaive`
remains unsupported under the term encoding regardless (a pre-existing
limitation, since it performs arbitrary live-database reads).
