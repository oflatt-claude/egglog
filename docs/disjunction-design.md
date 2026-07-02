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

Each branch is a parenthesized *list of facts* (a conjunction). The body
`C ∧ (D₁ ∨ … ∨ Dₙ)` matches when the surrounding conjunction `C` holds and at
least one branch `Dᵢ` holds.

## Semantics

- **Common variables.** `V = ⋂ᵢ vars(Dᵢ)` — the variables that appear in every
  branch. Only `V`, together with the variables bound by the surrounding
  conjunction `C`, are visible in the action and elsewhere outside the `or`.
- **Branch-local variables.** A variable that appears in some branch but is not
  in `V` is *branch-local*. Branch-locals in different branches are independent:
  during typechecking they are renamed to fresh names so their sorts are not
  conflated. A branch-local variable that is used outside its `or` is a type
  error (`TypeError::OrBranchLocalEscapes`).
- **Empty branch.** A branch with no facts is a type error
  (`TypeError::EmptyOrBranch`).
- **Scope.** `or` is only supported inside rule bodies (including the `:when`
  conditions of a `rewrite`, which desugar to rules). It is rejected in
  query-shaped commands like `check` and `query`
  (`TypeError::OrOutsideRule`).

## Frontend pipeline

1. **AST** — `egglog-ast/src/generic_ast.rs`: `GenericFact::Or(Span,
   Vec<Vec<GenericFact<Head, Leaf>>>)`. `Display`, `visit_exprs`, `map_exprs`,
   and `map_symbols` recurse into the branches
   (`egglog-ast/src/generic_ast_helpers.rs`).
2. **Parsing** — `src/ast/parse.rs`: `parse_fact` recognises the `OR_HEAD`
   (`"or"`) head and parses each argument as a list of facts.
3. **Typechecking** — `src/typechecking.rs` `typecheck_rule`:
   - `rename_or_locals` renames each branch's branch-local variables to fresh
     names (independently per branch) and enforces the interface rule
     (branch-locals may not escape their `or`). `outside_vars` is the set of
     variables visible outside every `or`: conjunctive-fact variables, action
     variables, and each `or`'s common variables.
   - `Facts::to_query` (`src/ast/mod.rs`) flattens every branch's atoms into one
     shared constraint `Query` so the constraint solver assigns a sort to every
     variable — common variables (whose sort is thereby unified across branches
     and with `C`) and the already-renamed branch-locals.
   - `Assignment::annotate_fact` (`src/constraint.rs`) reconstructs a
     `ResolvedFact::Or` with the resolved branches.
   - `src/ast/check_shadowing.rs` recurses into `or` branches when collecting
     pattern variable names.

## Backend compilation: Strategy C — a fused union node in the free-join engine

An `or`-containing rule compiles to **one** backend rule with a fused union node
in the free-join engine. The surrounding conjunction `C` is scanned **once**;
the branches are enumerated additively (never a `∏` of separate rules).

### egglog crate (`src/lib.rs`, `add_or_rule`)

`add_rule` dispatches `or`-containing rules to `add_or_rule`, which:

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

### Tradeoffs / restrictions

- **Naive evaluation.** `or` rules match the whole database each iteration
  (seminaive delta through a union is not supported).
- **Primitives in branches** are rejected (a branch must be a conjunction of
  table atoms). Primitives in the surrounding conjunction `C` are fine.
- **`∏` branches for multiple/nested `or`s.** `k` disjunctions produce `∏`
  union *branches* (enumerated additively into one materialization), but still a
  single rule with `C` scanned once — unlike rule-splitting, which would create
  `∏` rules each re-scanning `C`. A single `or` (the common case) is linear.
- **No cross-branch dedup of firings beyond the output key.** The union
  deduplicates output tuples; like every egglog rule, the action still fires per
  full match otherwise. This matches egglog's normal non-dedup semantics and is
  invisible for idempotent actions.
- **Proofs.** `or` is not supported with the proof / term encoding; the proof
  passes panic if they ever see an `or` fact (they never do, because proof mode
  compiles only proof-instrumented rules).
