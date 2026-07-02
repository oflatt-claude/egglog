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

## Backend compilation: a fused, deduplicating union node

An `or`-containing rule compiles to **one** backend rule with a fused union node
in the free-join engine (`src/lib.rs` `add_or_rule`). Every branch is enumerated
additively; its output tuple is materialized and **deduplicated on the union's
output variables**, and the shared action fires exactly once per distinct output
tuple. Because branch-local variables are *not* output variables, a row matched
via several branches (which differ only in branch-locals) is processed **once** —
disjunctive-semijoin single-rebuild semantics.

`add_or_rule`:

1. Splits the body into the conjunction `C` (non-`or` facts) and the `or`s, and
   forms the **disjuncts** as the cartesian product of every `or`'s branches
   (`expand_or_branch` expands nested `or`s the same way).
2. Chooses a branch layout by whether any disjunct is *correlated* — references a
   `C`-bound variable that is not common to every disjunct (e.g. `(v a b c)`
   outside, `(stale a al)` inside a branch, where `a` comes from `v`):
   - **Independent** (no correlation): `C` is a **continuation** — scanned once
     and joined against the deduplicated branch outputs. Branches are the
     disjuncts; output variables are the variables common to every disjunct.
   - **Correlated**: `C` is **prepended into every branch**, so each branch binds
     the shared output tuple itself (typically the surrounding row) and probes
     the disjunct's own atoms by the correlated columns. The continuation is
     empty; output variables are the variables common to every prepended branch —
     the surrounding row.
3. Computes the union's **output variables** (`common_branch_vars`), excluding
   `Unit`-sorted variables (they carry no dedup information and may be unbound at
   runtime, e.g. the unit result of a term-encoding view lookup).
4. Compiles the continuation's query and the rule's actions together
   (`to_canonicalized_core_rule_extra_binding`) so their flattened
   (fresh-`gensym`) variables agree, adding the output variables to the action
   binding (they are bound by the union at runtime).
5. Compiles each branch's query on its own
   (`to_canonicalized_core_rule_ungrounded`; the grounded check is skipped since
   a correlated branch variable is grounded by the prepended `C`).
6. Builds one backend rule: adds the continuation's atoms (`BackendRule::query`),
   then each branch's atoms (`query_union_branch`, recording their `AtomId`s),
   calls `set_union_branches`, and adds the actions. A correlated rule runs
   **seminaive / delta-driven** (see "Seminaive execution"); an independent one
   runs naive. Branch atoms must be table atoms; a primitive inside a branch is
   rejected — a `!=` staleness filter is encoded as a relation (e.g.
   `(stale term leader)` holding only non-canonical terms).

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
  no temporary database table. The result block then iterates the distinct
  output tuples (`FusedIntersectMat { mode: KeyOnly }`, joining the continuation
  atoms if any) and fires the action **once per key**.

For an independent `or`, the continuation `C` is evaluated a single time in the
result block, joined by index against the deduplicated union of the branch
outputs. For a correlated `or`, the continuation is empty (it was prepended into
every branch), so the result block simply enumerates the deduplicated output
tuples and fires the action once each.

### The correlated rebuild pattern

This is what the term encoding emits as the per-constructor rebuild rule (see
[Proofs and the term encoding](#proofs-and-the-term-encoding)). With a view
`AddView(a,b,c)` and a staleness relation `stale(term, leader)` (holding only
non-canonical terms):

```
(rule ((AddView a b c)
       (OR ((stale a al)) ((stale b bl)) ((stale c cl))))
      ((AddView (leader a) (leader b) (leader c))
       (delete (AddView a b c)))
      :ruleset rebuilding :unsafe-seminaive)
```

Each branch references the outer row `a`/`b`/`c` and probes `stale` on one
column, binding a branch-local leader. `AddView` is prepended into every branch,
so the output/dedup variables are the row `(a b c)`. A row stale in two columns
matches two branches but produces the same `(a b c)` tuple, so the shared action
rebuilds it **exactly once**. `:unsafe-seminaive` supplies the `Read`/`Full` RHS
context the action needs for the `leader` lookups.

### Seminaive (delta-driven) execution

A correlated union runs **seminaive**: a new `stale`/`AddView` tuple drives an
index probe of the other branch atom, rather than a per-iteration re-scan.

The semi-naive expansion of a union of conjunctions is the union of the
per-disjunct expansions: `seminaive(⋁ᵢ Bᵢ) = ⋃ᵢ seminaive(Bᵢ)`. Because a
correlated `or` prepends the conjunction into every branch, each branch `Bᵢ`
holds all of `O ∪ (branch i's atoms)`, so its semi-naive expansion is
self-contained (delta constraints never cross branch boundaries — other branches
are alternatives, not conjuncts).

- **`egglog-bridge` `add_rules_from_cached`**: for a union rule it iterates each
  branch and, per focus atom, builds the standard focus/old timestamp
  constraints (`GeConst` on the focus atom's `ts_col`, `LtConst` on the atoms
  before it) over that branch's atoms only. Each `(branch_index, constraints)` is
  one *variant*. It calls `RuleSetBuilder::add_union_rule_from_cached`.
- **`core-relations` `add_union_rule_from_cached`**: builds a single variant of
  the cached union plan whose `JoinStage::Union` holds one *variant branch* per
  variant — the cached branch narrowed by that variant's timestamp constraints
  applied as extra `JoinHeader`s (`reprocess_union_branch`). All variant branches
  feed the one deduplicating block-0 materialization and the shared action, so a
  row reached via several branches (or several focus atoms) is still processed
  once. This is how the branch delta constraint reaches the branch sub-plan: it
  becomes a header on that branch, which `execute.rs`'s `JoinStage::Union`
  handler already intersects into the branch's atom subsets before running it.

Independent `or`s (no correlation) keep the scanned-once continuation and run
naive.

### Restrictions

- **Independent `or`s run naive** (re-matched each iteration). Only correlated
  `or`s are delta-driven. (Seminaive of an independent `or` whose conjunction is
  a continuation would need the delta split between the continuation and the
  branches; prepending the conjunction into the branches, as the correlated path
  does, is the route to make it delta-driven.)
- **Primitives in branches** are rejected (a branch must be a conjunction of
  table atoms). Primitives in the surrounding conjunction are fine; a `!=`
  staleness filter is encoded as a staleness relation instead.
- **`∏` branches for multiple/nested `or`s.** `k` disjunctions produce `∏` union
  *branches* (enumerated additively into one deduplicated materialization), but
  still a single rule. A single `or` (the common case) is linear.
- **Dedup granularity.** Deduplication is on the (non-`Unit`) output tuple. For a
  correlated rebuild the output is the surrounding row, giving single-rebuild.
- **Branch-bound output (Shape B).** A layout where each branch *binds* the
  output row itself and pins an outer variable into a different column per branch
  (e.g. `((AddView a x1 x2)) ((AddView x0 a x2)) ...`) is not supported: aligning
  the per-branch row columns onto shared output variables would need per-branch
  output projections on the union node. The prepended-conjunction layout above
  covers the same rebuild use case.

## Proofs and the term encoding

`or` is allowed under the term encoding **without** proofs: `proof_form`
normalizes each branch independently, and `instrument_fact` rewrites each
branch's atoms to view-table lookups and re-emits an `(or (branch...) ...)`
fact, which is then compiled by the strategies above. With proofs enabled the
instrumentation panics (`or` is unsupported with proofs). `:unsafe-seminaive`
remains unsupported under the term encoding regardless (a pre-existing
limitation, since it performs arbitrary live-database reads).

### Per-constructor rebuild rule

Without proofs, the term encoding rebuilds each constructor's view with the
[correlated rebuild pattern](#the-correlated-rebuild-pattern) above
(`rebuilding_rules_correlated` in `src/proofs/proof_encoding.rs`). Each eq-sort
column `S` gets one hidden per-sort staleness relation and a monotone
maintenance rule that mirrors non-canonical UF parent edges into it:

```
(function stale_S (S S) Unit :merge old :internal-hidden)
(rule ((UF_S t l) (!= t l)) ((set (stale_S t l) ())) :ruleset rebuilding)
```

The rebuild rule then correlates the view against those staleness relations
(one `OR` branch per eq-sort column), re-looks-up each column's current leader
in the UF index in the action, and deletes the stale row. A view with a single
eq-sort column degenerates to the plain delta-driven rule
`((View ..) (UF_S ci e) (!= ci e))` (no one-branch `OR`); with none, no rebuild
rule is emitted. Non-eq-sort columns (including container sorts, which are not
`is_eq_sort`) are left untouched, as before.

Staleness is a monotone superset of non-canonical terms — a term never becomes
canonical again — and the action re-derives the current leader, so an outdated
`stale_S` row is harmless. The rule is marked `:unsafe-seminaive` for the action
reads; the maintenance rule is ordinary Datalog. Because rebuild runs to a
fixpoint, this produces the same final e-graph as the proof-mode rule, which
keeps the earlier `(guard (or (bool-!= ...)))` formulation since `OR` is
unsupported under proofs.
