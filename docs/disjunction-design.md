# Disjunction (`OR`) in egglog rule bodies

Status: **Strategy B (materialized union) is implemented in the `core-relations`
query planner** — the disjunction is materialized as a bag inside the
tree-decomposed plan, not rewritten into egglog relations/rules. Strategy A
(rule-splitting) is the reference semantics; Strategy C (native streaming union
node) is future work. See §4 for the comparison.

This document covers the syntax, semantics, and the strategies for executing
disjunction efficiently in the backend.

## 1. Syntax

A disjunction may appear anywhere a fact may appear in a rule body:

```
(rule ( fact*
        (OR (branch) (branch) ...)
        fact* )
      (action*))
```

Each `branch` is a **parenthesized list of facts** — a conjunctive subquery:

```
; connected is the symmetric closure of edge
(rule ((OR ((edge x y))
           ((edge y x))))
      ((connected x y)))
```

A branch with several facts is just a longer list:

```
(rule ((OR ((edge x m) (edge m y))     ; two-hop path
           ((edge x y))))              ; or a direct edge
      ((path x y)))
```

`OR`s may be nested, and a body may contain several `OR`s.

### Why `OR` (uppercase) and why branches are lists

- **Uppercase `OR` avoids a name clash.** egglog already defines a boolean
  primitive `or` (`src/sort/bool.rs:27`) usable in expression position, e.g.
  `(let b (or p q))`. A bare boolean fact `(or p q)` in a body is therefore
  already meaningful. Using the distinct, case-sensitive head `OR` keeps
  disjunction unambiguous and leaves every existing program untouched. (A
  lowercase spelling like `query-or` would work equally well; the parser matches
  a single constant, `OR_HEAD` in `src/ast/parse.rs`.)
- **Branches are lists, not bare facts.** A branch is a *conjunction*, so it is a
  list `(f1 f2 ...)`. A single-fact branch is `((edge x y))`. This is also what
  disambiguates `OR` from an ordinary call: the arguments of `OR` are always
  lists of facts.

## 2. Semantics

A rule body denotes a first-order formula. `OR` is logical disjunction, so a body

```
C ∧ (D₁ ∨ D₂ ∨ ... ∨ Dₙ)
```

(where `C` is the surrounding conjunction and each `Dᵢ` is a branch) matches a
substitution iff `C` holds and at least one `Dᵢ` holds. The rule fires once per
satisfying substitution of the variables visible to the actions.

### The common-variable rule

> Only variables that appear in **every** branch of an `OR` (together with the
> variables bound by the surrounding conjunction) may be used in the actions.

A variable that occurs in only some branches is *existentially quantified inside*
the disjunction and is not defined when a different branch is the witness. Forbidding
its use in the actions is what makes an `OR` behave like a derived relation over its
common variables: given the outer bindings, the disjunction ranges over tuples of
the common variables and nothing else.

Concretely, `(OR ((edge x y)) ((edge y x)))` has common variables `{x, y}`, so
`(connected x y)` is well-formed. But in `(OR ((edge x y)) ((edge x z)))`, `y`
is bound only in the first branch, so an action mentioning `y` is rejected.

### Interaction with the e-graph

egglog actions are idempotent with respect to the database: inserting the same row
or unioning the same two ids twice has no additional effect. Because the actions can
only reference common variables, if two branches match for the same binding of the
common variables the two firings perform *identical* work. Disjunction is therefore
sound regardless of how many branches match; the only question is how much redundant
work an implementation does (see §4).

## 3. Reference semantics: parse-time distribution (Strategy A)

The following describes the rule-splitting strategy, which is the *reference
semantics* any backend implementation must match, not the current backend (which
is Strategy B, §4).


Disjunction distributes over conjunction:

```
C ∧ (D₁ ∨ ... ∨ Dₙ)   ≡   (C ∧ D₁) ∨ ... ∨ (C ∧ Dₙ)
```

and a disjunction of rule bodies is exactly a set of rules: distributing a body
into the **cartesian product** of its branch choices yields one ordinary rule per
combination (`∏ mᵢ` rules for `k` disjunctions of sizes `m₁..mₖ`). This is the
textbook meaning of a disjunctive body and the semantics the backend (§4) must
match; it composes with seminaive and proofs because every product rule is an
ordinary conjunctive rule.

### Limitations

1. **Combinatorial blowup.** `∏ mᵢ` rules for `k` disjunctions. Small in practice
   (2–4 branches, 1–2 `OR`s), but multiplicative.
2. **Redundant firing.** If several branches match the same common-variable binding,
   the action runs once per matching branch. Idempotent, so correct, but wasted work.
3. **Shared outer work is re-planned.** The surrounding conjunction `C` is compiled
   and evaluated independently in every product rule.

These are exactly what a native backend implementation (§4) removes.

## 4. Efficient backend execution

The key reframing: an `OR` is a **derived relation** over its common variables
`V = ⋂ᵢ vars(Dᵢ)`:

```
R_or(V) = ⋃ᵢ π_V( Dᵢ )
```

Each branch `Dᵢ` is a conjunctive subquery; project its results onto `V` and union
them. The rest of the rule is then an ordinary conjunctive query with one extra atom
`R_or(V)`. This makes the common-variable rule structural (only `V` is exposed) and
removes redundant firing (the union is a set).

There are three implementation levels, in increasing order of backend intrusion.

### Strategy A — rule-splitting (the current prototype)

Frontend-only, described in §3. Correct, seminaive-friendly, zero backend change.
Best baseline; suffers blowup and redundant firing.

### Strategy B — materialized union in the query planner (implemented)

This is what the codebase does today. An `OR` is materialized as a **bag inside the
tree-decomposed plan** in `core-relations`; there are **no** egglog-level relations
or auxiliary rules. The union relation `R_or(V) = ⋃ᵢ π_V(Dᵢ)` is a materialization
keyed on the common variables `V`, computed once, and the rest of the query joins
against it using the *same* materialization machinery the planner already uses for
hypertree decomposition (Yannakakis): a bag materialized on its *message variables*,
which its parent joins against to prune its search
(`core-relations/src/free_join/plan.rs` module doc; `DecomposedPlan`, `MatSpec`,
`MatId`/`MatScanMode`, `JoinStage::FusedIntersectMat`).

#### The pipeline, end to end

- **Typechecking** (`src/typechecking.rs`, `typecheck_rule_with_or`). The body is
  split into its conjunctive facts and its `OR`s. Nested `OR`s are flattened to a flat
  list of conjunctive branches (DNF, `flatten_or_branches`). The conjunctive facts and
  every branch are added to a single constraint `Problem` — with each branch's
  *branch-local* variables renamed fresh so distinct branches never collide, while the
  common variables keep their names and unify to one sort. The interface rule (only a
  disjunction's common variables may be used outside it) is enforced on the original
  names (`OrBranchLocalEscapes`). The result carries each disjunction as a
  `ResolvedFact::Or`.
- **Frontend → backend** (`src/lib.rs`, `add_rule` / `lower_or_groups` / `BackendRule`).
  `OR`s are pulled out of the flat core query (`Facts::to_query` skips them); each
  branch is lowered to a canonicalized core query, and its common variables are passed
  as `extra_bound` so the actions may reference them. `BackendRule::unions` emits each
  branch's table atoms and then a single `RuleBuilder::query_union(output_vars, branches)`.
- **Bridge** (`egglog-bridge/src/rule.rs`). `query_union` records the branches (as
  indices into the query's atoms) and the shared `output_vars`. Adding a union forces
  the whole rule out of seminaive. `build_cached_plan` translates the branch atom
  indices to `core-relations` `AtomId`s and calls `QueryBuilder::add_union`.
- **Planner** (`core-relations/src/free_join/plan.rs`, `plan_union_query`). Each
  branch is planned (over its own atoms) into `JoinStages` that project onto `V`. Each
  `OR` becomes a leading materialization bag (`UnionMat`, `MatSpec { msg_vars: V,
  val_vars: [] }`); the surrounding conjunction is planned as an ordinary bag that
  joins against those materializations via `plan_single_bag`'s prologue
  (`FusedIntersectMat`), reusing the decomposition path. `build_union_result_block`
  gathers the final bindings. The result is a `Plan::UnionPlan`.
- **Executor** (`core-relations/src/free_join/execute.rs`, `run_union_plan_serial`).
  Each union's branches are run into one materialization (keyed on `V`) and deduped so
  each `V`-tuple appears once (a set); then the body bags run, then the result block
  fires the actions.

Benefits: no rule blowup (each branch planned once), automatic dedup (the union is a
set — no redundant firing), and the surrounding conjunction is planned and evaluated
once.

#### Restrictions of the current implementation

- **Naive, whole-table evaluation.** Unions are recomputed in full; there is no
  seminaive delta *through* a disjunction (adding a union opts the rule out of
  seminaive). Programs must be run to a fixpoint. This is acceptable because
  rule-splitting (A) already gives correct seminaive behavior as the reference.
- **Union bags are forced to be the leading bags.** The disjunction is not integrated
  into the tree-decomposition cost model; the surrounding conjunction is planned as a
  single bag joined against the union materializations.
- **No primitives inside a branch.** Branches may contain only table atoms.
- **Unsupported under proofs / term encoding.** `OR` rules are rejected in those modes
  (a proof would need to record which branch witnessed a match).

### Strategy C — native streaming union operator in free join

A first-class `Union` node in the execution plan that enumerates each branch's
tuples and yields their `π_V` to the continuation with on-the-fly dedup, avoiding
materialization. The most invasive option (see §5); future work.

### Comparison

| | A: rule-splitting | B: materialized union (current) | C: native union node |
|---|---|---|---|
| Backend changes | none | moderate (planner + bridge) | large (planner + executor) |
| Rule blowup | `∏ mᵢ` | none | none |
| Redundant firing | yes (idempotent) | no (set union) | no (dedup) |
| Outer work shared | no | yes | yes |
| Seminaive | free | no (whole-table) | needs delta maintenance |
| Streaming (no materialize) | n/a | no | yes |

## 5. Status and future work

Strategy B is the shipped backend. Strategy A remains the reference semantics: any
backend must produce the same fixpoint as A on the same input.

- **Seminaive through unions.** B recomputes each union in full every iteration. A
  delta scheme (recompute only branch deltas, treat the union's new rows as the outer
  delta) would restore incrementality; it requires the union bag to participate in
  seminaive variant expansion (`egglog-bridge/src/rule.rs`, `add_rules_from_cached`).
- **Cost-model integration.** Union bags are currently forced to be the leading bags
  rather than placed by the tree-decomposition heuristics.
- **Primitives in branches.** Not yet supported; a branch may contain only table atoms.
- **Proof support.** `OR` rules are rejected under proofs/term encoding. Supporting
  them needs the union to record which branch witnessed a match to reconstruct
  provenance.
- **Strategy C (streaming union node).** A first-class `Union` `JoinStage` that yields
  each branch's `π_V` to the continuation with on-the-fly dedup would avoid
  materializing the union. Most invasive (executor + cost model + seminaive); only
  worth it if profiling implicates materialization.

## Key code references

- Surface parsing: `src/ast/parse.rs` (`OR_HEAD`, `parse_fact`).
- Fact/rule AST: `egglog-ast/src/generic_ast.rs` (`GenericFact::Or`); the `map_symbols`
  / `visit_exprs` recursion in `egglog-ast/src/generic_ast_helpers.rs`.
- Typechecking: `src/typechecking.rs` (`typecheck_rule_with_or`, `flatten_or_branches`,
  `common_branch_vars`; `TypeError::OrBranchLocalEscapes` / `EmptyOrBranch`).
- Frontend → backend: `src/lib.rs` (`add_rule`, `lower_or_groups`, `LoweredOrGroup`,
  `resolved_common_vars`, `BackendRule::unions`); `src/core.rs` (`to_core_rule`'s
  `extra_bound`).
- Bridge: `egglog-bridge/src/rule.rs` (`RuleBuilder::query_union`, `BridgeUnion`,
  `build_cached_plan`).
- Planner: `core-relations/src/query.rs` (`QueryBuilder::add_union`, `UnionSpec`);
  `core-relations/src/free_join/plan.rs` (`plan_union_query`, `UnionPlan`, `UnionMat`,
  `build_union_result_block`).
- Executor: `core-relations/src/free_join/execute.rs` (`run_union_plan_serial`,
  `dedup_union_mat`).
- Boolean `or` primitive (the name we avoid): `src/sort/bool.rs`.
