# Disjunction (`OR`) in egglog rule bodies

Status: **prototype implemented** (parse-time distribution) + design for efficient
backend execution.

This document explores adding disjunction to rule queries: syntax, semantics, the
current prototype, and how to execute it efficiently in the backend.

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

## 3. Current implementation: parse-time distribution

Disjunction distributes over conjunction:

```
C ∧ (D₁ ∨ ... ∨ Dₙ)   ≡   (C ∧ D₁) ∨ ... ∨ (C ∧ Dₙ)
```

and a disjunction of rule bodies is exactly a set of rules. So the prototype expands
a body into the **cartesian product** of its branch choices at parse time, emitting
one ordinary rule per combination. With `k` disjunctions of sizes `m₁..mₖ`, it emits
`∏ mᵢ` rules.

Implementation (`src/ast/parse.rs`):

- `expand_or_body` walks the raw body s-expressions and returns one flat body per
  combination (recursively handling nested `OR`). A body with no `OR` yields exactly
  one combination, so non-disjunctive rules are unaffected.
- The `"rule"` command arm parses each combination into its own `Rule`. The command
  parser already returns `Vec<Command>`, so no new machinery is needed. Anonymous
  rules are named by their textual form (`src/ast/desugar.rs:434`), which differs per
  combination; explicitly named rules get a `__or<i>` suffix.
- The `"fail"` command arm now tolerates a sub-command that expands to several
  commands (previously a `todo!()`), mirroring how desugaring already handles
  `fail` (`src/ast/desugar.rs:188`).

Everything downstream — typechecking, canonicalization to `CoreRule`
(`src/core.rs`), the bridge (`egglog-bridge`), and execution (`core-relations`) — is
untouched: it only ever sees ordinary conjunctive rules.

### Why this is correct and complete

- **Semantics:** distribution is the textbook meaning of a disjunctive body.
- **The common-variable rule is enforced for free.** If an action uses a variable
  bound in only some branches, the product rule that chose a branch *without* that
  variable fails egglog's existing unbound-variable check (`typechecking.rs`), so the
  whole rule is rejected. (The error message names the offending variable but not the
  `OR` — see §6.)
- **Seminaive evaluation composes.** Each product rule is a normal rule and is run
  incrementally by the existing seminaive machinery
  (`egglog-bridge/src/rule.rs`, `add_rules_from_cached`).

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

### Strategy B — materialized union subquery (recommended next step)

Compile `R_or` to a **materialized intermediate relation** and give the outer query a
single atom over it. This is precisely what the planner already does for hypertree
decomposition (Yannakakis): `core-relations` breaks a query into *bags*, materializes
a bag keyed on the *message variables* it shares with its parent, and the parent joins
against that materialization to prune its search
(`core-relations/src/free_join/plan.rs:6-25`, `DecomposedPlan` at line 284,
`MatId`/`MatScanMode` at 83-91).

An `OR` maps onto this almost directly:

- Treat each branch `Dᵢ` as a bag whose message variables are `V`.
- Instead of one materialization per bag feeding a parent, **union** the `π_V(Dᵢ)`
  materializations into one relation `R_or` keyed on `V`.
- The outer query gets a synthetic atom `R_or(V)` and is planned normally.

Where it plugs in:

- Bridge: extend the query builder (`egglog-bridge/src/rule.rs`, `Query.atoms` and
  `query_table`/`query_prim`) with a "union atom" that carries a list of branch
  sub-queries and their shared columns `V`.
- Planner: lower the union atom to N branch plans plus a union-into-`R_or` step,
  reusing the existing bag-materialization code path in `plan.rs`, then expose `R_or`
  as an ordinary scannable atom to the outer plan.

Benefits: no rule blowup (each branch planned once), automatic dedup (the union is a
set, so no redundant firing), and the outer conjunction is planned once.

**The hard part — seminaive maintenance.** Rules run to fixpoint and seminaive only
considers *new* tuples each iteration. A materialized `R_or` must therefore be
maintained incrementally: a tuple in `R_or` is "new" this iteration if it is produced
by a branch from at least one new input tuple. The existing seminaive scheme
(`egglog-bridge/src/rule.rs`, `add_rules_from_cached`) builds, for an N-atom query, N
variants that each force one atom to the new-tuple delta. The analogous rule for a
union atom is a union over branches of a union over each branch's atoms — i.e. `R_or`'s
delta is `⋃ᵢ (delta of branch Dᵢ)`. Two viable designs:

- *Delta materialization:* recompute only the branch deltas each iteration and union
  them into `R_or`; treat `R_or`'s own new rows as the delta for the outer join. This
  keeps full incrementality but requires the union atom to participate in the
  seminaive variant expansion.
- *Recompute-per-iteration:* rematerialize `R_or` fully each iteration and diff. Much
  simpler, loses incrementality for the disjunctive part; acceptable when branches are
  cheap or the disjunction is small.

Because rule-splitting (A) already gives correct seminaive behavior, B is best viewed
as an optimization that a rule can *opt into* (e.g. when branch counts or shared outer
work make blowup expensive), not a wholesale replacement.

### Strategy C — native union operator in free join

Add a first-class `Union` node to the execution plan (`Plan`/`JoinStage` in
`plan.rs`, executed in `core-relations/src/free_join/execute.rs`) that enumerates
each branch's satisfying tuples and yields their projection onto `V` to the
continuation, deduplicating on the fly. This avoids materializing `R_or` when the
outer query consumes it in a streaming fashion, but it is the most invasive: the join
executor, the cost model, and seminaive variant generation all must learn about the
new node. Only worth it if profiling shows materialization (B) is the bottleneck.

### Comparison

| | A: rule-splitting | B: materialized union | C: native union node |
|---|---|---|---|
| Backend changes | none | moderate (bridge + planner) | large (planner + executor) |
| Rule blowup | `∏ mᵢ` | none | none |
| Redundant firing | yes (idempotent) | no (set union) | no (dedup) |
| Outer work shared | no | yes | yes |
| Seminaive | free | needs delta maintenance | needs delta maintenance |
| Streaming (no materialize) | n/a | no | yes |

## 5. Recommendation

1. **Ship Strategy A** as the semantics and surface syntax (done). It is correct,
   composes with seminaive and proofs, and needs no backend work.
2. **Add Strategy B behind the scenes** as an optimization the planner applies when a
   rule has disjunctions whose blowup or shared outer work is significant, reusing the
   existing bag-materialization path. Keep A as the fallback and as the reference
   semantics for testing (B must produce the same fixpoint as A).
3. **Consider Strategy C** only if profiling implicates materialization.

## 6. Open questions / future work

- **Error messages.** Distribution reports a bare "unbound variable" for a
  common-variable violation. A dedicated pre-pass over the surface body could compute
  the common variables of each `OR` and report a targeted error that names the `OR`
  and the offending branch.
- **`fail` atomicity.** `(fail (rule-with-OR ...))` currently runs the leading product
  rules for real and only asserts the last one fails (matching the existing `fail`
  desugaring). This is moot for typecheck errors — which escape `fail` entirely in
  egglog — but a group/transactional command would make `fail` over multi-expansions
  clean.
- **Equivalence testing for B/C.** Any backend implementation should be differentially
  tested against Strategy A on the same programs: same database in ⇒ same e-graph out.
- **Proof support.** Under A, proofs work unchanged because only ordinary rules reach
  the proof machinery. B/C would need to record which branch witnessed a match to
  reconstruct provenance.

## Key code references

- Surface parsing / distribution: `src/ast/parse.rs` (`expand_or_body`, `OR_HEAD`,
  the `"rule"` and `"fail"` command arms).
- Fact/rule AST: `egglog-ast/src/generic_ast.rs:35` (`GenericFact`), `:107`
  (`GenericRule`).
- Query lowering & variable binding: `src/core.rs:374` (`Query`), `:412` (`get_vars`),
  `to_core_rule`; binding handed to actions in `src/typechecking.rs`.
- Bridge rule building: `egglog-bridge/src/rule.rs` (`RuleBuilder`, `query_table`,
  `build`, `add_rules_from_cached` for seminaive).
- Backend planning/execution: `core-relations/src/free_join/plan.rs` (hypertree
  decomposition, `DecomposedPlan`, materialization), `core-relations/src/free_join/execute.rs`
  (`run_rule_set`).
- Boolean `or` primitive (the name we avoid): `src/sort/bool.rs:27`.
