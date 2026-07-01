# A native union-of-subqueries primitive for `core-relations`

This adds `RuleSetBuilder::add_union` to the `core-relations` free-join engine — a
backend building block for disjunction (`OR`) in rule bodies. It is the "Strategy C"
(native backend) direction from the disjunction design; see below for how it relates
to the materialized-union Strategy B.

## API

```rust
pub fn add_union<F>(&mut self, output_arity: usize, branches: Vec<F>) -> TableId
where
    F: FnOnce(&mut QueryBuilder) -> Vec<QueryEntry>;
```

Each branch is a sub-query (a conjunction of atoms) that returns the `output_arity`
entries it binds as its output tuple. `add_union`:

1. creates a fresh ephemeral table whose columns are **all keys**, so identical
   output tuples collapse to one row (this is the deduplication);
2. compiles each branch to an ordinary rule whose action inserts that branch's output
   tuple into the table;
3. returns the table id.

Downstream code scans the returned table as a normal atom to consume each distinct
union tuple. See the unit test `tests::union_disjunction` for a worked example
(`R(x) := A(x) OR B(x)`, asserting the deduplicated union and single-fire per tuple).

## How this relates to Strategies B and C

The disjunction design describes two efficient backends:

- **B — materialized union**: materialize `⋃ᵢ πV(branchᵢ)` into a relation keyed on
  the common variables `V`, then join it as one atom.
- **C — native fused union node**: a `JoinStage::Union` that streams each branch's
  `V`-tuples into the continuation in a single pass, without materializing.

`add_union` implements the **materialized** form at the `core-relations` level: the
ephemeral all-key table *is* the materialization, and deduplication is the table's
merge. Observably this matches Strategy B (a materialized, deduplicated relation), one
level below egglog's rule layer.

The genuinely-distinct **fused** Strategy C — a single-pass `JoinStage::Union` that
never materializes — was intentionally **not** built here: it requires threading
nested sub-plan execution through the recursive `run_plan` / `ActionBuffer` machinery
in `core-relations/src/free_join/execute.rs`, a much larger change, for the same
observable result on these examples. This primitive is the pragmatic foundation; the
fused node remains future work.

## Restrictions

- Naive / whole-table evaluation: no seminaive (timestamp/delta) filtering of the
  union; each branch re-runs over full tables.
- The union forms the leading part of a query; its output is a plain table that
  downstream rules join against.
- The result is delivered via a table, so callers must run the rule set and
  `Database::merge_all()` before scanning it.
