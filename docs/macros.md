# Writing egglog macros

Register a transformer by **space and name**. The same `Macro` interface handles
commands, actions, expressions, facts, and schedules:

```rust
use egglog::ast::{Expr, ParseError};
use egglog::macros::{Expansion, Fragment, MacroContext, Space, Syntax};
use egglog::EGraph;
use std::sync::Arc;

let mut eg = EGraph::default();
eg.parser.macros().register(
    Space::Expr,
    "double",
    Arc::new(|input: &Syntax, cx: &mut MacroContext<'_>| {
        let (_, args, span) = input.expect_call("double")?;
        let [arg] = args else {
            return Err(ParseError(span, "expected (double expr)".into()));
        };
        let arg = cx.parser().parse_expr(arg)?;
        Ok(Expansion::Parsed(Fragment::Expr(Expr::Call(
            span.clone(), "*".into(),
            vec![arg, Expr::Lit(span, egglog::ast::Literal::Int(2))],
        ))))
    }),
);
eg.parse_and_run_program(None, "(check (= (double 3) 6))")?;
# Ok::<(), egglog::Error>(())
```

There is one registration API. A transformer's result determines what happens
next:

| Result | Meaning |
| --- | --- |
| `Expansion::Syntax` | Expand the returned structured syntax in the same space. |
| `Expansion::Sequence` | Expand each command or action in order. |
| `Expansion::Parsed` | Use a parsed fragment without expanding its root again. |
| `Expansion::Deferred` | Contribute constraints now; finish after enclosing inference. |

`Syntax` is a cloneable, spanned s-expression with embedded parsed fragments and
captured macro bindings. A parent decides which children to expand by calling
`cx.expand(space, child)` or a category-specific parser method. It can also
rewrite or discard a child without expanding it. `Fragment::syntax(span)` embeds
a previously parsed fragment without printing and reparsing it.

`parse_and_run_program` and `resolve_program` drive ordered expansion.
`parse_program` retains commands as `Command::Unexpanded` when macros are
installed; passing those commands to `run_program` uses the same driver. A
standalone `Parser::parse_expr` or `parse_command` can expand syntax immediately,
but has no declaration environment unless a driver has supplied one.

## Declaring things before their uses

A command macro can return:

```rust
Expansion::Sequence(Parser::read_syntax(None, "
    (datatype Packet (PacketValue i64))
    (derive-record-view Packet)
    (use-record-view Packet)
")?)
```

The driver checks the first declaration before invoking `derive-record-view`.
That transformer can inspect `cx.types().get_func_types()` for constructor
signatures in stable name order, generate its own sorts and
constructors, and make them available to `use-record-view`. The generated
siblings are processed in the same order in resolve-only and execution modes.

For programmatic construction, build `Syntax` or `Command` values directly.
Reading a fixed template is convenient, but carrying syntax through strings is
unnecessary and loses captured bindings and parsed fragments.

`datatype*` discovers nominal sort headers first, then parameterized sorts, then
constructors. When a constructor transformer is installed, variants explicitly
delegate to the constructor binding captured at datatype expansion. For example:

```lisp
(datatype*
  (Tree (Leaf i64) (Node Trees))
  (sort Trees (Vec Tree)))
```

Both `Tree` and `Trees` are available when the `Leaf` and `Node` constructor
transformers run. This supports constructor extensions such as experimental's
`:regions` without a separate constructor-option registry.

## Extending a builtin and wrapping declarations

Capture the previous binding before replacing it:

```rust
let previous = eg.parser.macros().lookup(Space::Command, "constructor");
eg.parser.macros().register(
    Space::Command,
    "constructor",
    Arc::new(move |input: &Syntax, cx: &mut MacroContext<'_>| {
        // Inspect/rewrite input here, then delegate to the captured binding.
        previous.apply(input, cx)
    }),
);
```

`MacroBinding::core(space)` selects the core parser independently of shadowing.
`binding.bind(syntax)` places that binding on one syntax occurrence. Descendants
still expand normally. Use `cx.fresh` for names embedded in AST values, or
`cx.fresh_syntax` for generated identifiers embedded in syntax. These names
cannot collide with ordinary source names. This API supplies fresh names and
captured macro bindings; it does not implement general lexical scope sets.

A wrapper that wants to modify generated declarations should use
`Expansion::map_commands`. It visits parsed commands lazily: an earlier generated
sort becomes available before a later constructor transformer is invoked. A
mapper can return the original constructor followed by a cost-table declaration.
Other commands, including an extension's metadata commands, pass through.
Experimental's `with-dynamic-cost` uses this API, so it composes with `datatype*`
and the `:regions` constructor transformer.

## Deferring until types are known

A typed transformer returns `Deferred` from the same `expand` method. It supplies:

- Parsed operand expressions.
- Constraints over operand slots followed by the result slot.
- A completion callback receiving resolved operands, the result sort, and a
  `FinishContext`.

An action has an internal `Unit` result slot. `Same(a, b)` equates two slots,
`Is(a, sort)` fixes a slot, and `EqSort(a)` requires an equality sort. The last
constraint filters overloads but does not choose an otherwise unknown nominal
sort.

A type-preserving expression wrapper looks like this:

```rust
use egglog::macros::{Completion, Deferred, SortConstraint};

let operand = cx.parser().parse_expr(child)?;
let expansion = Expansion::Deferred(Deferred {
    operands: vec![operand],
    constraints: vec![SortConstraint::Same(0, 1)],
    finish: Arc::new(|_cx, operands, _sort| {
        Ok(Completion::Expr(operands[0].clone()))
    }),
});
```

The whole rule body and head are inferred together, using the existing primitive
constraint engine. Completion is not a second, independent inference request
on a guessed expression. Nested deferred operands finish first. Call operands
are bound to temporaries, preserving their evaluation order and ensuring a
callback can reuse an operand without executing it twice. Existing `let`
bindings retain their sharing.

A callback may call `cx.declare` to create helper sorts, constructors, functions,
or relations. The declaration is checked immediately, becomes visible through
`cx.types()`, and is emitted before the consuming rule/action. `cx.call` constructs
a resolved table call. Completion output is checked against the already inferred
types and overload choices; it cannot introduce another unresolved macro call.

`cx.query_bindings` contains the resolved local body bindings in source traversal
order. It excludes global references. This gives a fresh-value macro a stable
key for the whole query match.

### Worked example: inferred fresh values and effectful marks

With egglog-experimental:

```lisp
(datatype State (Initial))
(datatype Value (Constant i64))
(relation Input (i64))
(relation Seen (State))

(Input 7)
(rule ((Input key))
  ((let state (unstable-fresh! :cost 3))
   (set-effectful state)
   (Seen state)))
(run 1)
(check (Seen state) (effsafe_effectful_State state))
```

1. `unstable-fresh!` contributes an equality-sort result slot, say `T`.
2. `let state` and both uses of `state` refer to that same slot.
3. `set-effectful` requires an equality sort; `Seen` supplies `T = State`.
4. The fresh callback declares a constructor with input `(i64 i64)` and output
   `State`. Its key contains `key` and an occurrence component.
5. The mark callback declares `effsafe_effectful_State` once and emits its call.

Each fresh occurrence gets its own constructor, so differing inferred sorts,
costs, or `:unextractable` options do not interfere. Repeated evaluation of the
same rule match uses the same keys. Explicit `(unstable-fresh! State)` and
`(set-effectful State expr)` annotations remain available when needed.

With no constraining use, this is an inference error:

```lisp
(rule () ((set-effectful (unstable-fresh!))))
```

The expander does not pick `State` merely because it is an equality sort in
scope. Add an explicit sort or another use in the same rule.

### Worked example: information flowing back into a query

```lisp
(sort Ints (Vec i64))
(sort Floats (Vec f64))
(relation Save (Ints))
(rule ((= values (vec-empty)))
  ((Save (type-preserving-wrapper! values))))
```

The wrapper equates its operand and result slots. `Save` determines `Ints`, which
flows back to `values` and selects the corresponding `vec-empty` overload. The
body is not separately inferred before the head.

## Boundaries of this implementation

Deferred expressions and actions are supported in rule heads and top-level
actions. Queries, merge expressions, schedule conditions, and other command
positions must use ordinary expansion. Expansion requires a finite, fully
solvable inference region; there is no speculative callback scheduling or
unbounded expand/infer fixed point.

A generated type may depend on explicitly available declaration metadata:
`(derive-record-view Packet)` before a rule can inspect `Packet` and emit its
view type. A deferred callback may also create a helper whose complete interface
is determined by an already solved sort. It cannot create missing declarations
that the *same* inference problem needed to determine its operand/result types.
Move that declaration before the rule or supply an explicit annotation.

## Frontend and runtime integration

`TypeInfo::default()` creates the builtin declaration and primitive environment
without a backend. Sort registration hooks receive `&mut TypeInfo`. Primitive
registration records a logical definition, valid contexts, and an installer;
`EGraph` owns backend IDs. Standalone expression/rule checking and proof-mode
source checking use this environment.

`TypeInfo::seminaive` determines inference contexts. Use `EGraph::set_seminaive`
to change an e-graph's checking and execution policy together:

| Region | Query context | Action context |
| --- | --- | --- |
| Default seminaive rule | `Pure` | `Write` |
| `:naive`, `:unsafe-seminaive`, or globally naive | `Read` | `Full` |
| Standalone check / top-level action | `Read` | `Full` |
| Merge expression | — | `Write` |

A runtime command that creates declarations implements `UserDefinedCommand::declare`
using only `TypeInfo` and a name supply. It runs in both resolve-only and execution
pipelines. Its `update` method performs runtime installation or effects.
Experimental's `(primitive ...)` uses this split. Runtime extraction, scheduling,
and database inspection continue to use ordinary runtime commands.

The former `Macro<T>` parser registrations and `CommandMacro` pass registry are
removed. See `tests/test_command_macros.rs` and experimental's
`tests/unified_macros.rs` for executable examples, including resolve/replay,
ambiguity, constructor delegation, sharing, and source types in proof mode.
