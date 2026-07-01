//! Tests for `OR` disjunctions in rule bodies.
//!
//! `(OR (b1 ...) (b2 ...) ...)` inside a rule query matches when any branch
//! matches. Each branch is a conjunctive subquery. A rule body is expanded into
//! the cartesian product of its branch choices, so only variables bound in every
//! branch (the common variables) can be referenced by the actions.

use egglog::Error;
use egglog::prelude::*;

/// Both branches of an `OR` fire, so `connected` becomes the symmetric closure
/// of `edge`. The reverse direction is only derivable via the second branch.
#[test]
fn symmetric_closure_via_or() -> Result<(), Error> {
    let mut egraph = EGraph::default();
    egraph.parse_and_run_program(
        None,
        "
(relation edge (i64 i64))
(relation connected (i64 i64))
(edge 1 2)
(edge 3 2)

(rule ((OR ((edge x y)) ((edge y x))))
      ((connected x y)))
(run 1)

(check (connected 1 2))
(check (connected 3 2))
(check (connected 2 1))
(check (connected 2 3))
; a pair that shares no edge in either direction must be absent
(fail (check (connected 1 3)))
",
    )?;
    Ok(())
}

/// Two `OR` groups in one body expand to the cartesian product (2 x 2 rules).
#[test]
fn cartesian_product_of_two_or_groups() -> Result<(), Error> {
    let mut egraph = EGraph::default();
    egraph.parse_and_run_program(
        None,
        "
(relation p (i64))
(relation q (i64))
(relation r (i64))
(relation s (i64))
(relation out (i64 i64))
(p 1) (q 2) (r 3) (s 4)

(rule ((OR ((p a)) ((q a)))
       (OR ((r b)) ((s b))))
      ((out a b)))
(run 1)

(check (out 1 3))
(check (out 1 4))
(check (out 2 3))
(check (out 2 4))
",
    )?;
    Ok(())
}

/// An `OR` nested inside a branch expands recursively.
#[test]
fn nested_or() -> Result<(), Error> {
    let mut egraph = EGraph::default();
    egraph.parse_and_run_program(
        None,
        "
(relation a (i64))
(relation b (i64))
(relation c (i64))
(relation hit (i64))
(a 1) (b 2) (c 3)

; (a x) OR ((b x) OR (c x))  ==  (a x) OR (b x) OR (c x)
(rule ((OR ((a x))
           ((OR ((b x)) ((c x))))))
      ((hit x)))
(run 1)

(check (hit 1))
(check (hit 2))
(check (hit 3))
",
    )?;
    Ok(())
}

/// A single-branch `OR` behaves like a plain conjunction.
#[test]
fn single_branch_or() -> Result<(), Error> {
    let mut egraph = EGraph::default();
    egraph.parse_and_run_program(
        None,
        "
(relation edge (i64 i64))
(relation two-step (i64 i64))
(edge 1 2)
(edge 2 3)

(rule ((OR ((edge x y) (edge y z))))
      ((two-step x z)))
(run 1)

(check (two-step 1 3))
",
    )?;
    Ok(())
}

/// A variable bound in only some branches may not be used in the actions:
/// distributing the body produces a rule where that variable is unbound.
#[test]
fn branch_local_var_in_action_rejected() {
    let mut egraph = EGraph::default();
    let err = egraph
        .parse_and_run_program(
            None,
            "
(relation edge (i64 i64))
(relation connected (i64 i64))
; `y` is bound only in the first branch, so the (edge x z) branch leaves it
; unbound in the action.
(rule ((OR ((edge x y)) ((edge x z))))
      ((connected x y)))
",
        )
        .expect_err("rule using a branch-local variable in its action should be rejected");
    let err = err.to_string();
    assert!(
        err.contains("Unbound") && err.contains('y'),
        "expected an unbound-variable error mentioning `y`, got: {err}"
    );
}

/// An empty `OR` (no branches) is a parse error.
#[test]
fn empty_or_rejected() {
    let mut egraph = EGraph::default();
    let err = egraph
        .parse_and_run_program(
            None,
            "
(relation r (i64))
(rule ((OR)) ((r 1)))
",
        )
        .expect_err("an OR with no branches should be rejected");
    assert!(
        err.to_string().contains("OR requires at least one branch"),
        "got: {err}"
    );
}
