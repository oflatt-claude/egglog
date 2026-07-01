//! Tests for `OR` disjunctions in rule bodies.
//!
//! `(OR (b1 ...) (b2 ...) ...)` inside a rule query matches when any branch
//! matches. Each branch is a conjunctive subquery. Only variables common to every
//! branch may be referenced outside the disjunction (the actions or the rest of the
//! body).
//!
//! These tests are implementation-independent: they run the rules to a fixpoint and
//! only assert on the resulting database, so they hold for any execution strategy.

use egglog::Error;
use egglog::prelude::*;

fn run(program: &str) -> Result<(), Error> {
    EGraph::default()
        .parse_and_run_program(None, program)
        .map(|_| ())
}

/// Both branches of an `OR` fire, so `connected` becomes the symmetric closure
/// of `edge`. The reverse direction is only derivable via the second branch.
#[test]
fn symmetric_closure_via_or() -> Result<(), Error> {
    run("
(relation edge (i64 i64))
(relation connected (i64 i64))
(edge 1 2)
(edge 3 2)

(rule ((OR ((edge x y)) ((edge y x))))
      ((connected x y)))
(run-schedule (saturate (run)))

(check (connected 1 2))
(check (connected 3 2))
(check (connected 2 1))
(check (connected 2 3))
; a pair that shares no edge in either direction must be absent
(fail (check (connected 1 3)))
")
}

/// Two `OR` groups in one body yield every combination of branch choices.
#[test]
fn two_or_groups() -> Result<(), Error> {
    run("
(relation p (i64))
(relation q (i64))
(relation r (i64))
(relation s (i64))
(relation out (i64 i64))
(p 1) (q 2) (r 3) (s 4)

(rule ((OR ((p a)) ((q a)))
       (OR ((r b)) ((s b))))
      ((out a b)))
(run-schedule (saturate (run)))

(check (out 1 3))
(check (out 1 4))
(check (out 2 3))
(check (out 2 4))
")
}

/// An `OR` nested inside a branch matches the flattened disjunction.
#[test]
fn nested_or() -> Result<(), Error> {
    run("
(relation a (i64))
(relation b (i64))
(relation c (i64))
(relation hit (i64))
(a 1) (b 2) (c 3)

; (a x) OR ((b x) OR (c x))  ==  (a x) OR (b x) OR (c x)
(rule ((OR ((a x))
           ((OR ((b x)) ((c x))))))
      ((hit x)))
(run-schedule (saturate (run)))

(check (hit 1))
(check (hit 2))
(check (hit 3))
")
}

/// A branch may contain several facts (a conjunctive subquery).
#[test]
fn multi_fact_branch() -> Result<(), Error> {
    run("
(relation edge (i64 i64))
(relation reach (i64 i64))
(edge 1 2)
(edge 2 3)

; reach x z  if  (edge x z)  OR  (edge x y AND edge y z)
(rule ((OR ((edge x z))
           ((edge x y) (edge y z))))
      ((reach x z)))
(run-schedule (saturate (run)))

(check (reach 1 2))
(check (reach 2 3))
(check (reach 1 3))
")
}

/// A common variable shared with the surrounding conjunction joins correctly.
#[test]
fn common_var_joins_outer_conjunction() -> Result<(), Error> {
    run("
(relation node (i64))
(relation edge (i64 i64))
(relation back (i64 i64))
(relation marked (i64 i64))
(node 1)
(edge 1 2)
(back 3 1)

; only x=1 is a node; y ranges over either an outgoing or incoming neighbor
(rule ((node x)
       (OR ((edge x y)) ((back y x))))
      ((marked x y)))
(run-schedule (saturate (run)))

(check (marked 1 2))
(check (marked 1 3))
")
}

/// A variable bound in only some branches may not be used in the actions.
#[test]
fn branch_local_var_in_action_rejected() {
    let err = run("
(relation edge (i64 i64))
(relation connected (i64 i64))
; `y` is bound only in the first branch.
(rule ((OR ((edge x y)) ((edge x z))))
      ((connected x y)))
")
    .expect_err("using a branch-local variable in the action should be rejected");
    assert!(
        err.to_string().contains("local to one branch"),
        "got: {err}"
    );
}

/// A branch-local variable may not be shared with the surrounding conjunction.
#[test]
fn branch_local_var_shared_with_outer_rejected() {
    let err = run("
(relation edge (i64 i64))
(relation node (i64))
(relation out (i64))
; `y` is bound only in the first branch but is also used by the outer `node`.
(rule ((node y)
       (OR ((edge x y)) ((edge x x))))
      ((out x)))
")
    .expect_err("a branch-local variable shared with the outer query should be rejected");
    assert!(
        err.to_string().contains("local to one branch"),
        "got: {err}"
    );
}

/// An empty `OR` (no branches) is a parse error.
#[test]
fn empty_or_rejected() {
    let err = run("
(relation r (i64))
(rule ((OR)) ((r 1)))
")
    .expect_err("an OR with no branches should be rejected");
    assert!(
        err.to_string().contains("OR requires at least one branch"),
        "got: {err}"
    );
}

/// An empty branch is rejected.
#[test]
fn empty_branch_rejected() {
    let err = run("
(relation p (i64))
(relation out (i64))
(rule ((p x) (OR () ((p x))))
      ((out x)))
")
    .expect_err("an empty OR branch should be rejected");
    assert!(err.to_string().contains("at least one fact"), "got: {err}");
}
