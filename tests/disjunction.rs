//! Behavioral tests for disjunction (`or`) in rule bodies.
//!
//! A body `C ∧ (D₁ ∨ … ∨ Dₙ)` matches when `C` holds and at least one branch
//! `Dᵢ` holds. Only the variables common to every branch (plus variables bound
//! by the surrounding conjunction) are visible outside the `or`. Branch-local
//! variables that escape their `or`, and empty branches, are type errors.
//!
//! Each test runs rules to a fixpoint and asserts on the resulting database via
//! `check` / `fail`.

use egglog::{EGraph, Error};

/// Runs a program, returning any error.
fn run(program: &str) -> Result<(), Error> {
    let mut egraph = EGraph::default();
    egraph.parse_and_run_program(None, program)?;
    Ok(())
}

/// A two-branch `or` over relations behaves as set union.
#[test]
fn or_basic_union() -> Result<(), Error> {
    run("
(relation A (i64))
(relation B (i64))
(relation R (i64))
(A 1) (A 2)
(B 2) (B 3)
(rule ((or ((A x)) ((B x)))) ((R x)))
(run 5)
(check (R 1))
(check (R 2))
(check (R 3))
(fail (check (R 4)))
")
}

/// An `or` conjoined with a surrounding fact `C` matches only when `C` holds and
/// at least one branch holds.
#[test]
fn or_with_conjunction() -> Result<(), Error> {
    run("
(relation C (i64))
(relation A (i64))
(relation B (i64))
(relation R (i64))
(C 1) (C 2) (C 3)
(A 1) (A 2)
(B 2) (B 3)
(rule ((C x) (or ((A x)) ((B x)))) ((R x)))
(run 5)
(check (R 1))
(check (R 2))
(check (R 3))
(fail (check (R 4)))
")
}

/// A `C` value that satisfies neither branch does not fire.
#[test]
fn or_conjunction_requires_a_branch() -> Result<(), Error> {
    run("
(relation C (i64))
(relation A (i64))
(relation R (i64))
(C 5)
(rule ((C x) (or ((A x)) ((A x)))) ((R x)))
(run 5)
(fail (check (R 5)))
")
}

/// A variable common to every branch may be used in the action; a branch-local
/// variable (`y`) stays inside its branch.
#[test]
fn or_common_variable() -> Result<(), Error> {
    run("
(relation P (i64 i64))
(relation Q (i64 i64))
(relation Out (i64))
(P 1 10)
(Q 1 20)
(P 2 30)
(rule ((or ((P x y)) ((Q x y)))) ((Out x)))
(run 5)
(check (Out 1))
(check (Out 2))
(fail (check (Out 3)))
")
}

/// Three-branch `or`.
#[test]
fn or_three_branches() -> Result<(), Error> {
    run("
(relation A (i64))
(relation B (i64))
(relation C (i64))
(relation R (i64))
(A 1) (B 2) (C 3)
(rule ((or ((A x)) ((B x)) ((C x)))) ((R x)))
(run 5)
(check (R 1))
(check (R 2))
(check (R 3))
(fail (check (R 4)))
")
}

/// A branch may itself be a conjunction of several facts.
#[test]
fn or_branch_is_a_conjunction() -> Result<(), Error> {
    run("
(relation A (i64))
(relation B (i64))
(relation C (i64))
(relation R (i64))
(A 1) (B 1)
(A 2)
(C 3)
(rule ((or ((A x) (B x)) ((C x)))) ((R x)))
(run 5)
(check (R 1))
(fail (check (R 2)))
(check (R 3))
")
}

/// Two `or`s in one body distribute as a cartesian product of branch choices.
#[test]
fn or_two_disjunctions() -> Result<(), Error> {
    run("
(relation A (i64))
(relation B (i64))
(relation C (i64))
(relation D (i64))
(relation R (i64))
(A 1) (C 1)
(B 2) (D 2)
(A 3) (D 3)
(rule ((or ((A x)) ((B x))) (or ((C x)) ((D x)))) ((R x)))
(run 5)
(check (R 1))
(check (R 2))
(check (R 3))
(fail (check (R 4)))
")
}

/// A branch may join several atoms internally on a branch-local variable, with
/// only the common variable escaping.
#[test]
fn or_branch_internal_join() -> Result<(), Error> {
    run("
(relation A (i64 i64))
(relation B (i64 i64))
(relation C (i64 i64))
(relation Res (i64))
(A 1 9) (B 9 1)
(C 2 2)
(rule ((or ((A x t) (B t x)) ((C x x)))) ((Res x)))
(run 3)
(check (Res 1))
(check (Res 2))
(fail (check (Res 9)))
")
}

/// An `or` nested inside a branch of another `or` flattens correctly.
#[test]
fn or_nested() -> Result<(), Error> {
    run("
(relation A (i64))
(relation B (i64))
(relation C (i64))
(relation R (i64))
(A 1) (B 2) (C 3)
(rule ((or ((A x)) ((or ((B x)) ((C x)))))) ((R x)))
(run 5)
(check (R 1))
(check (R 2))
(check (R 3))
(fail (check (R 4)))
")
}

/// `or` works with an equality (`union`) action over an eq-sort.
#[test]
fn or_with_union_action() -> Result<(), Error> {
    run("
(datatype Math (Num i64))
(relation A (Math))
(relation B (Math))
(A (Num 1))
(B (Num 2))
(rule ((or ((A x)) ((B x)))) ((union x (Num 0))))
(run 5)
(check (= (Num 0) (Num 1)))
(check (= (Num 0) (Num 2)))
")
}

/// A branch-local variable used outside its `or` is a type error.
#[test]
fn or_branch_local_escapes_errors() {
    let err = run("
(relation P (i64 i64))
(relation Q (i64 i64))
(relation Out (i64))
(rule ((or ((P x y)) ((Q x z)))) ((Out y)))
")
    .unwrap_err()
    .to_string();
    assert!(
        err.contains("local to one branch") && err.contains('y'),
        "unexpected error: {err}"
    );
}

/// An empty `or` branch is a type error.
#[test]
fn or_empty_branch_errors() {
    let err = run("
(relation A (i64))
(relation R (i64))
(rule ((or ((A x)) ())) ((R x)))
")
    .unwrap_err()
    .to_string();
    assert!(err.contains("empty"), "unexpected error: {err}");
}

/// `or` is rejected in query-shaped commands like `check`.
#[test]
fn or_outside_rule_errors() {
    let err = run("
(relation A (i64))
(relation B (i64))
(A 1)
(check (or ((A 1)) ((B 1))))
")
    .unwrap_err()
    .to_string();
    assert!(
        err.contains("only supported inside rule bodies"),
        "unexpected error: {err}"
    );
}

/// `or` works in a `rewrite`'s `:when` condition (which desugars to a rule).
#[test]
fn or_in_rewrite_condition() -> Result<(), Error> {
    run("
(datatype Math (Num i64) (Add Math Math))
(relation Good (Math))
(relation Alt (Math))
(Good (Num 1))
(rewrite (Add x y) (Add y x) :when ((or ((Good x)) ((Alt x)))))
(Add (Num 1) (Num 2))
(run 3)
(check (= (Add (Num 1) (Num 2)) (Add (Num 2) (Num 1))))
")
}

/// A *correlated* `or` whose branches each equate an outer column with a
/// variable bound elsewhere in the surrounding conjunction — the e-graph
/// rebuild pattern. Every branch references the outer-bound `a`/`b`/`c` (from
/// `v`) and `d` (from the seminaive delta atom `u`); a `(!= d e)` primitive
/// sits in the conjunction beside the `or`. The action reads another table
/// (`f`) by function lookup. Under `:unsafe-seminaive` this must fire exactly
/// for `v`-rows that mention a `u`-key in some column (with `d != e`).
#[test]
fn or_correlated_seminaive_rebuild() -> Result<(), Error> {
    run("
(relation v (i64 i64 i64))
(relation u (i64 i64))
(function f (i64) i64 :merge (max old new))
(relation hit (i64 i64 i64))

(set (f 1) 10) (set (f 2) 20) (set (f 3) 30)
(set (f 4) 40) (set (f 5) 50) (set (f 6) 60)
(set (f 7) 70) (set (f 9) 90)

(v 1 2 3)
(v 4 5 6)
(v 7 7 9)

(u 2 8)   ; d=2, e=8: hits (v 1 2 3) via column b
(u 9 8)   ; d=9, e=8: hits (v 7 7 9) via column c
(u 5 5)   ; d=e=5: filtered out by (!= d e), so (v 4 5 6) is not hit

(ruleset rr)
(rule ((v a b c) (u d e) (!= d e) (OR (= a d) (= b d) (= c d)))
      ((hit (f a) (f b) (f c)))
      :ruleset rr :unsafe-seminaive)
(run rr 10)

(check (hit 10 20 30))
(check (hit 70 70 90))
(fail (check (hit 40 50 60)))
")
}

/// The same correlated pattern in plain (naive) mode also compiles by splitting
/// and produces the correct fixpoint.
#[test]
fn or_correlated_naive() -> Result<(), Error> {
    run("
(relation v (i64 i64 i64))
(relation u (i64 i64))
(relation hit (i64 i64 i64))
(v 1 2 3)
(v 4 5 6)
(u 2 8)
(rule ((v a b c) (u d e) (OR (= a d) (= b d) (= c d)))
      ((hit a b c)))
(run 5)
(check (hit 1 2 3))
(fail (check (hit 4 5 6)))
")
}
