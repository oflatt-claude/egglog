use egglog::macros::*;
use egglog::*;
use std::sync::{Arc, Mutex};

#[test]
fn proof_mode_macros_see_source_function_arities() {
    let seen = Arc::new(Mutex::new(vec![]));
    let mut egraph = EGraph::new_with_proofs();
    let output = seen.clone();
    let core = MacroBinding::core(Space::Command);
    egraph.parser.macros().register(
        Space::Command,
        "let",
        Arc::new(move |input: &Syntax, cx: &mut MacroContext<'_>| {
            output
                .lock()
                .unwrap()
                .push(cx.types()?.get_func_type("score").unwrap().input.len());
            core.apply(input, cx)
        }),
    );
    egraph
        .parse_and_run_program(
            None,
            "(datatype Math (Num i64)) (function score (Math) i64 :merge old) (let $x (Num 1))",
        )
        .unwrap();
    assert_eq!(*seen.lock().unwrap(), vec![1]);
}
