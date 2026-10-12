use egglog::ast::*;
use egglog::macros::*;
use egglog::*;
use std::sync::{Arc, Mutex};

fn relay(input: &Syntax, cx: &mut MacroContext<'_>) -> Result<Expansion, ParseError> {
    let (_, args, span) = input.expect_call("relay!")?;
    let [arg] = args else {
        return Err(ParseError(span, "expected one operand".into()));
    };
    Ok(Expansion::Deferred(Deferred {
        operands: vec![cx.parser().parse_expr(arg)?],
        constraints: vec![SortConstraint::Same(0, 1)],
        finish: Arc::new(|_, args, _| Ok(Completion::Expr(args[0].clone()))),
    }))
}

fn fresh(input: &Syntax, _: &mut MacroContext<'_>) -> Result<Expansion, ParseError> {
    let span = input.span();
    Ok(Expansion::Deferred(Deferred {
        operands: vec![],
        constraints: vec![SortConstraint::EqSort(0)],
        finish: Arc::new(move |cx, _, sort| {
            let name = cx.fresh("fresh");
            cx.declare(Command::Constructor {
                span: span.clone(),
                name: name.clone(),
                schema: Schema {
                    input: cx
                        .query_bindings
                        .iter()
                        .map(|v| v.sort.name().to_owned())
                        .collect(),
                    output: sort.name().to_owned(),
                },
                cost: Some(1),
                unextractable: false,
                hidden: true,
                let_binding: false,
                term_constructor: None,
            })?;
            let args = cx
                .query_bindings
                .iter()
                .map(|v| ResolvedExpr::Var(span.clone(), v.clone()))
                .collect();
            Ok(Completion::Expr(cx.call(&name, args)?))
        }),
    }))
}

fn graph() -> EGraph {
    let mut eg = EGraph::default();
    eg.parser
        .macros()
        .register(Space::Expr, "relay!", Arc::new(relay));
    eg.parser
        .macros()
        .register(Space::Expr, "fresh!", Arc::new(fresh));
    eg
}

#[test]
fn later_head_use_and_nested_macros_share_inference() {
    let mut eg = graph();
    eg.parse_and_run_program(
        None,
        "
        (datatype A (A0)) (datatype B (B0))
        (relation Seen (A))
        (rule () ((let x (relay! (fresh!))) (Seen x)))
        (run 1) (check (Seen x))
    ",
    )
    .unwrap();
    assert_eq!(eg.get_size("Seen"), 1);
}

#[test]
fn head_constraints_resolve_ambiguous_query_primitives() {
    let mut eg = graph();
    eg.parse_and_run_program(
        None,
        "
        (sort Ints (Vec i64)) (sort Floats (Vec f64))
        (relation Seen (Ints))
        (rule ((= xs (vec-empty))) ((Seen (relay! xs))))
        (run 1) (check (Seen (vec-empty)))
    ",
    )
    .unwrap();
}

#[test]
fn ambiguity_and_query_deferred_calls_report_errors() {
    let mut eg = graph();
    eg.parse_and_run_program(None, "(datatype A (A0)) (datatype B (B0))")
        .unwrap();
    let error = eg
        .parse_and_run_program(None, "(rule () ((fresh!)))")
        .unwrap_err()
        .to_string();
    assert!(error.contains("sort annotation"), "{error}");
    let error = eg
        .parse_and_run_program(None, "(rule ((= x (fresh!))) ((union x (A0))))")
        .unwrap_err()
        .to_string();
    assert!(error.contains("rule queries"), "{error}");
}

#[test]
fn generated_siblings_observe_prior_declarations() {
    let mut eg = EGraph::default();
    eg.parser.macros().register(
        Space::Command,
        "declare-and-use",
        Arc::new(|_: &Syntax, _: &mut MacroContext<'_>| {
            Ok(Expansion::Sequence(Parser::read_syntax(
                None,
                "(datatype A (A0)) (inspect-A)",
            )?))
        }),
    );
    let seen = Arc::new(Mutex::new(false));
    let output = seen.clone();
    eg.parser.macros().register(
        Space::Command,
        "inspect-A",
        Arc::new(move |_: &Syntax, cx: &mut MacroContext<'_>| {
            *output.lock().unwrap() = cx.types()?.get_func_type("A0").is_some();
            Ok(Fragment::Commands(vec![]).into())
        }),
    );
    eg.resolve_program(None, "(declare-and-use)").unwrap();
    assert!(*seen.lock().unwrap());
}

#[test]
fn datatype_headers_precede_constructor_expansion() {
    let mut eg = EGraph::default();
    let seen = Arc::new(Mutex::new(Vec::new()));
    let output = seen.clone();
    let core = MacroBinding::core(Space::Command);
    eg.parser.macros().register(
        Space::Command,
        "constructor",
        Arc::new(move |input: &Syntax, cx: &mut MacroContext<'_>| {
            assert!(cx.types()?.get_sort_by_name("Tree").is_some());
            assert!(cx.types()?.get_sort_by_name("Trees").is_some());
            output
                .lock()
                .unwrap()
                .push(input.expect_call("constructor")?.1[0].expect_atom("name")?);
            core.apply(input, cx)
        }),
    );
    eg.parse_and_run_program(
        None,
        "(datatype* (Tree (Leaf i64) (Many Trees)) (sort Trees (Vec Tree))) (Leaf 1)",
    )
    .unwrap();
    assert_eq!(*seen.lock().unwrap(), vec!["Leaf", "Many"]);
}

#[test]
fn captured_bindings_and_parsed_fragments_bypass_shadowing() {
    let mut eg = EGraph::default();
    let core = MacroBinding::core(Space::Command);
    eg.parser.macros().register(
        Space::Command,
        "alias-sort",
        Arc::new(move |input: &Syntax, _: &mut MacroContext<'_>| {
            let (_, args, span) = input.expect_call("alias-sort")?;
            let mut call = vec![Syntax::Atom("sort".into(), span.clone())];
            call.extend_from_slice(args);
            Ok(Expansion::Syntax(core.bind(Syntax::List(call, span))))
        }),
    );
    eg.parser.macros().register(
        Space::Command,
        "sort",
        Arc::new(|_: &Syntax, _: &mut MacroContext<'_>| {
            panic!("a captured core binding must bypass this shadow")
        }),
    );
    eg.parse_and_run_program(None, "(alias-sort A)").unwrap();
    assert!(eg.get_sort_by_name("A").is_some());
}

#[test]
fn facts_and_schedules_have_the_same_transformer_api() {
    let mut eg = EGraph::default();
    eg.parser.macros().register(
        Space::Fact,
        "same",
        Arc::new(|input: &Syntax, cx: &mut MacroContext<'_>| {
            let (_, args, span) = input.expect_call("same")?;
            Ok(Fragment::Fact(Fact::Eq(
                span,
                cx.parser().parse_expr(&args[0])?,
                cx.parser().parse_expr(&args[1])?,
            ))
            .into())
        }),
    );
    eg.parser.macros().register(
        Space::Schedule,
        "once",
        Arc::new(|input: &Syntax, _: &mut MacroContext<'_>| {
            Ok(Fragment::Schedule(Schedule::Run(
                input.span(),
                RunConfig {
                    ruleset: "".into(),
                    until: None,
                },
            ))
            .into())
        }),
    );
    eg.parse_and_run_program(
        None,
        "(relation R (i64)) (rule ((same x 1)) ((R x))) (run-schedule (once)) (check (R 1))",
    )
    .unwrap();
}

#[test]
fn standalone_types_install_inference_without_a_backend() {
    let mut types = TypeInfo::default();
    let mut parser = Parser::default();
    let commands = parser
        .get_program_from_string(None, "(datatype A (A0))")
        .unwrap();
    // A frontend can check desugared declarations using only TypeInfo and a name supply.
    types.declare_sort("A", &None, egglog::span!()).unwrap();
    let expr = parser.get_expr_from_string(None, "(+ 1 2)").unwrap();
    let result = types
        .typecheck_expr_with_bindings_and_output(
            &mut parser.symbol_gen,
            &expr,
            &[],
            types.get_sort_by_name("i64").unwrap().clone(),
            Context::Pure,
        )
        .unwrap();
    assert_eq!(result.to_string(), "(+ 1 2)");
    assert_eq!(commands.len(), 1);
}

#[test]
fn deferred_expansion_is_deterministic_and_resolve_only() {
    let source = "(datatype A (A0)) (relation Seen (A)) (rule () ((Seen (fresh!))))";
    let resolve = || {
        graph()
            .resolve_program(None, source)
            .unwrap()
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
    };
    let first = resolve();
    assert_eq!(first, resolve());
    assert!(!first.join("\n").contains("deferred_"));
    let mut replay = EGraph::default();
    replay.parser.ensure_no_reserved_symbols = false;
    replay
        .parse_and_run_program(None, &first.join("\n"))
        .unwrap();
    replay
        .parse_and_run_program(None, "(run 1) (check (Seen x))")
        .unwrap();
}

#[test]
fn expansion_recursion_is_bounded() {
    let mut eg = EGraph::default();
    eg.parser.macros().register(
        Space::Command,
        "loop",
        Arc::new(|input: &Syntax, _: &mut MacroContext<'_>| Ok(Expansion::Syntax(input.clone()))),
    );
    let error = eg.resolve_program(None, "(loop)").unwrap_err().to_string();
    assert!(error.contains("exceeded 256"), "{error}");
}

#[test]
fn parse_then_run_keeps_the_declaration_environment_in_order() {
    let mut eg = graph();
    let program = eg.parse_program(None, "(datatype A (A0)) (relation Seen (A)) (rule () ((Seen (fresh!)))) (run 1) (check (Seen a))").unwrap();
    assert!(matches!(&program[0], Command::Unexpanded(_)));
    let mut other = graph();
    other.run_program(program.clone()).unwrap();
    eg.run_program(program).unwrap();
}

#[test]
fn deferred_rules_work_with_proof_instrumentation() {
    let mut eg = EGraph::new_with_proofs();
    eg.parser
        .macros()
        .register(Space::Expr, "fresh!", Arc::new(fresh));
    eg.parse_and_run_program(None, "(datatype A (A0)) (relation Input (i64)) (relation Seen (A)) (Input 1) (rule ((Input x)) ((Seen (fresh!)))) (run 1) (check (Seen a))").unwrap();
}

#[test]
fn generated_syntax_identifiers_do_not_capture_source_names() {
    let mut eg = graph();
    eg.parser.macros().register(
        Space::Action,
        "with-temp",
        Arc::new(|input: &Syntax, cx: &mut MacroContext<'_>| {
            let (_, args, span) = input.expect_call("with-temp")?;
            let temp = cx.fresh_syntax("temp", span.clone());
            Ok(Expansion::Sequence(vec![
                Syntax::List(
                    vec![
                        Syntax::Atom("let".into(), span.clone()),
                        temp.clone(),
                        args[0].clone(),
                    ],
                    span.clone(),
                ),
                Syntax::List(vec![Syntax::Atom("Seen".into(), span.clone()), temp], span),
            ]))
        }),
    );
    eg.parse_and_run_program(None, "(relation Input (i64)) (relation Seen (i64)) (Input 7) (rule ((Input temp)) ((with-temp 3) (Seen temp))) (run 1) (check (Seen 3) (Seen 7))").unwrap();
}

#[test]
fn explicit_record_view_can_generate_a_type_before_its_consumers() {
    let mut eg = graph();
    eg.parser.macros().register(
        Space::Command,
        "derive-record-view",
        Arc::new(|input: &Syntax, cx: &mut MacroContext<'_>| {
            let (_, args, span) = input.expect_call("derive-record-view")?;
            let sort = args[0].expect_atom("record sort")?;
            let constructors = cx
                .types()?
                .get_func_types()
                .into_iter()
                .filter(|function| {
                    function.subtype == FunctionSubtype::Constructor
                        && function.output.name() == sort
                })
                .collect::<Vec<_>>();
            let [constructor] = constructors.as_slice() else {
                return Err(ParseError(
                    span,
                    "expected a record with one constructor".into(),
                ));
            };
            Ok(Fragment::Commands(vec![Command::Datatype {
                span: span.clone(),
                name: format!("{sort}View"),
                variants: vec![Variant {
                    span,
                    name: format!("View{sort}"),
                    types: constructor
                        .input
                        .iter()
                        .map(|sort| sort.name().to_owned())
                        .collect(),
                    cost: None,
                    unextractable: false,
                }],
            }])
            .into())
        }),
    );
    eg.parse_and_run_program(None, "(datatype Packet (PacketValue i64 String)) (derive-record-view Packet) (relation Seen (PacketView)) (PacketValue 7 \"hello\") (rule ((= packet (PacketValue n text))) ((Seen (ViewPacket n text)))) (run 1) (check (Seen (ViewPacket 7 \"hello\")))").unwrap();
}
