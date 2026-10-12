//! Expansion driver and builtin delegation.
use super::*;

impl Parser {
    pub fn macros(&mut self) -> &mut MacroRegistry {
        &mut self.macros
    }

    /// Read structured syntax without invoking any transformer.
    pub fn read_syntax(filename: Option<String>, source: &str) -> Result<Vec<Syntax>, ParseError> {
        all_sexps(SexpParser::new(filename, source))
    }

    pub fn expand(&mut self, space: Space, input: &Syntax) -> Result<Expansion, ParseError> {
        if self.expansion_depth >= 256 {
            return Err(ParseError(
                input.span(),
                "macro expansion exceeded 256 nested steps".into(),
            ));
        }
        self.expansion_depth += 1;
        let result = (|| {
            match input {
                Syntax::Bound(binding, inner) => {
                    if binding.space != space {
                        return Err(ParseError(
                            input.span(),
                            "macro binding used in the wrong space".into(),
                        ));
                    }
                    binding.apply(
                        inner,
                        &mut MacroContext {
                            parser: self,
                            span: input.span(),
                        },
                    )
                }
                Syntax::Parsed(fragment, _) => Ok(Expansion::Parsed((**fragment).clone())),
                _ => {
                    // Expressions can also have atom transformers. Lists use the head binding.
                    let binding = if let Syntax::Atom(name, _) | Syntax::Generated(name, _) = input
                    {
                        self.macros.lookup(space, name)
                    } else if let Ok((name, _, _)) = input.expect_call("macro call") {
                        self.macros.lookup(space, &name)
                    } else {
                        MacroBinding::core(space)
                    };
                    binding.apply(
                        input,
                        &mut MacroContext {
                            parser: self,
                            span: input.span(),
                        },
                    )
                }
            }
        })();
        self.expansion_depth -= 1;
        result
    }

    pub(crate) fn parse_core(
        &mut self,
        space: Space,
        input: &Syntax,
    ) -> Result<Fragment, ParseError> {
        Ok(match space {
            Space::Command => Fragment::Commands(self.parse_core_command(input)?),
            Space::Action => Fragment::Actions(self.parse_core_action(input)?),
            Space::Expr => Fragment::Expr(self.parse_core_expr(input)?),
            Space::Fact => Fragment::Fact(self.parse_core_fact(input)?),
            Space::Schedule => Fragment::Schedule(self.parse_core_schedule(input)?),
        })
    }

    fn finish_parse(
        &mut self,
        space: Space,
        input: &Syntax,
        fuel: usize,
    ) -> Result<Fragment, ParseError> {
        if fuel == 0 {
            return Err(ParseError(
                input.span(),
                "macro expansion exceeded 256 steps".into(),
            ));
        }
        match self.expand(space, input)? {
            Expansion::Parsed(fragment) => Ok(fragment),
            Expansion::Syntax(syntax) => self.finish_parse(space, &syntax, fuel - 1),
            Expansion::Sequence(forms) => match space {
                Space::Command => {
                    let mut commands = Vec::new();
                    for form in forms {
                        match self.finish_parse(space, &form, fuel - 1)? {
                            Fragment::Commands(cs) => commands.extend(cs),
                            _ => return self.wrong_space(input),
                        }
                    }
                    Ok(Fragment::Commands(commands))
                }
                Space::Action => {
                    let mut actions = Vec::new();
                    for form in forms {
                        match self.finish_parse(space, &form, fuel - 1)? {
                            Fragment::Actions(xs) => actions.extend(xs),
                            _ => return self.wrong_space(input),
                        }
                    }
                    Ok(Fragment::Actions(actions))
                }
                _ => self.wrong_space(input),
            },
            Expansion::Deferred(deferred) => {
                if !matches!(space, Space::Expr | Space::Action) {
                    return Err(ParseError(
                        input.span(),
                        "deferred expansion is supported only in expression and action spaces"
                            .into(),
                    ));
                }
                let slots = deferred.operands.len() + 1;
                for constraint in &deferred.constraints {
                    let valid = match constraint {
                        SortConstraint::Same(a, b) => *a < slots && *b < slots,
                        SortConstraint::Is(a, _) | SortConstraint::EqSort(a) => *a < slots,
                    };
                    if !valid {
                        return Err(ParseError(
                            input.span(),
                            "deferred macro refers to a nonexistent type slot".into(),
                        ));
                    }
                }
                let hint = input
                    .expect_call("macro")
                    .map(|(name, _, _)| name)
                    .unwrap_or_else(|_| "expression".into());
                let name = self.symbol_gen.fresh(&format!("deferred_{hint}"));
                let expr = Expr::Call(input.span(), name.clone(), deferred.operands.clone());
                self.deferred.insert(
                    name.clone(),
                    DeferredCall {
                        name,
                        span: input.span(),
                        space,
                        deferred,
                    },
                );
                Ok(if space == Space::Expr {
                    Fragment::Expr(expr)
                } else {
                    Fragment::Actions(vec![Action::Expr(input.span(), expr)])
                })
            }
        }
    }

    fn wrong_space<T>(&self, input: &Syntax) -> Result<T, ParseError> {
        Err(ParseError(
            input.span(),
            "macro returned a fragment in the wrong space".into(),
        ))
    }

    pub fn parse_command(&mut self, input: &Syntax) -> Result<Vec<Command>, ParseError> {
        match self.finish_parse(Space::Command, input, 256)? {
            Fragment::Commands(cs) => Ok(cs),
            _ => self.wrong_space(input),
        }
    }
    pub fn parse_action(&mut self, input: &Syntax) -> Result<Vec<Action>, ParseError> {
        match self.finish_parse(Space::Action, input, 256)? {
            Fragment::Actions(xs) => Ok(xs),
            _ => self.wrong_space(input),
        }
    }
    pub fn parse_expr(&mut self, input: &Syntax) -> Result<Expr, ParseError> {
        match self.finish_parse(Space::Expr, input, 256)? {
            Fragment::Expr(e) => Ok(e),
            _ => self.wrong_space(input),
        }
    }
    pub fn parse_fact(&mut self, input: &Syntax) -> Result<Fact, ParseError> {
        match self.finish_parse(Space::Fact, input, 256)? {
            Fragment::Fact(f) => Ok(f),
            _ => self.wrong_space(input),
        }
    }
    pub fn parse_schedule(&mut self, input: &Syntax) -> Result<Schedule, ParseError> {
        match self.finish_parse(Space::Schedule, input, 256)? {
            Fragment::Schedule(s) => Ok(s),
            _ => self.wrong_space(input),
        }
    }
}

impl Parser {
    // Discover nominal headers first, then parameterized sorts, then variants.
    // All variants explicitly delegate to the constructor binding captured here.
    pub(super) fn expand_datatype(&mut self, input: &Syntax) -> Result<Expansion, ParseError> {
        let (head, args, span) = input.expect_call("datatype declaration")?;
        let datatypes = if head == "datatype" {
            if args.is_empty() {
                return Err(ParseError(span, "datatype requires a name".into()));
            }
            vec![Syntax::List(args.to_vec(), span.clone())]
        } else {
            args.to_vec()
        };
        let constructor = self.macros.lookup(Space::Command, "constructor");
        let core = MacroBinding::core(Space::Command);
        let mut headers = Vec::new();
        let mut containers = Vec::new();
        let mut variants = Vec::new();
        for datatype in datatypes {
            let (name, forms, dspan) = datatype.expect_call("datatype or parameterized sort")?;
            if name == "sort" {
                containers.push(core.bind(datatype));
                continue;
            }
            headers.push(core.bind(Syntax::List(
                vec![
                    Syntax::Atom("sort".into(), dspan.clone()),
                    Syntax::Atom(name.clone(), dspan.clone()),
                ],
                dspan.clone(),
            )));
            for variant in forms {
                let (ctor, fields, vspan) = variant.expect_call("datatype variant")?;
                let options = fields
                    .iter()
                    .position(
                        |field| matches!(field, Syntax::Atom(name, _) if name.starts_with(':')),
                    )
                    .unwrap_or(fields.len());
                let mut call = vec![
                    Syntax::Atom("constructor".into(), vspan.clone()),
                    Syntax::Atom(ctor, vspan.clone()),
                    Syntax::List(fields[..options].to_vec(), vspan.clone()),
                    Syntax::Atom(name.clone(), dspan.clone()),
                ];
                call.extend_from_slice(&fields[options..]);
                variants.push(constructor.bind(Syntax::List(call, vspan)));
            }
        }
        headers.extend(containers);
        headers.extend(variants);
        Ok(Expansion::Sequence(headers))
    }
}

impl Parser {
    pub(crate) fn with_core<T>(&mut self, f: impl FnOnce(&mut Parser) -> T) -> T {
        let mut core = Parser::default();
        core.symbol_gen = self.symbol_gen.clone();
        core.ensure_no_reserved_symbols = false;
        let result = f(&mut core);
        self.symbol_gen = core.symbol_gen;
        result
    }
}

impl Expansion {
    pub fn map_commands(
        self,
        cx: &mut MacroContext<'_>,
        span: Span,
        mapper: Arc<CommandMapper>,
    ) -> Result<Self, ParseError> {
        let wrap = |syntax| {
            MacroBinding::new(
                Space::Command,
                Arc::new(MapCommands {
                    mapper: mapper.clone(),
                }),
            )
            .bind(syntax)
        };
        Ok(match self {
            Self::Syntax(syntax) => Self::Syntax(wrap(syntax)),
            Self::Sequence(forms) => Self::Sequence(forms.into_iter().map(wrap).collect()),
            Self::Parsed(Fragment::Commands(commands)) => {
                let mut result = Vec::new();
                for command in commands {
                    result.extend(mapper(command, cx)?);
                }
                Self::Parsed(Fragment::Commands(result))
            }
            _ => return Err(ParseError(span, "expected a command expansion".into())),
        })
    }
}
struct MapCommands {
    mapper: Arc<CommandMapper>,
}
impl Macro for MapCommands {
    fn expand(&self, input: &Syntax, cx: &mut MacroContext<'_>) -> Result<Expansion, ParseError> {
        cx.expand(Space::Command, input)?
            .map_commands(cx, input.span(), self.mapper.clone())
    }
}
