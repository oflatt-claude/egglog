//! Structured, space-specific macro expansion.
//!
//! A transformer can return ordinary syntax or defer an expression/action until
//! the enclosing rule's body and head have been inferred together. See
//! `docs/macros.md` for the author-facing API and worked examples.

use crate::ast::*;
use crate::*;

/// The grammar in which a transformer is invoked.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Space {
    Command,
    Action,
    Expr,
    Fact,
    Schedule,
}

/// Cloneable syntax retains its source locations and embedded parsed fragments.
pub type Syntax = Sexp;

/// One transformer interface for both syntactic and type-directed expansion.
pub trait Macro: Send + Sync {
    fn expand(&self, input: &Syntax, cx: &mut MacroContext<'_>) -> Result<Expansion, ParseError>;
}

impl<F> Macro for F
where
    F: Fn(&Syntax, &mut MacroContext<'_>) -> Result<Expansion, ParseError> + Send + Sync,
{
    fn expand(&self, input: &Syntax, cx: &mut MacroContext<'_>) -> Result<Expansion, ParseError> {
        self(input, cx)
    }
}

/// A binding captured before shadowing continues to refer to the same transformer.
#[derive(Clone)]
pub struct MacroBinding {
    space: Space,
    transformer: Option<Arc<dyn Macro>>,
}

impl Debug for MacroBinding {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("MacroBinding").field(&self.space).finish()
    }
}

impl MacroBinding {
    /// Create a binding for generated syntax without installing a global name.
    pub fn new(space: Space, transformer: Arc<dyn Macro>) -> Self {
        Self {
            space,
            transformer: Some(transformer),
        }
    }

    /// The core parser in this space, bypassing a shadowing transformer at the root.
    /// Children are still expanded using their own bindings.
    pub fn core(space: Space) -> Self {
        Self {
            space,
            transformer: None,
        }
    }

    pub fn apply(
        &self,
        input: &Syntax,
        cx: &mut MacroContext<'_>,
    ) -> Result<Expansion, ParseError> {
        match &self.transformer {
            Some(transformer) => transformer.expand(input, cx),
            None => {
                if self.space == Space::Command
                    && cx.parser.macros.contains(Space::Command, "constructor")
                    && let Ok((name, _, _)) = input.expect_call("command")
                    && matches!(name.as_str(), "datatype" | "datatype*")
                {
                    return cx.parser.expand_datatype(input);
                }
                cx.parser
                    .parse_core(self.space, input)
                    .map(Expansion::Parsed)
            }
        }
    }

    /// Bind this particular occurrence, without relying on its printed name.
    pub fn bind(&self, input: Syntax) -> Syntax {
        Syntax::Bound(self.clone(), Box::new(input))
    }
}

#[derive(Clone, Default)]
pub struct MacroRegistry {
    bindings: HashMap<(Space, String), MacroBinding>,
}

impl MacroRegistry {
    pub fn is_empty(&self) -> bool {
        self.bindings.is_empty()
    }
    pub fn register(&mut self, space: Space, name: impl Into<String>, transformer: Arc<dyn Macro>) {
        self.bindings.insert(
            (space, name.into()),
            MacroBinding {
                space,
                transformer: Some(transformer),
            },
        );
    }
    /// Capture an installed binding, or the core parser when none shadows it.
    pub fn lookup(&self, space: Space, name: &str) -> MacroBinding {
        self.bindings
            .get(&(space, name.to_owned()))
            .cloned()
            .unwrap_or_else(|| MacroBinding::core(space))
    }
    pub(crate) fn contains(&self, space: Space, name: &str) -> bool {
        self.bindings.contains_key(&(space, name.to_owned()))
    }
}

pub struct MacroContext<'a> {
    pub(crate) parser: &'a mut Parser,
    span: Span,
}

impl MacroContext<'_> {
    pub fn parser(&mut self) -> &mut Parser {
        self.parser
    }
    /// Declarations established by preceding commands. Available when expansion
    /// is driven by an EGraph; parsing syntax alone does not create declarations.
    pub fn types(&self) -> Result<&TypeInfo, ParseError> {
        self.parser.macro_types.as_ref().ok_or_else(|| ParseError(self.span.clone(), "this macro requires an expansion environment; use EGraph::resolve_program or parse_and_run_program".into()))
    }
    pub fn fresh(&mut self, hint: &str) -> String {
        self.parser.symbol_gen.fresh(hint)
    }
    /// A generated identifier can be embedded in syntax without disabling the
    /// parser's protection against reserved names in user input.
    pub fn fresh_syntax(&mut self, hint: &str, span: Span) -> Syntax {
        Syntax::Generated(self.fresh(hint), span)
    }
    pub fn binding(&self, space: Space, name: &str) -> MacroBinding {
        self.parser.macros.lookup(space, name)
    }
    /// Expand just the requested category. The parent chooses which children to
    /// inspect and when; uninspected syntax stays intact.
    pub fn expand(&mut self, space: Space, input: &Syntax) -> Result<Expansion, ParseError> {
        self.parser.expand(space, input)
    }
}

#[derive(Clone, Debug)]
pub enum Fragment {
    Commands(Vec<Command>),
    Actions(Vec<Action>),
    Expr(Expr),
    Fact(Fact),
    Schedule(Schedule),
}

impl Fragment {
    pub fn syntax(self, span: Span) -> Syntax {
        Syntax::Parsed(Arc::new(self), span)
    }
}

pub enum Expansion {
    Syntax(Syntax),
    /// Commands are expanded and installed in order, including generated siblings.
    Sequence(Vec<Syntax>),
    Parsed(Fragment),
    /// Supported in expressions and actions in rule heads and top-level actions.
    Deferred(Deferred),
}

impl From<Fragment> for Expansion {
    fn from(fragment: Fragment) -> Self {
        Self::Parsed(fragment)
    }
}

/// Type slots are operands followed by the expression's result. An action's
/// result is an internal Unit slot. Equality-sort requirements do not guess a
/// nominal sort: a use or explicit annotation must supply that information.
#[derive(Clone, Debug)]
pub enum SortConstraint {
    Same(usize, usize),
    Is(usize, ArcSort),
    EqSort(usize),
}

type Finish = dyn Fn(&mut FinishContext<'_>, &[ResolvedExpr], ArcSort) -> Result<Completion, Error>
    + Send
    + Sync;

#[derive(Clone)]
pub struct Deferred {
    pub operands: Vec<Expr>,
    pub constraints: Vec<SortConstraint>,
    pub finish: Arc<Finish>,
}

impl Debug for Deferred {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Deferred")
            .field("operands", &self.operands)
            .field("constraints", &self.constraints)
            .finish_non_exhaustive()
    }
}

pub enum Completion {
    Expr(ResolvedExpr),
    Actions(ResolvedActions),
}

/// Information available after the entire inference region has been solved.
/// Operand expressions are already expanded, including nested deferred calls.
/// Helper declarations are checked immediately and emitted before the consumer.
pub struct FinishContext<'a> {
    pub span: Span,
    pub query_bindings: &'a [ResolvedVar],
    pub context: Context,
    pub is_rule: bool,
    types: &'a mut TypeInfo,
    parser: &'a mut Parser,
    declarations: &'a mut Vec<ResolvedNCommand>,
}

impl FinishContext<'_> {
    pub fn types(&self) -> &TypeInfo {
        self.types
    }
    pub fn fresh(&mut self, hint: &str) -> String {
        self.parser.symbol_gen.fresh(hint)
    }

    pub fn declare(&mut self, declaration: Command) -> Result<(), Error> {
        if !matches!(
            declaration,
            Command::Sort { .. }
                | Command::Constructor { .. }
                | Command::Function { .. }
                | Command::Relation { .. }
        ) {
            return Err(ParseError(
                self.span.clone(),
                "deferred expansion may introduce only helper declarations".into(),
            )
            .into());
        }
        let commands = desugar_command(declaration, self.parser, false)?;
        self.declarations.extend(
            self.types
                .typecheck_program(&mut self.parser.symbol_gen, &commands)?,
        );
        Ok(())
    }

    /// Construct a resolved call to a declared table. Operands are reused as
    /// syntax, so an effectful operand is not evaluated during expansion.
    pub fn call(&self, name: &str, operands: Vec<ResolvedExpr>) -> Result<ResolvedExpr, Error> {
        let typ = self
            .types
            .get_func_type(name)
            .ok_or_else(|| TypeError::UnboundFunction(name.into(), self.span.clone()))?;
        if typ.input.len() != operands.len()
            || typ
                .input
                .iter()
                .zip(&operands)
                .any(|(sort, expr)| sort.name() != expr.output_type().name())
        {
            return Err(ParseError(
                self.span.clone(),
                format!("macro generated an invalid call to {name}"),
            )
            .into());
        }
        Ok(ResolvedExpr::Call(
            self.span.clone(),
            ResolvedCall::Func(typ.clone()),
            operands,
        ))
    }
}

/// A wrapper's transformation of parsed commands. Generated syntax is visited
/// lazily, so declaration-producing siblings establish their environments first.
pub type CommandMapper =
    dyn Fn(Command, &mut MacroContext<'_>) -> Result<Vec<Command>, ParseError> + Send + Sync;

mod deferred;
mod expand;
pub(crate) use deferred::{DeferredCall, check_deferred};
