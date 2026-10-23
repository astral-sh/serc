//! Source validation runs before lowering can discard unreachable statements.

use std::borrow::Cow;
use std::cell::{Cell, RefCell};

use ruff_python_ast::visitor::{
    Visitor, walk_expr, walk_interpolated_string_element, walk_parameters, walk_pattern, walk_stmt,
};
use ruff_python_ast::{self as ast, Expr, Pattern, Stmt};
use ruff_python_parser::semantic_errors::{
    AwaitOutsideAsyncFunctionKind, InvalidExpressionKind, LazyImportContext, SemanticSyntaxChecker,
    SemanticSyntaxContext, SemanticSyntaxError, SemanticSyntaxErrorKind, WriteToDebugKind,
};
use ruff_text_size::{Ranged, TextRange};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::{CompileError, OptimizationLevel, PythonVersion};

use super::constant::explicit_surrogate_string;
use super::statement::suite_contains_yield_in_function_scope;
use super::symbol::mangle_name;

#[cfg(test)]
mod declaration_tests;
mod declarations;
mod mapping_diagnostic;
mod pattern_debug;
mod pattern_numeric;
mod unicode_printable;

/// Conservatively identify modules whose mapping patterns might contain duplicate keys.
pub(crate) fn may_have_duplicate_mapping_key(body: &[Stmt]) -> bool {
    struct Finder(bool);

    impl<'ast> Visitor<'ast> for Finder {
        fn visit_stmt(&mut self, statement: &'ast Stmt) {
            if crate::stack_growth_required() {
                return crate::grow_stack(|| self.visit_stmt(statement));
            }
            if !self.0 {
                walk_stmt(self, statement);
            }
        }

        fn visit_pattern(&mut self, pattern: &'ast Pattern) {
            if crate::stack_growth_required() {
                return crate::grow_stack(|| self.visit_pattern(pattern));
            }
            if self.0 {
                return;
            }
            if matches!(pattern, Pattern::MatchMapping(mapping) if mapping.keys.len() > 1) {
                self.0 = true;
            } else {
                walk_pattern(self, pattern);
            }
        }

        fn visit_expr(&mut self, _expression: &'ast Expr) {}
    }

    let mut finder = Finder(false);
    finder.visit_body(body);
    finder.0
}

/// Validate AST-based syntax restrictions using Ruff's shared checker.
#[cfg(test)]
pub(crate) fn validate(
    source: &str,
    body: &[Stmt],
    python_version: PythonVersion,
) -> Result<(), CompileError> {
    validate_with_optimization(source, body, python_version, OptimizationLevel::Zero)
}

/// Validate syntax before optimization, retaining symbol-table checks in discarded assertions.
#[cfg(test)]
fn validate_with_optimization(
    source: &str,
    body: &[Stmt],
    python_version: PythonVersion,
    optimization_level: OptimizationLevel,
) -> Result<(), CompileError> {
    validate_with_integer_limit(source, body, python_version, optimization_level, None)
}

pub(crate) fn validate_with_integer_limit(
    source: &str,
    body: &[Stmt],
    python_version: PythonVersion,
    optimization_level: OptimizationLevel,
    mapping_key_int_max_str_digits: Option<u32>,
) -> Result<(), CompileError> {
    validate_with_statement_pruning::<true>(
        source,
        body,
        python_version,
        optimization_level,
        mapping_key_int_max_str_digits,
    )
}

fn validate_declarations(
    source: &str,
    body: &[Stmt],
    python_version: PythonVersion,
) -> Result<(), CompileError> {
    // Keywords cannot be escaped or normalized into their ASCII spellings. Avoid walking modules
    // without a possible declaration; strings and comments merely cause a harmless extra walk.
    if source.contains("global") || source.contains("nonlocal") {
        declarations::validate(body, python_version)?;
    }
    Ok(())
}

fn validate_with_statement_pruning<const PRUNE_STATEMENTS: bool>(
    source: &str,
    body: &[Stmt],
    python_version: PythonVersion,
    optimization_level: OptimizationLevel,
    mapping_key_int_max_str_digits: Option<u32>,
) -> Result<(), CompileError> {
    let mut validator = new_validator::<PRUNE_STATEMENTS, false>(
        source,
        body,
        python_version,
        optimization_level,
        mapping_key_int_max_str_digits,
    );
    validator.visit_scope_body(body);
    let lowering_keyword_error = validator.lowering_keyword_error.get();
    let debug_pattern_replay =
        matches!(python_version, PythonVersion::Py314 | PythonVersion::Py315)
            && validator.may_have_debug_patterns
            && pattern_debug::body_has_debug_pattern(body);
    let mut numeric_symbol_replay = validator.lowering_numeric_error
        && matches!(python_version, PythonVersion::Py314 | PythonVersion::Py315);
    let lowering_error = lowering_keyword_error
        || validator.lowering_debug_error
        || validator.lowering_numeric_error
        || debug_pattern_replay;
    let mut error = validator.error.into_inner();
    let legacy_async_generator_return = error
        .as_ref()
        .is_some_and(|error| error.is_legacy_async_generator_return);
    if legacy_async_generator_return
        || (error
            .as_ref()
            .is_some_and(|error| error.is_async_generator_return)
            && simple_comprehension_module(body))
    {
        // Value returns in async generators fail during lowering, after symbol checks.
        // A legacy sync function can gain those flags from a removed assertion; simple
        // comprehension modules have no competing symbol-table diagnostics.
        let mut replay = new_validator::<false, false>(
            source,
            body,
            python_version,
            optimization_level,
            mapping_key_int_max_str_digits,
        );
        replay.pre_lowering_only = true;
        replay.visit_body(body);
        if let Some(priority_error) = replay.error.into_inner() {
            if legacy_async_generator_return
                && (source.contains("global") || source.contains("nonlocal"))
                && let Some(range) = priority_error.error.range()
                && let Some(declaration_error) =
                    declarations::immediate_before_node(body, python_version, range)
            {
                return Err(declaration_error);
            }
            return Err(priority_error.error);
        }
        if legacy_async_generator_return {
            validate_declarations(source, body, python_version)?;
        }
    }
    if lowering_keyword_error
        && let Some(CompileError::InvalidSyntax { range, .. }) =
            error.as_ref().map(|error| &error.error)
    {
        // A class body is compiled before its bases and class-call keywords. Revisit only
        // classes containing the lowering error, leaving the ordinary symbol walk unchanged.
        let mut replay = new_validator::<PRUNE_STATEMENTS, false>(
            source,
            body,
            python_version,
            optimization_level,
            mapping_key_int_max_str_digits,
        );
        replay.class_lowering_target = Some(*range);
        replay.visit_scope_body(body);
        let replay_numeric_error = replay.lowering_numeric_error;
        let replay_error = replay.error.into_inner().or_else(|| {
            replay
                .bare_starred
                .map(|(range, kind)| CompileError::invalid_syntax(kind.message(), range).into())
        });
        // A numeric duplicate found in the class body needs the same ordered symbol replay
        // as one found by the initial walk.
        if replay_error.is_some()
            && matches!(python_version, PythonVersion::Py314 | PythonVersion::Py315)
        {
            numeric_symbol_replay |= replay_numeric_error;
        }
        error = replay_error.or(error);
    }
    let error = error.map(|error| error.error);
    if matches!(&error, Some(CompileError::InvalidDocstring { .. })) || lowering_error {
        // Revisit these error paths for diagnostics from earlier compiler phases.
        // Future directives moved ahead of call lowering in Python 3.14.
        if !debug_pattern_replay
            && !numeric_symbol_replay
            && (!lowering_error
                || matches!(python_version, PythonVersion::Py314 | PythonVersion::Py315))
        {
            let mut validator = new_validator::<false, true>(
                source,
                body,
                python_version,
                optimization_level,
                mapping_key_int_max_str_digits,
            );
            validator.visit_body(body);
            if let Some(future_error) = validator.error.into_inner() {
                return Err(future_error.error);
            }
        }
        // Symbol-table diagnostics precede docstring cleanup too, including declarations in
        // another scope. Keep walking past code-generation errors to find those diagnostics.
        let mut validator = new_validator::<false, false>(
            source,
            body,
            python_version,
            optimization_level,
            mapping_key_int_max_str_digits,
        );
        validator.pre_lowering_only = true;
        validator.numeric_symbol_replay = numeric_symbol_replay;
        validator.visit_body(body);
        let pattern_debug_range = validator.symbol_pattern_debug_range;
        if let Some(priority_error) = validator.error.into_inner() {
            let priority_error = priority_error.error;
            if source.contains("global") || source.contains("nonlocal") {
                let prior_declaration = if let Some(range) = pattern_debug_range {
                    declarations::immediate_before_pattern_debug(body, python_version, range)
                } else if numeric_symbol_replay {
                    priority_error.range().and_then(|range| {
                        declarations::immediate_before_node(body, python_version, range)
                    })
                } else {
                    None
                };
                if let Some(declaration_error) = prior_declaration {
                    return Err(declaration_error);
                }
            }
            return Err(priority_error);
        }
        validate_declarations(source, body, python_version)?;
    }
    let lowering_error = validator.lowering_pattern_error
        || matches!(&error, Some(CompileError::InvalidPattern { .. }))
        || (error.is_none() && validator.bare_starred.is_some());
    let result = error
        .or_else(|| {
            validator
                .bare_starred
                .map(|(range, kind)| CompileError::invalid_syntax(kind.message(), range))
        })
        .map_or(Ok(()), Err);
    // CPython resolves declarations in the symbol table before lowering match patterns or bare
    // stars. Other errors from the shared checker retain their precedence over declarations.
    if lowering_error {
        validate_declarations(source, body, python_version)?;
        return result;
    }
    result?;
    if validator.has_declarations {
        declarations::validate(body, python_version)?;
    }
    Ok(())
}

/// Recognize a small grammar whose symbol-table walk has the same order as the replay visitor.
fn simple_comprehension_module(body: &[Stmt]) -> bool {
    body.iter().all(|statement| match statement {
        Stmt::FunctionDef(function) => simple_comprehension_function(function),
        Stmt::Assign(_) | Stmt::Expr(_) | Stmt::Pass(_) => {
            simple_comprehension_statement(statement)
        }
        _ => false,
    })
}

fn simple_comprehension_function(function: &ast::StmtFunctionDef) -> bool {
    if function.name.as_str() == "__debug__"
        || !function.decorator_list.is_empty()
        || function.type_params.is_some()
        || function.returns.is_some()
    {
        return false;
    }
    let mut names = FxHashSet::default();
    if !function.parameters.iter().all(|parameter| {
        let name = parameter.name().as_str();
        name != "__debug__"
            && names.insert(name)
            && parameter.annotation().is_none()
            && parameter.default().is_none_or(simple_atom)
    }) {
        return false;
    }
    function.body.iter().all(simple_comprehension_statement)
}

fn simple_comprehension_statement(statement: &Stmt) -> bool {
    match statement {
        Stmt::Pass(_) => true,
        Stmt::Assign(statement) => {
            statement
                .targets
                .iter()
                .all(|target| matches!(target, Expr::Name(name) if name.id.as_str() != "__debug__"))
                && simple_comprehension_expression(&statement.value)
        }
        Stmt::Return(statement) => statement
            .value
            .as_deref()
            .is_none_or(simple_comprehension_expression),
        Stmt::Expr(statement) => simple_comprehension_expression(&statement.value),
        _ => false,
    }
}

fn simple_comprehension_expression(expression: &Expr) -> bool {
    if simple_atom_or_yield(expression) {
        return true;
    }
    let (generators, result): (&[ast::Comprehension], bool) = match expression {
        Expr::ListComp(comp) => (&comp.generators, simple_atom_or_yield(&comp.elt)),
        Expr::SetComp(comp) => (&comp.generators, simple_atom_or_yield(&comp.elt)),
        Expr::Generator(comp) => (&comp.generators, simple_atom_or_yield(&comp.elt)),
        Expr::DictComp(comp) => (
            &comp.generators,
            comp.key.as_deref().is_some_and(simple_atom_or_yield)
                && simple_atom_or_yield(&comp.value),
        ),
        _ => return false,
    };
    result
        && !generators.is_empty()
        && generators.iter().all(|generator| {
            !generator.is_async
                && generator.ifs.is_empty()
                && matches!(&generator.target, Expr::Name(name) if name.id.as_str() != "__debug__")
                && matches!(generator.iter, Expr::Name(_))
        })
}

fn simple_atom_or_yield(expression: &Expr) -> bool {
    match expression {
        Expr::Yield(yield_) => yield_.value.as_deref().is_none_or(simple_atom),
        Expr::YieldFrom(yield_from) => simple_atom(&yield_from.value),
        _ => simple_atom(expression),
    }
}

fn simple_atom(expression: &Expr) -> bool {
    matches!(
        expression,
        Expr::Name(_)
            | Expr::StringLiteral(_)
            | Expr::BytesLiteral(_)
            | Expr::NumberLiteral(_)
            | Expr::BooleanLiteral(_)
            | Expr::NoneLiteral(_)
            | Expr::EllipsisLiteral(_)
    )
}

fn new_validator<'source, 'ast, const PRUNE_STATEMENTS: bool, const FUTURE_ONLY: bool>(
    source: &'source str,
    body: &'ast [Stmt],
    python_version: PythonVersion,
    optimization_level: OptimizationLevel,
    mapping_key_int_max_str_digits: Option<u32>,
) -> Validator<'source, 'ast, PRUNE_STATEMENTS, FUTURE_ONLY> {
    Validator {
        checker: SemanticSyntaxChecker::new(),
        checked_type_params: None,
        checker_prefix: CheckerPrefix::Initial,
        error: RefCell::new(None),
        reported_future_feature: Cell::new(None),
        collected_match_errors: RefCell::new(None),
        symbol_pattern_debug_range: None,
        pending_pattern: None,
        checked_match: None,
        surrogate_mapping_keys: RefCell::new(FxHashMap::default()),
        lowering_pattern_error: false,
        lowering_keyword_error: Cell::new(false),
        checking_class_header: Cell::new(false),
        suppress_class_keyword: Cell::new(false),
        class_lowering_target: None,
        class_lowering_depth: 0,
        lowering_debug_error: false,
        lowering_numeric_error: false,
        numeric_symbol_replay: false,
        bare_starred: None,
        check_bare_starred: true,
        has_declarations: false,
        pre_lowering_only: false,
        optimization_level,
        comprehension_yield_operand: false,
        checking_comprehension_yield: false,
        collecting_comprehension_errors: false,
        deferred_comprehension_errors: RefCell::new(Vec::new()),
        source,
        may_have_debug_patterns: source.contains("__debug__") || !source.is_ascii(),
        may_have_legacy_coroutines: matches!(
            python_version,
            PythonVersion::Py312 | PythonVersion::Py313
        ) && optimization_level != OptimizationLevel::Zero
            && (source.contains("await") || source.contains("async")),
        body,
        mapping_key_int_max_str_digits,
        python_version: match python_version {
            PythonVersion::Py312 => ast::PythonVersion::PY312,
            PythonVersion::Py313 => ast::PythonVersion::PY313,
            PythonVersion::Py314 => ast::PythonVersion::PY314,
            PythonVersion::Py315 => ast::PythonVersion::PY315,
        },
        future_annotations: body.iter().any(|statement| {
            matches!(statement, Stmt::ImportFrom(import)
                if import.level == 0 && import.module.as_deref() == Some("__future__")
                    && import.names.iter().any(|alias| alias.name.as_str() == "annotations"))
        }),
        private_name: None,
        mangled_names: None,
        scopes: vec![Scope::new(ScopeKind::Module)],
    }
}

#[cfg(test)]
fn validate_without_statement_pruning(
    source: &str,
    body: &[Stmt],
    python_version: PythonVersion,
) -> Result<(), CompileError> {
    validate_with_statement_pruning::<false>(
        source,
        body,
        python_version,
        OptimizationLevel::Zero,
        None,
    )
}

/// Returns the UTF-8 failure CPython encounters before it starts cleaning a docstring.
fn surrogate_docstring_error(source: &str, string: &ast::ExprStringLiteral) -> Option<String> {
    if !string
        .value
        .iter()
        .any(|part| !part.flags.prefix().is_raw() && part.as_str().contains('\u{fffd}'))
    {
        return None;
    }

    let mut value = Vec::new();
    for part in &string.value {
        if !part.flags.prefix().is_raw()
            && let Some(restored) = explicit_surrogate_string(part.as_str(), &source[part.range])
        {
            value.extend(restored);
        } else {
            value.extend_from_slice(part.as_str().as_bytes());
        }
    }

    // The restored value is UTF-8 with surrogate code points retained. Only leading bytes
    // contribute a character position, and CPython reports the first contiguous surrogate run.
    let mut first = None;
    let mut end = 0;
    for (position, (offset, _)) in value
        .iter()
        .enumerate()
        .filter(|(_, byte)| **byte & 0xc0 != 0x80)
        .enumerate()
    {
        if let [0xed, middle @ 0xa0..=0xbf, last @ 0x80..=0xbf, ..] = value[offset..] {
            let codepoint = 0xd000 | (u16::from(middle & 0x3f) << 6) | u16::from(last & 0x3f);
            first.get_or_insert((position, codepoint));
            end = position + 1;
        } else if first.is_some() {
            break;
        }
    }
    let (start, codepoint) = first?;
    let characters = if end == start + 1 {
        format!("character '\\u{codepoint:04x}' in position {start}")
    } else {
        format!("characters in position {start}-{}", end - 1)
    };
    Some(format!(
        "'utf-8' codec can't encode {characters}: surrogates not allowed"
    ))
}

#[derive(Clone, Copy)]
enum CheckerPrefix {
    Initial,
    Open,
    Closed,
}

#[derive(Clone, Copy)]
enum BareStarredKind {
    Expression,
    AssignmentTarget,
}

impl BareStarredKind {
    fn message(self) -> &'static str {
        match self {
            Self::Expression => "can't use starred expression here",
            Self::AssignmentTarget => "starred assignment target must be in a list or tuple",
        }
    }
}

#[derive(Clone, Copy)]
enum ComprehensionKind {
    List,
    Set,
    Dict,
    Generator,
}

impl ComprehensionKind {
    fn yield_error(self) -> &'static str {
        match self {
            Self::List => "'yield' inside list comprehension",
            Self::Set => "'yield' inside set comprehension",
            Self::Dict => "'yield' inside dict comprehension",
            Self::Generator => "'yield' inside generator expression",
        }
    }
}

#[derive(Clone, Copy)]
enum ScopeKind<'ast> {
    Module,
    Class,
    Function {
        is_async: bool,
        is_async_generator: bool,
        parameters: Option<&'ast ast::Parameters>,
    },
    Comprehension {
        kind: ComprehensionKind,
        is_async: bool,
    },
}

struct Scope<'ast> {
    kind: ScopeKind<'ast>,
    loop_depth: usize,
    except_star_loop_depth: Option<usize>,
    in_try: bool,
    deferred_annotations: Vec<&'ast Expr>,
}

impl<'ast> Scope<'ast> {
    fn new(kind: ScopeKind<'ast>) -> Self {
        Self {
            kind,
            loop_depth: 0,
            except_star_loop_depth: None,
            in_try: false,
            deferred_annotations: Vec::new(),
        }
    }
}

/// Preserve the fields Ruff checks on an ordinary function while replacing
/// simple annotations with leaves its recursive checker can visit cheaply.
fn simple_function_checker_view(function: &ast::StmtFunctionDef) -> Option<Stmt> {
    fn leaf() -> Expr {
        Expr::NoneLiteral(ast::ExprNoneLiteral::default())
    }
    fn parameter(original: &ast::Parameter) -> ast::Parameter {
        ast::Parameter {
            range: original.range,
            node_index: original.node_index.clone(),
            name: original.name.clone(),
            annotation: original.annotation.as_ref().map(|_| Box::new(leaf())),
        }
    }
    fn with_default(original: &ast::ParameterWithDefault) -> ast::ParameterWithDefault {
        ast::ParameterWithDefault {
            range: original.range,
            node_index: original.node_index.clone(),
            parameter: parameter(&original.parameter),
            default: original.default.as_ref().map(|_| Box::new(leaf())),
        }
    }

    if function.is_async
        || function.type_params.is_some()
        || !function
            .parameters
            .iter()
            .filter_map(ast::AnyParameterRef::annotation)
            .all(crate::stack::is_simple_annotation)
        || !function
            .returns
            .as_deref()
            .is_none_or(crate::stack::is_simple_annotation)
    {
        return None;
    }

    let original = &function.parameters;
    let parameters = ast::Parameters {
        range: original.range,
        node_index: original.node_index.clone(),
        posonlyargs: original.posonlyargs.iter().map(with_default).collect(),
        args: original.args.iter().map(with_default).collect(),
        vararg: original.vararg.as_deref().map(parameter).map(Box::new),
        kwonlyargs: original.kwonlyargs.iter().map(with_default).collect(),
        kwarg: original.kwarg.as_deref().map(parameter).map(Box::new),
    };
    Some(Stmt::FunctionDef(ast::StmtFunctionDef {
        node_index: function.node_index.clone(),
        range: function.range,
        is_async: false,
        decorator_list: ast::DecoratorList::new(),
        name: function.name.clone(),
        type_params: None,
        parameters: Box::new(parameters),
        returns: function.returns.as_ref().map(|_| Box::new(leaf())),
        body: ast::Suite::new(),
    }))
}

struct Validator<'source, 'ast, const PRUNE_STATEMENTS: bool, const FUTURE_ONLY: bool> {
    pre_lowering_only: bool,
    optimization_level: OptimizationLevel,
    may_have_legacy_coroutines: bool,
    comprehension_yield_operand: bool,
    checking_comprehension_yield: bool,
    collecting_comprehension_errors: bool,
    deferred_comprehension_errors: RefCell<Vec<FxHashMap<TextRange, Vec<SemanticSyntaxError>>>>,
    checker: SemanticSyntaxChecker,
    checked_type_params: Option<&'ast ast::TypeParams>,
    checker_prefix: CheckerPrefix,
    error: RefCell<Option<ValidationError>>,
    reported_future_feature: Cell<Option<TextRange>>,
    collected_match_errors: RefCell<Option<Vec<SemanticSyntaxError>>>,
    symbol_pattern_debug_range: Option<TextRange>,
    pending_pattern: Option<PendingPattern<'ast>>,
    checked_match: Option<&'ast ast::StmtMatch>,
    surrogate_mapping_keys: RefCell<FxHashMap<TextRange, bool>>,
    lowering_pattern_error: bool,
    lowering_keyword_error: Cell<bool>,
    checking_class_header: Cell<bool>,
    suppress_class_keyword: Cell<bool>,
    class_lowering_target: Option<TextRange>,
    class_lowering_depth: usize,
    lowering_debug_error: bool,
    lowering_numeric_error: bool,
    numeric_symbol_replay: bool,
    bare_starred: Option<(TextRange, BareStarredKind)>,
    check_bare_starred: bool,
    has_declarations: bool,
    source: &'source str,
    may_have_debug_patterns: bool,
    body: &'ast [Stmt],
    python_version: ast::PythonVersion,
    mapping_key_int_max_str_digits: Option<u32>,
    future_annotations: bool,
    private_name: Option<&'ast str>,
    mangled_names: Option<FxHashSet<&'ast str>>,
    scopes: Vec<Scope<'ast>>,
}

/// Ruff represents escaped lone surrogates as U+FFFD in its AST. Compare the original
/// decoded strings when its mapping-pattern duplicate check encounters such a value.
fn surrogate_mapping_key_outcomes(
    statement: &ast::StmtMatch,
    source: &str,
    range: TextRange,
) -> Option<Vec<(TextRange, bool)>> {
    fn string_bytes(source: &str, string: &ast::ExprStringLiteral) -> Vec<u8> {
        let mut result = Vec::new();
        for part in &string.value {
            if !part.flags.prefix().is_raw()
                && let Some(restored) =
                    explicit_surrogate_string(part.as_str(), &source[part.range])
            {
                result.extend(restored);
            } else {
                result.extend_from_slice(part.as_str().as_bytes());
            }
        }
        result
    }

    struct Finder<'a> {
        source: &'a str,
        range: TextRange,
        outcomes: Option<Vec<(TextRange, bool)>>,
    }
    impl<'ast> Visitor<'ast> for Finder<'_> {
        fn visit_pattern(&mut self, pattern: &'ast Pattern) {
            if self.outcomes.is_some() {
                return;
            }
            if crate::stack_growth_required() {
                return crate::grow_stack(|| self.visit_pattern(pattern));
            }
            if !pattern.range().contains_range(self.range) {
                return;
            }
            if let Pattern::MatchMapping(mapping) = pattern
                && let Some(index) = mapping
                    .keys
                    .iter()
                    .position(|key| key.range() == self.range)
                && let Expr::StringLiteral(string) = &mapping.keys[index]
            {
                if string.value.to_str().contains('\u{fffd}') {
                    let mut seen = FxHashSet::default();
                    self.outcomes = Some(
                        mapping
                            .keys
                            .iter()
                            .filter_map(|key| {
                                let Expr::StringLiteral(string) = key else {
                                    return None;
                                };
                                // A first occurrence is not a duplicate even if Ruff's lossy
                                // representation collides with a different earlier string.
                                let unique = seen.insert(string_bytes(self.source, string));
                                Some((
                                    key.range(),
                                    unique && string.value.to_str().contains('\u{fffd}'),
                                ))
                            })
                            .collect(),
                    );
                }
                return;
            }
            walk_pattern(self, pattern);
        }
    }

    let mut finder = Finder {
        source,
        range,
        outcomes: None,
    };
    let index = statement
        .cases
        .partition_point(|case| case.pattern.range().end() <= range.start());
    if let Some(case) = statement.cases.get(index) {
        finder.visit_pattern(&case.pattern);
    }
    finder.outcomes
}

struct ValidationError {
    error: CompileError,
    is_async_generator_return: bool,
    is_legacy_async_generator_return: bool,
}

impl ValidationError {
    #[cold]
    #[inline(never)]
    fn from_semantic(
        error: &SemanticSyntaxError,
        python_version: ast::PythonVersion,
        scope: ScopeKind<'_>,
        comprehension_yield_operand: bool,
        checked_type_params: Option<&ast::TypeParams>,
    ) -> Self {
        use SemanticSyntaxErrorKind as Kind;
        let message = match &error.kind {
            Kind::FutureFeatureNotDefined(name) => {
                if name == "braces" {
                    "not a chance".to_owned()
                } else {
                    // CPython limits the UTF-8 representation to 100 bytes. Incomplete
                    // characters at the limit are replaced before 3.14 and omitted afterward.
                    let mut end = name.len().min(100);
                    if python_version >= ast::PythonVersion::PY314 {
                        while !name.is_char_boundary(end) {
                            end -= 1;
                        }
                    }
                    let feature = String::from_utf8_lossy(&name.as_bytes()[..end]);
                    format!("future feature {feature} is not defined")
                }
            }
            Kind::LateFutureImport => {
                "from __future__ imports must occur at the beginning of the file".to_owned()
            }
            Kind::WriteToDebug(WriteToDebugKind::Store) => "cannot assign to __debug__".to_owned(),
            Kind::WriteToDebug(WriteToDebugKind::Delete(_)) => "cannot delete __debug__".to_owned(),
            Kind::BreakOutsideLoop => "'break' outside loop".to_owned(),
            Kind::ContinueOutsideLoop => "'continue' not properly in loop".to_owned(),
            Kind::ReturnOutsideFunction => "'return' outside function".to_owned(),
            Kind::YieldOutsideFunction(kind) => {
                if !kind.is_await()
                    && let ScopeKind::Comprehension { kind, .. } = scope
                {
                    kind.yield_error().to_owned()
                } else {
                    format!("'{kind}' outside function")
                }
            }
            Kind::YieldFromInAsyncFunction => "'yield from' inside async function".to_owned(),
            Kind::AwaitOutsideAsyncFunction(AwaitOutsideAsyncFunctionKind::Await) => {
                if comprehension_yield_operand
                    || matches!(
                        scope,
                        ScopeKind::Function {
                            is_async: false,
                            ..
                        }
                    )
                {
                    "'await' outside async function".to_owned()
                } else {
                    "'await' outside function".to_owned()
                }
            }
            Kind::DuplicateParameter(name) if comprehension_yield_operand => {
                let kind = if python_version >= ast::PythonVersion::PY315 {
                    "parameter"
                } else {
                    "argument"
                };
                format!("duplicate {kind} '{name}' in function definition")
            }
            Kind::AwaitOutsideAsyncFunction(AwaitOutsideAsyncFunctionKind::AsyncFor) => {
                "'async for' outside async function".to_owned()
            }
            Kind::AwaitOutsideAsyncFunction(AwaitOutsideAsyncFunctionKind::AsyncWith) => {
                "'async with' outside async function".to_owned()
            }
            Kind::DuplicateTypeParameter => checked_type_params
                .and_then(|params| params.iter().find(|param| param.range() == error.range))
                .map_or_else(
                    || error.to_string(),
                    |param| format!("duplicate type parameter '{}'", param.name().as_str()),
                ),
            Kind::MultipleCaseAssignment(name) => {
                format!("multiple assignments to name '{name}' in pattern")
            }
            _ => error.to_string(),
        };
        let is_async_generator_return = matches!(error.kind, Kind::ReturnInGenerator);
        let is_legacy_async_generator_return = is_async_generator_return
            && matches!(
                scope,
                ScopeKind::Function {
                    is_async: false,
                    ..
                }
            );
        Self {
            error: if matches!(
                error.kind,
                Kind::DifferentMatchPatternBindings
                    | Kind::MultipleCaseAssignment(_)
                    | Kind::MultipleStarredNamesInSequencePattern
                    | Kind::IrrefutableCasePattern(_)
                    | Kind::DuplicateMatchKey(_)
                    | Kind::DuplicateMatchClassAttribute(_)
            ) {
                CompileError::InvalidPattern {
                    message,
                    range: error.range,
                }
            } else {
                CompileError::invalid_syntax(message, error.range)
            },
            is_async_generator_return,
            is_legacy_async_generator_return,
        }
    }
}

impl From<CompileError> for ValidationError {
    fn from(error: CompileError) -> Self {
        Self {
            error,
            is_async_generator_return: false,
            is_legacy_async_generator_return: false,
        }
    }
}

struct PendingPattern<'ast> {
    statement: &'ast ast::StmtMatch,
    pattern: ast::IrrefutablePattern,
}

impl PendingPattern<'_> {
    /// Preserve pattern errors CPython checks before reaching the irrefutable token.
    fn prefers(&self, error: &SemanticSyntaxError) -> bool {
        use SemanticSyntaxErrorKind as Kind;
        match &error.kind {
            // Binding a reserved name is rejected by the symbol table before any pattern lowering.
            Kind::WriteToDebug(_) => true,
            Kind::IrrefutableCasePattern(_) => false,
            Kind::MultipleCaseAssignment(_) => error.range.start() < self.pattern.range.start(),
            Kind::MultipleStarredNamesInSequencePattern
            | Kind::DuplicateMatchKey(_)
            | Kind::DuplicateMatchClassAttribute(_) => {
                error.range.start() < self.pattern.range.start()
                    || self.statement.cases.iter().any(|case| {
                        pattern_preflight_contains(&case.pattern, self.pattern.range, error)
                    })
            }
            Kind::DifferentMatchPatternBindings => {
                if !error.range.contains_range(self.pattern.range) {
                    return error.range.end() <= self.pattern.range.start();
                }
                self.statement.cases.iter().any(|case| {
                    let Some(pattern) = find_or_pattern(&case.pattern, error.range) else {
                        return false;
                    };
                    let Some((first, rest)) = pattern.patterns.split_first() else {
                        return false;
                    };
                    let first_names = pattern_capture_names(first);
                    rest.iter()
                        .find(|arm| pattern_capture_names(arm) != first_names)
                        .is_some_and(|arm| arm.range().end() <= self.pattern.range.start())
                })
            }
            _ => true,
        }
    }
}

fn pattern_preflight_contains(
    root: &Pattern,
    candidate: TextRange,
    error: &SemanticSyntaxError,
) -> bool {
    struct Finder<'a> {
        candidate: TextRange,
        error: &'a SemanticSyntaxError,
        found: bool,
    }
    impl<'ast> Visitor<'ast> for Finder<'_> {
        fn visit_pattern(&mut self, pattern: &'ast Pattern) {
            use SemanticSyntaxErrorKind as Kind;

            if self.found || !pattern.range().contains_range(self.candidate) {
                return;
            }
            self.found = match (pattern, &self.error.kind) {
                (Pattern::MatchSequence(pattern), Kind::MultipleStarredNamesInSequencePattern) => {
                    pattern
                        .patterns
                        .iter()
                        .filter(|pattern| pattern.is_match_star())
                        .skip(1)
                        .any(|pattern| pattern.range() == self.error.range)
                }
                (Pattern::MatchMapping(pattern), Kind::DuplicateMatchKey(_)) => pattern
                    .keys
                    .iter()
                    .any(|key| key.range() == self.error.range),
                (Pattern::MatchClass(pattern), Kind::DuplicateMatchClassAttribute(_)) => pattern
                    .arguments
                    .keywords
                    .iter()
                    .any(|keyword| keyword.attr.range == self.error.range),
                _ => false,
            };
            if !self.found {
                walk_pattern(self, pattern);
            }
        }
    }
    let mut finder = Finder {
        candidate,
        error,
        found: false,
    };
    finder.visit_pattern(root);
    finder.found
}

fn find_or_pattern(root: &Pattern, range: TextRange) -> Option<&ast::PatternMatchOr> {
    struct Finder<'ast> {
        range: TextRange,
        found: Option<&'ast ast::PatternMatchOr>,
    }
    impl<'ast> Visitor<'ast> for Finder<'ast> {
        fn visit_pattern(&mut self, pattern: &'ast Pattern) {
            if self.found.is_some() || !pattern.range().contains_range(self.range) {
                return;
            }
            if let Pattern::MatchOr(pattern) = pattern
                && pattern.range == self.range
            {
                self.found = Some(pattern);
            } else {
                walk_pattern(self, pattern);
            }
        }
    }
    let mut finder = Finder { range, found: None };
    finder.visit_pattern(root);
    finder.found
}

fn pattern_capture_names(pattern: &Pattern) -> FxHashSet<&str> {
    #[derive(Default)]
    struct CaptureNames<'ast>(FxHashSet<&'ast str>);
    impl<'ast> Visitor<'ast> for CaptureNames<'ast> {
        fn visit_pattern(&mut self, pattern: &'ast Pattern) {
            if let Pattern::MatchOr(pattern) = pattern {
                if let Some(first) = pattern.patterns.first() {
                    self.visit_pattern(first);
                }
                return;
            }
            let name = match pattern {
                Pattern::MatchAs(pattern) => pattern.name.as_ref(),
                Pattern::MatchStar(pattern) => pattern.name.as_ref(),
                Pattern::MatchMapping(pattern) => pattern.rest.as_ref(),
                _ => None,
            };
            if let Some(name) = name {
                self.0.insert(name.as_str());
            }
            walk_pattern(self, pattern);
        }
    }
    let mut names = CaptureNames::default();
    names.visit_pattern(pattern);
    names.0
}

impl<'ast, const PRUNE_STATEMENTS: bool, const FUTURE_ONLY: bool>
    Validator<'_, 'ast, PRUNE_STATEMENTS, FUTURE_ONLY>
{
    fn false_surrogate_mapping_duplicate(&self, range: TextRange) -> bool {
        if let Some(&unique) = self.surrogate_mapping_keys.borrow().get(&range) {
            return unique;
        }
        let Some(outcomes) = self
            .checked_match
            .and_then(|statement| surrogate_mapping_key_outcomes(statement, self.source, range))
        else {
            return false;
        };
        let mut cache = self.surrogate_mapping_keys.borrow_mut();
        cache.extend(outcomes);
        cache.get(&range).copied().unwrap_or(false)
    }

    fn record_bare_starred(&mut self, expression: &Expr, kind: BareStarredKind) {
        if !self.pre_lowering_only
            && self.check_bare_starred
            && self.bare_starred.is_none()
            && self.error.borrow().is_none()
            && expression.is_starred_expr()
        {
            self.bare_starred = Some((expression.range(), kind));
        }
    }

    fn with_bare_starred_check(&mut self, check: bool, visit: impl FnOnce(&mut Self)) {
        let previous = self.check_bare_starred;
        self.check_bare_starred &= check;
        visit(self);
        self.check_bare_starred = previous;
    }

    fn visit_scope_body(&mut self, body: &'ast [Stmt]) {
        if !self.pre_lowering_only
            && self.optimization_level != OptimizationLevel::Two
            && self.error.borrow().is_none()
            && self.python_version >= ast::PythonVersion::PY313
            && let Some(Stmt::Expr(statement)) = body.first()
            && let Expr::StringLiteral(string) = statement.value.as_ref()
            && let Some(message) = surrogate_docstring_error(self.source, string)
        {
            *self.error.borrow_mut() = Some(
                CompileError::InvalidDocstring {
                    message,
                    range: string.range,
                }
                .into(),
            );
        }
        self.visit_body(body);
        // Modern module and class annotations are lowered after the enclosing body.
        // Their symbol-table checks already ran when the assignment was encountered.
        for annotation in std::mem::take(&mut self.scope_mut().deferred_annotations) {
            self.visit_annotation(annotation);
        }
    }

    fn scope(&self) -> &Scope<'ast> {
        self.scopes
            .last()
            .expect("validation always has a module scope")
    }

    fn scope_mut(&mut self) -> &mut Scope<'ast> {
        self.scopes
            .last_mut()
            .expect("validation always has a module scope")
    }

    fn reject_except_star_transfer(&self, statement: &Stmt) {
        if self.pre_lowering_only {
            return;
        }
        let mut error = self.error.borrow_mut();
        if error.is_none() {
            *error = Some(
                CompileError::invalid_syntax(
                    "'break', 'continue' and 'return' cannot appear in an except* block",
                    statement.range(),
                )
                .into(),
            );
        }
    }

    fn check_debug_write(&mut self, name: &str, context: ast::ExprContext, range: TextRange) {
        // These checks moved from code generation into symbol analysis in Python 3.14,
        // which also made them apply inside stringized and unevaluated annotations.
        if name != "__debug__"
            || (!self.check_bare_starred && self.python_version < ast::PythonVersion::PY314)
        {
            return;
        }
        let kind = match context {
            ast::ExprContext::Store => WriteToDebugKind::Store,
            ast::ExprContext::Del if self.python_version >= ast::PythonVersion::PY314 => {
                WriteToDebugKind::Delete(self.python_version)
            }
            _ => return,
        };
        let track_lowering_error = self.python_version < ast::PythonVersion::PY314
            && !self.pre_lowering_only
            && self.bare_starred.is_none()
            && self.error.borrow().is_none();
        self.report_semantic_error(SemanticSyntaxError {
            kind: SemanticSyntaxErrorKind::WriteToDebug(kind),
            range,
            python_version: self.python_version,
        });
        if track_lowering_error && self.error.borrow().is_some() {
            self.lowering_debug_error = true;
        }
    }

    /// Call keyword names are checked before the callable or any argument is lowered.
    fn check_call_keywords(&mut self, arguments: &ast::Arguments) {
        if FUTURE_ONLY
            || !self.check_bare_starred
            || self.pre_lowering_only
            || self.bare_starred.is_some()
            || self.error.borrow().is_some()
        {
            return;
        }
        let legacy = self.python_version < ast::PythonVersion::PY314;
        if let Some((name, range)) = invalid_call_keyword(arguments, legacy) {
            // Legacy compilation checks each forbidden name before its later duplicates.
            // Modern forbidden-name checks belong to the earlier symbol-table pass.
            self.lowering_keyword_error.set(true);
            let message = if legacy && name == "__debug__" {
                "cannot assign to __debug__".to_owned()
            } else {
                format!("keyword argument repeated: {name}")
            };
            *self.error.borrow_mut() = Some(CompileError::invalid_syntax(message, range).into());
        }
    }

    fn defer_pattern_reachability(&mut self, statement: &'ast ast::StmtMatch) {
        for (index, case) in statement.cases.iter().enumerate() {
            let allow_irrefutable = case.guard.is_some() || index + 1 == statement.cases.len();
            if let Some(pattern) = unreachable_pattern(&case.pattern, allow_irrefutable) {
                self.pending_pattern = Some(PendingPattern { statement, pattern });
                return;
            }
        }
    }

    /// Ruff's annotation walk also visits independent lambda and lazy generator bodies.
    /// Their expressions are checked again below in the scope where they actually execute.
    fn escapes_annotation_scope(&self, range: TextRange, kind: &InvalidExpressionKind) -> bool {
        struct Finder {
            range: TextRange,
            is_await: bool,
            found: bool,
        }
        impl<'ast> Visitor<'ast> for Finder {
            fn visit_stmt(&mut self, statement: &'ast Stmt) {
                if !self.found && statement.range().contains_range(self.range) {
                    walk_stmt(self, statement);
                }
            }
            fn visit_expr(&mut self, expression: &'ast Expr) {
                if crate::stack_growth_required() {
                    return crate::grow_stack(|| self.visit_expr(expression));
                }

                if self.found || !expression.range().contains_range(self.range) {
                    return;
                }
                self.found = match expression {
                    Expr::Lambda(lambda) => lambda.body.range().contains_range(self.range),
                    Expr::Generator(generator) if self.is_await => {
                        // Only the first iterable executes eagerly in the annotation scope.
                        generator
                            .generators
                            .first()
                            .is_some_and(|first| !first.iter.range().contains_range(self.range))
                    }
                    _ => false,
                };
                if !self.found {
                    walk_expr(self, expression);
                }
            }
        }
        let mut finder = Finder {
            range,
            is_await: matches!(kind, InvalidExpressionKind::Await),
            found: false,
        };
        finder.visit_body(self.body);
        finder.found
    }

    fn with_scope(&mut self, kind: ScopeKind<'ast>, visit: impl FnOnce(&mut Self)) {
        self.scopes.push(Scope::new(kind));
        visit(self);
        self.scopes.pop();
    }

    fn with_private_context(
        &mut self,
        private_name: &'ast str,
        mangled_names: Option<FxHashSet<&'ast str>>,
        visit: impl FnOnce(&mut Self),
    ) {
        let previous_private = self.private_name.replace(private_name);
        let previous_mangled = std::mem::replace(&mut self.mangled_names, mangled_names);
        visit(self);
        self.private_name = previous_private;
        self.mangled_names = previous_mangled;
    }

    fn visit_class_body_in_lowering_order(&mut self, body: &'ast [Stmt]) {
        self.class_lowering_depth += 1;
        self.with_scope(ScopeKind::Class, |visitor| visitor.visit_scope_body(body));
        self.class_lowering_depth -= 1;
    }

    fn visit_class_arguments_in_lowering_order(&mut self, arguments: &'ast ast::Arguments) {
        self.check_call_keywords(arguments);
        self.visit_arguments(arguments);
    }

    fn visit_class_in_lowering_order(&mut self, class: &'ast ast::StmtClassDef) {
        for decorator in &class.decorator_list {
            self.visit_decorator(decorator);
        }
        if let Some(params) = &class.type_params {
            self.with_private_context(class.name.as_str(), Some(FxHashSet::default()), |visitor| {
                for parameter in params.iter() {
                    visitor
                        .mangled_names
                        .as_mut()
                        .expect("generic headers have restricted name mangling")
                        .insert(parameter.name().as_str());
                    visitor.visit_type_param(parameter);
                }
                let header_names = visitor.mangled_names.take();
                visitor.visit_class_body_in_lowering_order(&class.body);
                visitor.mangled_names = header_names;
                if let Some(arguments) = &class.arguments {
                    visitor.visit_class_arguments_in_lowering_order(arguments);
                }
            });
        } else {
            self.with_private_context(class.name.as_str(), None, |visitor| {
                visitor.visit_class_body_in_lowering_order(&class.body);
            });
            if let Some(arguments) = &class.arguments {
                self.visit_class_arguments_in_lowering_order(arguments);
            }
        }
    }

    fn validate_private_parameters(&self, parameters: &'ast ast::Parameters) {
        let Some(private_name) = self.private_name else {
            return;
        };
        // This check only reports differently spelled parameters that mangling makes equal.
        // Ruff already checks duplicate spellings, including when none of them can be mangled.
        if self.error.borrow().is_some()
            || parameters.len() < 2
            || private_name.trim_start_matches('_').is_empty()
            || !parameters.iter().any(|parameter| {
                let spelling = parameter.name().as_str();
                spelling.starts_with("__")
                    && !spelling.ends_with("__")
                    && !spelling.contains('.')
                    && self
                        .mangled_names
                        .as_ref()
                        .is_none_or(|names| names.contains(spelling))
            })
        {
            return;
        }
        let mut seen = FxHashMap::default();
        // Symbol analysis visits keyword-only parameters before either variadic parameter.
        for parameter in parameters
            .iter_non_variadic_params()
            .map(|parameter| &parameter.parameter)
            .chain(parameters.vararg.as_deref())
            .chain(parameters.kwarg.as_deref())
        {
            let spelling = parameter.name.as_str();
            let canonical = if self
                .mangled_names
                .as_ref()
                .is_some_and(|names| !names.contains(spelling))
            {
                Cow::Borrowed(spelling)
            } else {
                mangle_name(spelling, self.private_name)
            };
            if let Some(previous) = seen.insert(canonical, spelling)
                && previous != spelling
            {
                let kind = if self.python_version >= ast::PythonVersion::PY315 {
                    "parameter"
                } else {
                    "argument"
                };
                *self.error.borrow_mut() = Some(
                    CompileError::invalid_syntax(
                        format!("duplicate {kind} '{spelling}' in function definition"),
                        parameter.name.range(),
                    )
                    .into(),
                );
                return;
            }
        }
    }

    /// Reject nested scopes where Python 3.12 annotation scopes can see a class namespace.
    fn python_312_class_annotation_error(&self, statement: &Stmt) -> Option<CompileError> {
        #[derive(Default)]
        struct FirstRestriction(Option<Result<(&'static str, TextRange), ()>>);

        impl FirstRestriction {
            fn into_error(self) -> Option<CompileError> {
                self.0.and_then(Result::ok).map(|(kind, range)| {
                    CompileError::invalid_syntax(
                        format!("Cannot use {kind} in annotation scope within class scope"),
                        range,
                    )
                })
            }
        }

        impl<'ast> Visitor<'ast> for FirstRestriction {
            fn visit_expr(&mut self, expression: &'ast Expr) {
                if crate::stack_growth_required() {
                    return crate::grow_stack(|| self.visit_expr(expression));
                }

                if self.0.is_some() {
                    return;
                }
                match expression {
                    Expr::Lambda(_) => self.0 = Some(Ok(("lambda", expression.range()))),
                    Expr::ListComp(_)
                    | Expr::SetComp(_)
                    | Expr::DictComp(_)
                    | Expr::Generator(_) => {
                        self.0 = Some(Ok(("comprehension", expression.range())));
                    }
                    // These restrictions take precedence when symbol analysis reaches them first.
                    Expr::Named(_) | Expr::Yield(_) | Expr::YieldFrom(_) | Expr::Await(_) => {
                        self.0 = Some(Err(()));
                    }
                    Expr::Dict(dict) => {
                        // CPython visits every key before any value during symbol analysis.
                        for item in &dict.items {
                            if let Some(key) = &item.key {
                                self.visit_expr(key);
                            }
                        }
                        for item in &dict.items {
                            self.visit_expr(&item.value);
                        }
                    }
                    _ => walk_expr(self, expression),
                }
            }
        }

        let (parameters, private_name) = match statement {
            Stmt::TypeAlias(alias) => (alias.type_params.as_deref(), self.private_name),
            Stmt::ClassDef(class) if class.type_params.is_some() => {
                (class.type_params.as_deref(), Some(class.name.as_str()))
            }
            Stmt::FunctionDef(function) if function.type_params.is_some() => {
                (function.type_params.as_deref(), self.private_name)
            }
            _ => return None,
        };
        let mut first = FirstRestriction::default();
        if let Some(parameters) = parameters {
            let mut names = FxHashSet::default();
            for parameter in parameters {
                let name = parameter.name().as_str();
                if name == "__classdict__"
                    || !names.insert(mangle_name(name, private_name).into_owned())
                {
                    return first.into_error();
                }
                if let ast::TypeParam::TypeVar(parameter) = parameter
                    && let Some(bound) = parameter.bound.as_deref()
                {
                    first.visit_expr(bound);
                }
                if let Some(default) = parameter.default() {
                    first.visit_expr(default);
                }
            }
        }
        match statement {
            Stmt::TypeAlias(alias) => first.visit_expr(&alias.value),
            Stmt::ClassDef(class) => {
                if let Some(arguments) = &class.arguments {
                    // Symbol analysis visits all positional bases before keyword values.
                    for argument in &arguments.args {
                        first.visit_expr(argument);
                    }
                    for keyword in &arguments.keywords {
                        first.visit_expr(&keyword.value);
                    }
                }
            }
            Stmt::FunctionDef(function) if !self.future_annotations => {
                // Future annotations create a separate scope without class visibility.
                let parameters = &function.parameters;
                for parameter in parameters
                    .posonlyargs
                    .iter()
                    .chain(&parameters.args)
                    .map(|parameter| &parameter.parameter)
                    .chain(parameters.vararg.as_deref())
                    .chain(parameters.kwarg.as_deref())
                    .chain(
                        parameters
                            .kwonlyargs
                            .iter()
                            .map(|parameter| &parameter.parameter),
                    )
                {
                    if let Some(annotation) = &parameter.annotation {
                        first.visit_expr(annotation);
                    }
                }
                if let Some(returns) = &function.returns {
                    first.visit_expr(returns);
                }
            }
            _ => {}
        }
        first.into_error()
    }

    fn with_checker(&mut self, visit: impl FnOnce(&mut SemanticSyntaxChecker, &Self)) {
        let mut checker = std::mem::take(&mut self.checker);
        visit(&mut checker, self);
        self.checker = checker;
    }

    fn check_statement(&mut self, statement: &'ast Stmt) {
        // Ruff identifies the repeated parameter by range; keep its normalized AST name for
        // the CPython diagnostic emitted synchronously by the checker.
        self.checked_type_params = match statement {
            Stmt::FunctionDef(function) => function.type_params.as_deref(),
            Stmt::ClassDef(class) => class.type_params.as_deref(),
            Stmt::TypeAlias(alias) => alias.type_params.as_deref(),
            _ => None,
        };
        if let Stmt::AnnAssign(assignment) = statement
            && matches!(assignment.target.as_ref(), Expr::Name(_))
            && crate::stack::is_simple_annotation(&assignment.annotation)
        {
            // These annotations contain none of the expressions checked by Ruff's
            // recursive InvalidExpressionVisitor. Preserve the original target and
            // statement kind so its declaration and future-import checks still run.
            let statement = Stmt::AnnAssign(ast::StmtAnnAssign {
                node_index: assignment.node_index.clone(),
                range: assignment.range,
                target: assignment.target.clone(),
                annotation: Box::new(Expr::NoneLiteral(ast::ExprNoneLiteral::default())),
                value: None,
                simple: assignment.simple,
            });
            self.with_checker(|checker, context| checker.visit_stmt(&statement, context));
            return;
        }
        if let Stmt::TypeAlias(alias) = statement
            && alias.type_params.is_none()
            && matches!(alias.name.as_ref(), Expr::Name(_))
            && crate::stack::is_simple_annotation(&alias.value)
        {
            // Nongeneric aliases have no type-parameter checks; their value can
            // be replaced when it contains no invalid-expression candidates.
            let statement = Stmt::TypeAlias(ast::StmtTypeAlias {
                node_index: alias.node_index.clone(),
                range: alias.range,
                name: alias.name.clone(),
                type_params: None,
                value: Box::new(Expr::NoneLiteral(ast::ExprNoneLiteral::default())),
            });
            self.with_checker(|checker, context| checker.visit_stmt(&statement, context));
            return;
        }
        // Relative imports of a module named __future__ are ordinary imports. The shared
        // checker identifies directives by their module spelling, so hide that spelling here.
        if let Stmt::ImportFrom(import) = statement
            && import.level > 0
            && import.module.as_deref() == Some("__future__")
        {
            let mut import = import.clone();
            import.module = None;
            self.with_checker(|checker, context| {
                checker.visit_stmt(&Stmt::ImportFrom(import), context);
            });
        } else {
            // Ruff's semantic checker has a private recursive annotation visitor. Measure
            // the input it may walk and provide a stack sized for that walk.
            let mut depth = crate::stack::ExpressionDepth::default();
            match statement {
                Stmt::AnnAssign(statement) => depth.visit_expr(&statement.annotation),
                Stmt::FunctionDef(statement) => {
                    depth.visit_parameters(&statement.parameters);
                    if let Some(returns) = &statement.returns {
                        depth.visit_expr(returns);
                    }
                    if let Some(type_params) = &statement.type_params {
                        depth.visit_type_params(type_params);
                    }
                    if statement.is_async {
                        depth.visit_body(&statement.body);
                    }
                }
                Stmt::ClassDef(statement) => {
                    if let Some(arguments) = &statement.arguments {
                        depth.visit_arguments(arguments);
                    }
                    if let Some(type_params) = &statement.type_params {
                        depth.visit_type_params(type_params);
                    }
                }
                Stmt::TypeAlias(statement) => {
                    depth.visit_expr(&statement.value);
                    if let Some(type_params) = &statement.type_params {
                        depth.visit_type_params(type_params);
                    }
                }
                _ => {}
            }
            let depth = depth.maximum();
            if depth >= 1_024
                && let Stmt::FunctionDef(function) = statement
                && let Some(view) = simple_function_checker_view(function)
            {
                // Ruff's synchronous nongeneric function checks inspect names and
                // annotations, but not decorators, defaults, or the function body.
                // The validator still visits every original child after this check.
                self.with_checker(|checker, context| checker.visit_stmt(&view, context));
                return;
            }
            self.with_checker(|checker, context| {
                if depth == 0 {
                    checker.visit_stmt(statement, context);
                } else {
                    crate::stack::with_depth(depth, || checker.visit_stmt(statement, context));
                }
            });
        }
    }

    fn statement_needs_checker(&mut self, statement: &Stmt) -> bool {
        if !PRUNE_STATEMENTS {
            return true;
        }

        // Ruff updates its docstring and future-import boundaries on statement entry. Keep every
        // call until both are closed; after that its remaining statement state never changes.
        if !matches!(self.checker_prefix, CheckerPrefix::Closed) {
            let keeps_open = match statement {
                Stmt::Expr(statement) => {
                    matches!(self.checker_prefix, CheckerPrefix::Initial)
                        && statement.value.is_string_literal_expr()
                }
                Stmt::ImportFrom(import) => {
                    import.level == 0
                        && !import.is_lazy
                        && import.module.as_deref() == Some("__future__")
                }
                _ => false,
            };
            self.checker_prefix = if keeps_open {
                CheckerPrefix::Open
            } else {
                CheckerPrefix::Closed
            };
            return true;
        }

        // The pinned checker reports errors only for these statement kinds. Parent checks for
        // starred expressions apply to direct children; other child errors are still visited.
        match statement {
            Stmt::FunctionDef(_)
            | Stmt::ClassDef(_)
            | Stmt::TypeAlias(_)
            | Stmt::AnnAssign(_)
            | Stmt::Match(_)
            | Stmt::Try(_)
            | Stmt::Import(_)
            | Stmt::ImportFrom(_)
            | Stmt::Global(_)
            | Stmt::Nonlocal(_) => true,
            Stmt::Assign(statement) => {
                statement.value.is_starred_expr()
                    || matches!(statement.targets.as_slice(), [Expr::Starred(_)])
            }
            Stmt::Return(statement) => {
                !self.in_function_scope()
                    || statement
                        .value
                        .as_deref()
                        .is_some_and(Expr::is_starred_expr)
            }
            Stmt::For(statement) => {
                statement.is_async
                    || statement.target.is_starred_expr()
                    || statement.iter.is_starred_expr()
            }
            Stmt::With(statement) => statement.is_async,
            Stmt::Break(_) | Stmt::Continue(_) => !self.in_loop_context(),
            Stmt::Delete(_)
            | Stmt::AugAssign(_)
            | Stmt::While(_)
            | Stmt::If(_)
            | Stmt::Raise(_)
            | Stmt::Assert(_)
            | Stmt::Expr(_)
            | Stmt::Pass(_)
            | Stmt::IpyEscapeCommand(_) => false,
        }
    }

    fn comprehension(
        &mut self,
        generators: &'ast [ast::Comprehension],
        kind: ComprehensionKind,
        visit_result: impl FnOnce(&mut Self),
    ) {
        let Some((first, rest)) = generators.split_first() else {
            return;
        };
        // The first iterable executes in the enclosing scope, even for a lazy generator.
        self.visit_expr(&first.iter);
        self.with_scope(
            ScopeKind::Comprehension {
                kind,
                is_async: generators.iter().any(|clause| clause.is_async),
            },
            |visitor| {
                visitor.visit_expr(&first.target);
                for condition in &first.ifs {
                    visitor.visit_expr(condition);
                }
                for clause in rest {
                    visitor.visit_comprehension(clause);
                }
                visit_result(visitor);
            },
        );
    }
}

/// Find the first keyword-name error in CPython's outer-to-inner validation order.
fn invalid_call_keyword(
    arguments: &ast::Arguments,
    forbid_debug: bool,
) -> Option<(&str, TextRange)> {
    if arguments.keywords.len() < 2 {
        return arguments.keywords.first().and_then(|keyword| {
            keyword.arg.as_ref().and_then(|name| {
                (forbid_debug && name == "__debug__").then_some((name.as_str(), keyword.range))
            })
        });
    }
    let mut seen = FxHashMap::default();
    let mut repeated = None;
    // Reverse traversal preserves the next occurrence of each name without a quadratic scan.
    for keyword in arguments.keywords.iter().rev() {
        if let Some(name) = &keyword.arg {
            let next = seen.insert(name.as_str(), keyword.range);
            if forbid_debug && name == "__debug__" {
                repeated = Some((name.as_str(), keyword.range));
            } else if let Some(range) = next {
                repeated = Some((name.as_str(), range));
            }
        }
    }
    repeated
}

/// Follow CPython's pattern walk: structural subpatterns can match anything, but only the final
/// arm of an OR pattern may do so, and only when its enclosing pattern permits it.
fn unreachable_pattern(
    pattern: &Pattern,
    allow_irrefutable: bool,
) -> Option<ast::IrrefutablePattern> {
    match pattern {
        Pattern::MatchAs(as_pattern) => match &as_pattern.pattern {
            Some(pattern) => unreachable_pattern(pattern, allow_irrefutable),
            None if !allow_irrefutable => pattern.irrefutable_pattern(),
            None => None,
        },
        Pattern::MatchOr(pattern) => {
            pattern
                .patterns
                .iter()
                .enumerate()
                .find_map(|(index, arm)| {
                    unreachable_pattern(
                        arm,
                        allow_irrefutable && index + 1 == pattern.patterns.len(),
                    )
                })
        }
        Pattern::MatchSequence(pattern) => pattern
            .patterns
            .iter()
            .find_map(|pattern| unreachable_pattern(pattern, true)),
        Pattern::MatchMapping(pattern) => pattern
            .patterns
            .iter()
            .find_map(|pattern| unreachable_pattern(pattern, true)),
        Pattern::MatchClass(pattern) => pattern
            .arguments
            .patterns
            .iter()
            .chain(
                pattern
                    .arguments
                    .keywords
                    .iter()
                    .map(|keyword| &keyword.pattern),
            )
            .find_map(|pattern| unreachable_pattern(pattern, true)),
        Pattern::MatchValue(_) | Pattern::MatchSingleton(_) | Pattern::MatchStar(_) => None,
    }
}

impl<'ast, const PRUNE_STATEMENTS: bool, const FUTURE_ONLY: bool> Visitor<'ast>
    for Validator<'_, 'ast, PRUNE_STATEMENTS, FUTURE_ONLY>
{
    fn visit_stmt(&mut self, statement: &'ast Stmt) {
        if self.error.borrow().is_some() {
            return;
        }
        if FUTURE_ONLY {
            self.check_statement(statement);
            walk_stmt(self, statement);
            return;
        }
        if let Stmt::Match(match_statement) = statement {
            let numeric_duplicate =
                pattern_numeric::has_large_numeric_duplicate(match_statement, self.python_version);
            if numeric_duplicate
                || (self.may_have_debug_patterns
                    && pattern_debug::has_debug_pattern(match_statement))
            {
                self.lowering_numeric_error |= numeric_duplicate;
                self.visit_debug_match(statement, match_statement);
                return;
            }
        }
        let mut prechecked_match_cases = 0;
        match statement {
            Stmt::Expr(statement) => {
                self.record_bare_starred(&statement.value, BareStarredKind::Expression);
            }
            Stmt::AnnAssign(statement) => {
                if let Some(value) = &statement.value {
                    self.record_bare_starred(value, BareStarredKind::Expression);
                }
            }
            Stmt::Assign(statement) => {
                self.record_bare_starred(&statement.value, BareStarredKind::Expression);
            }
            Stmt::For(statement) => {
                self.record_bare_starred(&statement.iter, BareStarredKind::Expression);
                if statement.target.is_starred_expr() {
                    // Validate the iterable first even when the shared statement checker would
                    // report the direct target before visiting a nested iterable expression.
                    self.visit_expr(&statement.iter);
                    self.record_bare_starred(&statement.target, BareStarredKind::AssignmentTarget);
                }
            }
            Stmt::Global(_) | Stmt::Nonlocal(_) => self.has_declarations = true,
            _ => {}
        }
        // This precedes return-value checks and except* transfer checks, as in CPython.
        if !self.pre_lowering_only
            && let Stmt::Return(statement) = statement
            && statement.value.is_some()
            && matches!(
                self.scope().kind,
                ScopeKind::Function {
                    is_async_generator: true,
                    ..
                }
            )
        {
            self.report_semantic_error(SemanticSyntaxError {
                kind: SemanticSyntaxErrorKind::ReturnInGenerator,
                range: statement.range,
                python_version: self.python_version,
            });
            return;
        }
        // A loop contained within the handler can be exited without leaving except*.
        // Independent function and class scopes start without the enclosing boundary.
        if !self.pre_lowering_only
            && matches!(statement, Stmt::Break(_) | Stmt::Continue(_))
            && self.scope().except_star_loop_depth == Some(self.scope().loop_depth)
        {
            self.reject_except_star_transfer(statement);
            return;
        }
        // Ruff checks reachability across whole cases but does not reject unreachable arms of an
        // OR pattern. Walk both boundaries in CPython's order before checking binding differences.
        if !self.pre_lowering_only
            && let Stmt::Match(statement) = statement
        {
            self.visit_expr(&statement.subject);
            self.defer_pattern_reachability(statement);
            if let Some(pending) = self.pending_pattern.take() {
                for case in &statement.cases {
                    if case.pattern.range().contains_range(pending.pattern.range) {
                        break;
                    }
                    self.visit_match_case(case);
                    prechecked_match_cases += 1;
                }
                self.pending_pattern = Some(pending);
            }
        }
        if self.python_version == ast::PythonVersion::PY312
            && matches!(self.scope().kind, ScopeKind::Class)
            && let Some(error) = self.python_312_class_annotation_error(statement)
        {
            // Defaults and decorators are checked before entering the annotation scope.
            // Only revisit these eager expressions when the preflight found a restriction.
            // Their code-generation errors still follow the annotation's symbol-table error.
            let previous = std::mem::replace(&mut self.pre_lowering_only, true);
            match statement {
                Stmt::FunctionDef(function) => {
                    for parameter in function.parameters.iter_non_variadic_params() {
                        if let Some(default) = &parameter.default {
                            self.visit_expr(default);
                        }
                    }
                    for decorator in &function.decorator_list {
                        self.visit_decorator(decorator);
                    }
                }
                Stmt::ClassDef(class) => {
                    for decorator in &class.decorator_list {
                        self.visit_decorator(decorator);
                    }
                }
                _ => {}
            }
            self.pre_lowering_only = previous;
            if self.error.borrow().is_none() {
                *self.error.borrow_mut() = Some(error.into());
            }
            return;
        }
        let replay_class = !self.pre_lowering_only
            && self.class_lowering_target.is_some()
            && matches!(statement, Stmt::ClassDef(class)
                if self.class_lowering_depth > 0
                    || self.class_lowering_target.is_some_and(|range| class.range.contains_range(range)));
        let previous_class_header = self
            .checking_class_header
            .replace(matches!(statement, Stmt::ClassDef(_)));
        let previous_suppression = self.suppress_class_keyword.replace(replay_class);
        // Relative imports of a module named __future__ are ordinary imports. The shared
        // checker identifies directives by their module spelling, so hide that spelling here.
        if self.statement_needs_checker(statement) {
            let previous_match = self.checked_match;
            self.checked_match = match statement {
                Stmt::Match(statement) => Some(statement),
                _ => None,
            };
            self.check_statement(statement);
            self.checked_match = previous_match;
        }
        self.checking_class_header.set(previous_class_header);
        self.suppress_class_keyword.set(previous_suppression);
        if let Some(pending) = self.pending_pattern.take() {
            if self.error.borrow().is_none() && self.bare_starred.is_none() {
                self.lowering_pattern_error = true;
                let message = match pending.pattern.kind {
                    ast::IrrefutablePatternKind::Name(name) => {
                        format!("name capture '{name}' makes remaining patterns unreachable")
                    }
                    ast::IrrefutablePatternKind::Wildcard => {
                        "wildcard makes remaining patterns unreachable".to_owned()
                    }
                };
                *self.error.borrow_mut() = Some(
                    CompileError::InvalidPattern {
                        message,
                        range: pending.pattern.range,
                    }
                    .into(),
                );
            }
            if self.error.borrow().is_some() {
                return;
            }
        }
        match statement {
            Stmt::Assert(_) if self.optimization_level != OptimizationLevel::Zero => {
                // CPython visits assertions in the symbol table, then drops them before code
                // generation. In particular, yield errors disappear but duplicate parameters
                // and modern await / __debug__ assignment errors must still be reported.
                let previous = std::mem::replace(&mut self.pre_lowering_only, true);
                walk_stmt(self, statement);
                self.pre_lowering_only = previous;
            }
            Stmt::Match(statement) => {
                for case in statement.cases.iter().skip(prechecked_match_cases) {
                    self.visit_match_case(case);
                }
            }
            Stmt::AnnAssign(statement) => {
                if let Some(value) = &statement.value {
                    self.visit_expr(value);
                }
                self.visit_expr(&statement.target);
                // Local variable annotations and, from 3.14, complex variable annotations are
                // not compiled; their interpolations are never evaluated.
                let compiled = !self.in_function_scope()
                    && (statement.simple || self.python_version < ast::PythonVersion::PY314);
                if compiled
                    && !self.future_annotations
                    && !self.pre_lowering_only
                    && self.python_version >= ast::PythonVersion::PY314
                {
                    self.scope_mut()
                        .deferred_annotations
                        .push(&statement.annotation);
                    self.pre_lowering_only = true;
                    self.visit_annotation(&statement.annotation);
                    self.pre_lowering_only = false;
                } else {
                    self.with_bare_starred_check(compiled, |visitor| {
                        visitor.visit_annotation(&statement.annotation);
                    });
                }
            }
            Stmt::Assign(statement) => {
                // CPython compiles the right-hand side before any chained assignment target.
                self.visit_expr(&statement.value);
                for target in &statement.targets {
                    self.record_bare_starred(target, BareStarredKind::AssignmentTarget);
                    self.visit_expr(target);
                }
            }
            Stmt::AugAssign(statement) if self.python_version < ast::PythonVersion::PY314 => {
                // Legacy augmented attribute stores bypass the ordinary attribute-name check.
                // Their base expression and RHS still undergo normal validation.
                if let Expr::Attribute(attribute) = statement.target.as_ref() {
                    self.visit_expr(&attribute.value);
                } else {
                    self.visit_expr(&statement.target);
                }
                self.visit_expr(&statement.value);
            }
            Stmt::FunctionDef(function) => {
                for decorator in &function.decorator_list {
                    self.visit_decorator(decorator);
                }
                if let Some(params) = &function.type_params {
                    self.visit_type_params(params);
                }
                self.visit_parameters(&function.parameters);
                if let Some(returns) = &function.returns {
                    self.visit_annotation(returns);
                }
                // Before 3.14, symbol-table traversal can mark a sync function as a
                // coroutine from an assertion that optimization subsequently removes.
                let legacy_coroutine = !function.is_async
                    && self.may_have_legacy_coroutines
                    && super::source::function_has_elided_coroutine_assertion(&function.body);
                self.with_scope(
                    ScopeKind::Function {
                        is_async: function.is_async,
                        // Ruff's return checker skips eager nested headers and defaults.
                        is_async_generator: (function.is_async || legacy_coroutine)
                            && suite_contains_yield_in_function_scope(
                                &function.body,
                                !self.future_annotations
                                    && self.python_version < ast::PythonVersion::PY314,
                            ),
                        parameters: Some(&function.parameters),
                    },
                    |visitor| visitor.visit_scope_body(&function.body),
                );
            }
            Stmt::ClassDef(class) => {
                if replay_class {
                    self.visit_class_in_lowering_order(class);
                    return;
                }
                for decorator in &class.decorator_list {
                    self.visit_decorator(decorator);
                }
                if let Some(params) = &class.type_params {
                    self.with_private_context(
                        class.name.as_str(),
                        Some(FxHashSet::default()),
                        |visitor| {
                            for parameter in params.iter() {
                                // Generic class headers only mangle type parameters already
                                // declared when this bound or default is visited.
                                visitor
                                    .mangled_names
                                    .as_mut()
                                    .expect("generic headers have restricted name mangling")
                                    .insert(parameter.name().as_str());
                                visitor.visit_type_param(parameter);
                            }
                            if let Some(arguments) = &class.arguments {
                                visitor.visit_arguments(arguments);
                            }
                            visitor.mangled_names = None;
                            visitor.with_scope(ScopeKind::Class, |visitor| {
                                visitor.visit_scope_body(&class.body);
                            });
                        },
                    );
                } else {
                    if let Some(arguments) = &class.arguments {
                        self.visit_arguments(arguments);
                    }
                    self.with_private_context(class.name.as_str(), None, |visitor| {
                        visitor.with_scope(ScopeKind::Class, |visitor| {
                            visitor.visit_scope_body(&class.body);
                        });
                    });
                }
            }
            Stmt::For(statement) => {
                if !statement.target.is_starred_expr() {
                    self.visit_expr(&statement.iter);
                }
                self.visit_expr(&statement.target);
                self.scope_mut().loop_depth += 1;
                self.visit_body(&statement.body);
                self.scope_mut().loop_depth -= 1;
                self.visit_body(&statement.orelse);
            }
            Stmt::While(statement) => {
                self.visit_expr(&statement.test);
                self.scope_mut().loop_depth += 1;
                self.visit_body(&statement.body);
                self.scope_mut().loop_depth -= 1;
                self.visit_body(&statement.orelse);
            }
            Stmt::Return(_) => {
                // CPython validates the returned expression before unwinding the handler.
                walk_stmt(self, statement);
                if self.scope().except_star_loop_depth.is_some() {
                    self.reject_except_star_transfer(statement);
                }
            }
            Stmt::Try(try_statement) => {
                let previous = std::mem::replace(&mut self.scope_mut().in_try, true);
                if try_statement.is_star {
                    self.visit_body(&try_statement.body);
                    for ast::ExceptHandler::ExceptHandler(handler) in &try_statement.handlers {
                        if let Some(type_) = &handler.type_ {
                            self.visit_expr(type_);
                        }
                        let scope = self.scope_mut();
                        let previous = scope.except_star_loop_depth.replace(scope.loop_depth);
                        self.visit_body(&handler.body);
                        self.scope_mut().except_star_loop_depth = previous;
                    }
                    self.visit_body(&try_statement.orelse);
                    self.visit_body(&try_statement.finalbody);
                } else {
                    walk_stmt(self, statement);
                }
                self.scope_mut().in_try = previous;
            }
            _ => walk_stmt(self, statement),
        }
    }

    fn visit_expr(&mut self, expression: &'ast Expr) {
        if crate::stack_growth_required() {
            return crate::grow_stack(|| self.visit_expr(expression));
        }

        if FUTURE_ONLY {
            return;
        }
        // This adapter does not supply declarations to Ruff's global-order check. A bare name
        // therefore only needs checking when it assigns to or deletes `__debug__`. Ordinary
        // literals have no validation state; attribute chains check the target before their base.
        match expression {
            Expr::Name(name)
                if name.id.as_str() != "__debug__"
                    || !(name.ctx.is_store() || name.ctx.is_del()) =>
            {
                return;
            }
            Expr::StringLiteral(_)
            | Expr::BytesLiteral(_)
            | Expr::NumberLiteral(_)
            | Expr::BooleanLiteral(_)
            | Expr::NoneLiteral(_)
            | Expr::EllipsisLiteral(_) => return,
            Expr::Attribute(attribute) => {
                self.check_debug_write(attribute.attr.as_str(), attribute.ctx, attribute.range);
                let mut base = attribute.value.as_ref();
                while let Expr::Attribute(attribute) = base {
                    base = attribute.value.as_ref();
                }
                self.visit_expr(base);
                return;
            }
            _ => {}
        }
        if self.error.borrow().is_some() {
            return;
        }
        if let Expr::Call(call) = expression {
            self.check_call_keywords(&call.arguments);
            if self.error.borrow().is_some() {
                return;
            }
        }
        if self.comprehension_yield_operand
            && let Expr::Named(named) = expression
        {
            // Ruff scans a whole comprehension at entry. Release an observed named-expression
            // error only when the symbol-table walk actually reaches that expression.
            let deferred = {
                let mut frames = self.deferred_comprehension_errors.borrow_mut();
                let mut found = None;
                // CPython checks iterable restrictions, then iteration-variable conflicts in
                // surrounding comprehensions, before it reaches a containing class scope.
                'priority: for priority in 0..3 {
                    for frame in frames.iter_mut().rev() {
                        for range in [named.range, named.target.range()] {
                            if let Some(errors) = frame.get_mut(&range)
                                && let Some(index) = errors.iter().position(|error| {
                                    matches!(
                                        (&error.kind, priority),
                                        (SemanticSyntaxErrorKind::NamedExpressionInComprehensionIterable, 0)
                                            | (SemanticSyntaxErrorKind::ReboundComprehensionVariable, 1)
                                            | (SemanticSyntaxErrorKind::NamedExpressionInClassBodyComprehension, 2)
                                    )
                                })
                            {
                                found = Some(errors.remove(index));
                                break 'priority;
                            }
                        }
                    }
                }
                found
            };
            if let Some(error) = deferred {
                if matches!(
                    error.kind,
                    SemanticSyntaxErrorKind::ReboundComprehensionVariable
                ) && let Expr::Name(name) = named.target.as_ref()
                {
                    *self.error.borrow_mut() = Some(
                        CompileError::invalid_syntax(
                            format!(
                                "assignment expression cannot rebind comprehension iteration variable '{}'",
                                name.id
                            ),
                            error.range,
                        )
                        .into(),
                    );
                } else if matches!(
                    error.kind,
                    SemanticSyntaxErrorKind::NamedExpressionInClassBodyComprehension
                ) {
                    *self.error.borrow_mut() = Some(
                        CompileError::invalid_syntax(error.to_string(), named.target.range())
                            .into(),
                    );
                } else {
                    self.report_semantic_error(error);
                }
                if self.error.borrow().is_some() {
                    return;
                }
            }
        }
        let comprehension_yield = matches!(self.scope().kind, ScopeKind::Comprehension { .. })
            && matches!(expression, Expr::Yield(_) | Expr::YieldFrom(_));
        if comprehension_yield {
            let value = match expression {
                Expr::Yield(yield_) => yield_.value.as_deref(),
                Expr::YieldFrom(yield_from) => Some(yield_from.value.as_ref()),
                _ => unreachable!(),
            };
            if let Some(value) = value {
                // Symbol-table checks inside the operand precede the enclosing yield error.
                // Suppress later lowering errors while visiting the operand in that order.
                let previous_pre_lowering = std::mem::replace(&mut self.pre_lowering_only, true);
                let previous_operand =
                    std::mem::replace(&mut self.comprehension_yield_operand, true);
                self.visit_expr(value);
                self.comprehension_yield_operand = previous_operand;
                self.pre_lowering_only = previous_pre_lowering;
                if self.error.borrow().is_some() {
                    return;
                }
            }
        }
        // Lambda defaults execute in the enclosing scope before its parameters are checked.
        if self.comprehension_yield_operand
            && let Expr::Lambda(lambda) = expression
            && let Some(parameters) = &lambda.parameters
        {
            walk_parameters(self, parameters);
            if self.error.borrow().is_some() {
                return;
            }
        }
        let check_expression = match expression {
            // These are the only remaining variants checked by the pinned Ruff visitor. Its
            // tuple/list check applies only to assignment targets; a lambda without parameters
            // has no identifiers or duplicates to check. All other expressions still recurse.
            Expr::Name(_)
            | Expr::ListComp(_)
            | Expr::SetComp(_)
            | Expr::DictComp(_)
            | Expr::Generator(_)
            | Expr::Yield(_)
            | Expr::YieldFrom(_)
            | Expr::Await(_) => true,
            Expr::Tuple(tuple) => tuple.ctx.is_store(),
            Expr::List(list) => list.ctx.is_store(),
            Expr::Lambda(lambda) => lambda.parameters.is_some(),
            Expr::BoolOp(_)
            | Expr::Named(_)
            | Expr::BinOp(_)
            | Expr::UnaryOp(_)
            | Expr::If(_)
            | Expr::Dict(_)
            | Expr::Set(_)
            | Expr::Compare(_)
            | Expr::Call(_)
            | Expr::StringLiteral(_)
            | Expr::BytesLiteral(_)
            | Expr::NumberLiteral(_)
            | Expr::BooleanLiteral(_)
            | Expr::NoneLiteral(_)
            | Expr::EllipsisLiteral(_)
            | Expr::FString(_)
            | Expr::TString(_)
            | Expr::Attribute(_)
            | Expr::Subscript(_)
            | Expr::Starred(_)
            | Expr::Slice(_)
            | Expr::IpyEscapeCommand(_) => false,
        };
        let deferred_frame = self.comprehension_yield_operand
            && matches!(
                expression,
                Expr::ListComp(_) | Expr::SetComp(_) | Expr::DictComp(_) | Expr::Generator(_)
            );
        if deferred_frame {
            self.deferred_comprehension_errors
                .borrow_mut()
                .push(FxHashMap::default());
        }
        if check_expression {
            if matches!(
                expression,
                Expr::ListComp(_) | Expr::SetComp(_) | Expr::DictComp(_) | Expr::Generator(_)
            ) {
                let mut depth = crate::stack::ExpressionDepth::default();
                depth.visit_expr(expression);
                let previous =
                    std::mem::replace(&mut self.collecting_comprehension_errors, deferred_frame);
                self.with_checker(|checker, context| {
                    crate::stack::with_depth(depth.maximum(), || {
                        checker.visit_expr(expression, context);
                    });
                });
                self.collecting_comprehension_errors = previous;
            } else {
                let previous =
                    std::mem::replace(&mut self.checking_comprehension_yield, comprehension_yield);
                self.with_checker(|checker, context| checker.visit_expr(expression, context));
                self.checking_comprehension_yield = previous;
            }
        }
        if comprehension_yield {
            return;
        }
        match expression {
            Expr::Lambda(lambda) => {
                if let Some(parameters) = &lambda.parameters {
                    if self.comprehension_yield_operand {
                        self.validate_private_parameters(parameters);
                    } else {
                        self.visit_parameters(parameters);
                    }
                }
                self.with_scope(
                    ScopeKind::Function {
                        is_async: false,
                        is_async_generator: false,
                        parameters: lambda.parameters.as_deref(),
                    },
                    |visitor| visitor.visit_expr(&lambda.body),
                );
            }
            Expr::Dict(dict) if self.comprehension_yield_operand => {
                // The symbol table visits all dictionary keys before any values.
                for item in &dict.items {
                    if let Some(key) = &item.key {
                        self.visit_expr(key);
                    }
                }
                for item in &dict.items {
                    self.visit_expr(&item.value);
                }
            }
            Expr::ListComp(ast::ExprListComp {
                elt, generators, ..
            }) => {
                self.comprehension(generators, ComprehensionKind::List, |visitor| {
                    visitor.visit_expr(elt);
                });
            }
            Expr::SetComp(ast::ExprSetComp {
                elt, generators, ..
            }) => {
                self.comprehension(generators, ComprehensionKind::Set, |visitor| {
                    visitor.visit_expr(elt);
                });
            }
            Expr::Generator(ast::ExprGenerator {
                elt, generators, ..
            }) => {
                self.comprehension(generators, ComprehensionKind::Generator, |visitor| {
                    visitor.visit_expr(elt);
                });
            }
            Expr::DictComp(ast::ExprDictComp {
                key,
                value,
                generators,
                ..
            }) => {
                self.comprehension(generators, ComprehensionKind::Dict, |visitor| {
                    if visitor.comprehension_yield_operand {
                        visitor.visit_expr(value);
                        if let Some(key) = key {
                            visitor.visit_expr(key);
                        }
                    } else if key.as_deref().is_some_and(direct_yield_with_simple_operand)
                        && direct_yield_with_simple_operand(value)
                    {
                        // Outside an operand replay, only simple direct yields are reordered.
                        visitor.visit_expr(value);
                        visitor.visit_expr(key.as_deref().expect("key was checked"));
                    } else {
                        if let Some(key) = key {
                            visitor.visit_expr(key);
                        }
                        visitor.visit_expr(value);
                    }
                });
            }
            _ => walk_expr(self, expression),
        }
        if deferred_frame {
            self.deferred_comprehension_errors.borrow_mut().pop();
        }
    }

    fn visit_parameters(&mut self, parameters: &'ast ast::Parameters) {
        if FUTURE_ONLY {
            return;
        }
        self.validate_private_parameters(parameters);
        walk_parameters(self, parameters);
    }

    fn visit_pattern(&mut self, pattern: &'ast Pattern) {
        if let Pattern::MatchClass(class) = pattern {
            for keyword in &class.arguments.keywords {
                self.check_debug_write(
                    keyword.attr.as_str(),
                    ast::ExprContext::Store,
                    keyword.pattern.range(),
                );
            }
        }
        walk_pattern(self, pattern);
    }

    fn visit_arguments(&mut self, arguments: &'ast ast::Arguments) {
        self.check_call_keywords(arguments);
        for argument in &arguments.args {
            self.visit_expr(argument);
        }
        // Native checks explicit keyword names before walking any keyword values.
        for keyword in &arguments.keywords {
            if let Some(name) = &keyword.arg {
                self.check_debug_write(name.as_str(), ast::ExprContext::Store, keyword.range);
            }
        }
        for keyword in &arguments.keywords {
            self.visit_keyword(keyword);
        }
    }

    fn visit_annotation(&mut self, annotation: &'ast Expr) {
        self.with_bare_starred_check(!self.future_annotations, |visitor| {
            visitor.visit_expr(annotation);
        });
    }

    fn visit_with_item(&mut self, item: &'ast ast::WithItem) {
        self.visit_expr(&item.context_expr);
        if let Some(target) = &item.optional_vars {
            self.record_bare_starred(target, BareStarredKind::AssignmentTarget);
            self.visit_expr(target);
        }
    }

    fn visit_interpolated_string_element(&mut self, element: &'ast ast::InterpolatedStringElement) {
        if let ast::InterpolatedStringElement::Interpolation(interpolation) = element {
            self.record_bare_starred(&interpolation.expression, BareStarredKind::Expression);
        }
        walk_interpolated_string_element(self, element);
    }
}

/// Identify direct yields whose operands cannot contain earlier syntax errors.
fn direct_yield_with_simple_operand(expression: &Expr) -> bool {
    let value = match expression {
        Expr::Yield(yield_) => yield_.value.as_deref(),
        Expr::YieldFrom(yield_from) => Some(yield_from.value.as_ref()),
        _ => return false,
    };
    value.is_none_or(|value| {
        matches!(
            value,
            Expr::Name(_)
                | Expr::StringLiteral(_)
                | Expr::BytesLiteral(_)
                | Expr::NumberLiteral(_)
                | Expr::BooleanLiteral(_)
                | Expr::NoneLiteral(_)
                | Expr::EllipsisLiteral(_)
        )
    })
}

impl<const PRUNE_STATEMENTS: bool, const FUTURE_ONLY: bool> SemanticSyntaxContext
    for Validator<'_, '_, PRUNE_STATEMENTS, FUTURE_ONLY>
{
    fn future_annotations_or_stub(&self) -> bool {
        self.future_annotations
    }
    fn python_version(&self) -> ast::PythonVersion {
        self.python_version
    }
    fn source(&self) -> &str {
        self.source
    }

    fn lazy_import_context(&self) -> Option<LazyImportContext> {
        match self.scope().kind {
            ScopeKind::Function { .. } => Some(LazyImportContext::Function),
            ScopeKind::Class => Some(LazyImportContext::Class),
            _ => self
                .scope()
                .in_try
                .then_some(LazyImportContext::TryExceptBlocks),
        }
    }

    // Declaration ordering and enclosing-name resolution remain outside this AST-only
    // adapter, as in ty. These hooks do not claim to validate those restrictions.
    fn global(&self, _name: &str) -> Option<TextRange> {
        None
    }
    fn has_nonlocal_binding(&self, _name: &str) -> bool {
        true
    }

    fn in_async_context(&self) -> bool {
        self.scopes
            .iter()
            .rev()
            .find_map(|scope| match scope.kind {
                ScopeKind::Function { is_async, .. } => Some(is_async),
                ScopeKind::Module | ScopeKind::Class => Some(false),
                ScopeKind::Comprehension { .. } => None,
            })
            .unwrap_or(false)
    }

    fn in_await_allowed_context(&self) -> bool {
        self.in_async_context() || self.in_generator_context() || self.in_function_scope()
    }

    fn in_yield_allowed_context(&self) -> bool {
        self.in_function_scope()
    }

    fn in_sync_comprehension(&self) -> bool {
        for scope in self.scopes.iter().rev() {
            match scope.kind {
                ScopeKind::Comprehension {
                    is_async: false, ..
                } => return true,
                ScopeKind::Comprehension { is_async: true, .. } => {}
                _ => break,
            }
        }
        false
    }

    fn in_class_body_comprehension(&self) -> bool {
        self.scopes
            .iter()
            .rev()
            .find_map(|scope| match scope.kind {
                ScopeKind::Comprehension { .. } => None,
                ScopeKind::Class => Some(true),
                _ => Some(false),
            })
            .unwrap_or(false)
    }

    fn in_module_scope(&self) -> bool {
        matches!(self.scope().kind, ScopeKind::Module)
    }
    fn in_function_scope(&self) -> bool {
        matches!(self.scope().kind, ScopeKind::Function { .. })
    }
    fn in_generator_context(&self) -> bool {
        for scope in self.scopes.iter().rev() {
            match scope.kind {
                ScopeKind::Comprehension {
                    kind: ComprehensionKind::Generator,
                    ..
                } => return true,
                ScopeKind::Comprehension { .. } => {}
                _ => break,
            }
        }
        false
    }
    fn in_notebook(&self) -> bool {
        false
    }
    fn in_loop_context(&self) -> bool {
        self.scope().loop_depth > 0
    }
    fn is_bound_parameter(&self, name: &str) -> bool {
        matches!(self.scope().kind, ScopeKind::Function { parameters: Some(parameters), .. } if parameters.includes(name))
    }

    fn report_semantic_error(&self, error: SemanticSyntaxError) {
        use SemanticSyntaxErrorKind as Kind;
        if let Some(errors) = self.collected_match_errors.borrow_mut().as_mut() {
            errors.push(error);
            return;
        }
        if self.checking_comprehension_yield && matches!(error.kind, Kind::InvalidStarExpression) {
            return;
        }
        if self.comprehension_yield_operand
            && matches!(self.scope().kind, ScopeKind::Comprehension { .. })
            && (matches!(&error.kind, Kind::YieldOutsideFunction(kind) if kind.is_await())
                || matches!(error.kind, Kind::AwaitOutsideAsyncFunction(_)))
        {
            return;
        }
        if FUTURE_ONLY
            && !matches!(
                &error.kind,
                Kind::FutureFeatureNotDefined(_) | Kind::LateFutureImport | Kind::LazyFutureImport
            )
        {
            return;
        }
        if self.checking_class_header.get()
            && self.suppress_class_keyword.get()
            && matches!(error.kind, Kind::DuplicateKeywordArgument(_))
        {
            // The replay checks this class call after its body, as CPython lowering does.
            return;
        }
        if self.collecting_comprehension_errors
            && matches!(
                error.kind,
                Kind::ReboundComprehensionVariable
                    | Kind::NamedExpressionInComprehensionIterable
                    | Kind::NamedExpressionInClassBodyComprehension
            )
        {
            self.deferred_comprehension_errors
                .borrow_mut()
                .last_mut()
                .expect("comprehension error frame")
                .entry(error.range)
                .or_default()
                .push(error);
            return;
        }
        // The declaration pass checks complete symbol histories and places errors on the full
        // CPython statement, including parameters and module-level nonlocals.
        if matches!(
            error.kind,
            Kind::GlobalParameter(_)
                | Kind::NonlocalParameter(_)
                | Kind::NonlocalDeclarationAtModuleLevel
        ) {
            return;
        }
        if let Some(pending) = &self.pending_pattern
            && !pending.prefers(&error)
        {
            return;
        }
        // Ruff reports this on statement entry and only for a sole assignment target. Check every
        // direct target ourselves after visiting the right-hand side, in CPython compilation order.
        if matches!(error.kind, Kind::SingleStarredAssignment) {
            return;
        }
        if let Kind::InvalidExpression(kind, _) = &error.kind
            && self.escapes_annotation_scope(error.range, kind)
        {
            return;
        }
        if self.bare_starred.is_some() || self.pre_lowering_only {
            // Bare stars fail during code generation. Keep walking for errors from earlier
            // compiler phases; 3.14 moved await and writes to __debug__ into such a phase.
            let code_generation_error = match &error.kind {
                Kind::LateFutureImport | Kind::FutureFeatureNotDefined(_) => {
                    self.python_version < ast::PythonVersion::PY314
                }
                Kind::ReturnInGenerator => self.pre_lowering_only,
                Kind::BreakOutsideLoop
                | Kind::ContinueOutsideLoop
                | Kind::ReturnOutsideFunction
                | Kind::YieldFromInAsyncFunction
                | Kind::InvalidStarExpression
                | Kind::DifferentMatchPatternBindings
                | Kind::MultipleCaseAssignment(_)
                | Kind::MultipleStarredNamesInSequencePattern
                | Kind::IrrefutableCasePattern(_)
                | Kind::DuplicateMatchKey(_)
                | Kind::DuplicateKeywordArgument(_)
                | Kind::DuplicateMatchClassAttribute(_) => true,
                Kind::YieldOutsideFunction(kind) => {
                    if kind.is_await() {
                        self.python_version < ast::PythonVersion::PY314
                    } else {
                        // Comprehension yields fail in the symbol-table pass, before bare stars
                        // and yields outside a function fail during code generation.
                        !matches!(self.scope().kind, ScopeKind::Comprehension { .. })
                    }
                }
                Kind::AwaitOutsideAsyncFunction(_) | Kind::WriteToDebug(_) => {
                    self.python_version < ast::PythonVersion::PY314
                }
                _ => false,
            };
            if code_generation_error {
                return;
            }
        }
        if matches!(error.kind, Kind::DuplicateMatchKey(_))
            && self.error.borrow().is_none()
            && self.false_surrogate_mapping_duplicate(error.range)
        {
            return;
        }
        let mut reported = self.error.borrow_mut();
        // The shared checker reports an unknown feature before it reports that the
        // same import is misplaced. Native compilation checks placement first, but
        // an earlier statement's error must still retain its priority.
        let later_future_in_same_statement = matches!(error.kind, Kind::LateFutureImport)
            && self
                .reported_future_feature
                .get()
                .is_some_and(|range| error.range.contains_range(range));
        // Ruff reports an unknown future name before its enclosing late import. During this
        // symbol-order replay CPython rejects the late import first, even for an unknown name.
        let replaces_unknown_future = self.numeric_symbol_replay
            && matches!(error.kind, Kind::LateFutureImport)
            && reported
                .as_ref()
                .and_then(|error| error.error.range())
                .is_some_and(|range| range != error.range && error.range.contains_range(range));
        let replaces_pending_debug = self.pending_pattern.is_some()
            && matches!(error.kind, Kind::WriteToDebug(_))
            && !matches!(
                reported.as_ref().map(|error| &error.error),
                Some(CompileError::InvalidSyntax { .. })
            );
        if reported.is_some()
            && !(later_future_in_same_statement
                || replaces_unknown_future
                || replaces_pending_debug)
        {
            return;
        }
        if matches!(error.kind, Kind::FutureFeatureNotDefined(_)) {
            self.reported_future_feature.set(Some(error.range));
        }
        if self.checking_class_header.get()
            && matches!(error.kind, Kind::DuplicateKeywordArgument(_))
        {
            self.lowering_keyword_error.set(true);
        }
        // Preserve the existing public diagnostics for checks previously performed in lowering.
        if matches!(error.kind, Kind::DuplicateMatchKey(_))
            && let Some(diagnostic) = mapping_diagnostic::find(
                self.source,
                self.body,
                error.range,
                self.python_version,
                self.mapping_key_int_max_str_digits,
            )
        {
            *reported = Some(diagnostic.into());
            return;
        }
        *reported = Some(ValidationError::from_semantic(
            &error,
            self.python_version,
            self.scope().kind,
            self.comprehension_yield_operand,
            self.checked_type_params,
        ));
    }
}

#[cfg(test)]
mod tests {
    use ruff_python_parser::parse_module;

    use super::{
        simple_comprehension_module, validate, validate_with_optimization,
        validate_without_statement_pruning,
    };
    use crate::{
        CompileError, CompileOptions, OptimizationLevel, PythonVersion, compile_with_options,
    };

    const TARGETS: [PythonVersion; 4] = [
        PythonVersion::Py312,
        PythonVersion::Py313,
        PythonVersion::Py314,
        PythonVersion::Py315,
    ];

    #[test]
    fn optimized_assertions_keep_symbol_table_errors() {
        for python_version in TARGETS {
            for optimization_level in [OptimizationLevel::One, OptimizationLevel::Two] {
                for (source, valid) in [
                    ("assert (yield 1)", true),
                    ("async def f():\n assert (yield from [])", true),
                    ("assert await value", python_version < PythonVersion::Py314),
                    (
                        "assert (__debug__ := False)",
                        python_version < PythonVersion::Py314,
                    ),
                    ("assert (lambda x, x: x)", false),
                    ("async def f():\n assert (yield 1)\n return 2", false),
                    ("assert value\nfrom __future__ import annotations", false),
                    ("if __debug__:\n yield 1", false),
                    ("if not __debug__:\n yield 1", false),
                ] {
                    let parsed = parse_module(source).unwrap();
                    let result = validate_with_optimization(
                        source,
                        &parsed.syntax().body,
                        python_version,
                        optimization_level,
                    );
                    assert_eq!(
                        result.is_ok(),
                        valid,
                        "{python_version} -O{optimization_level}: {source}: {result:?}"
                    );
                }
            }
        }
    }

    #[test]
    fn stripped_docstrings_skip_native_utf8_cleanup() {
        for python_version in TARGETS {
            for source in ["'\\ud800'", "def f():\n '\\ud800'", "class C:\n '\\ud800'"] {
                let parsed = parse_module(source).unwrap();
                for optimization_level in [OptimizationLevel::One, OptimizationLevel::Two] {
                    let result = validate_with_optimization(
                        source,
                        &parsed.syntax().body,
                        python_version,
                        optimization_level,
                    );
                    assert_eq!(
                        result.is_ok(),
                        optimization_level == OptimizationLevel::Two
                            || python_version == PythonVersion::Py312,
                        "{python_version} -O{optimization_level}: {source}: {result:?}"
                    );
                }
            }
        }
    }

    #[test]
    fn duplicate_type_parameter_diagnostics_include_normalized_name() {
        for python_version in TARGETS {
            for (source, name, highlighted) in [
                ("class Example[T, T]: pass", "T", "T"),
                ("def function[T, *T](): pass", "T", "*T"),
                ("type Alias[T, **T] = int", "T", "**T"),
                ("class Example[K, \u{212A}]: pass", "K", "\u{212A}"),
                ("class Example[T, T: int]: pass", "T", "T: int"),
                ("class Outer:\n class Inner[__T, __T]: pass", "__T", "__T"),
            ] {
                let options = CompileOptions {
                    python_version,
                    ..CompileOptions::default()
                };
                let error = compile_with_options(source, "duplicate.py", &options).unwrap_err();
                let CompileError::InvalidSyntax { message, range } = error else {
                    panic!("unexpected error for {python_version}: {source:?}: {error}");
                };
                assert_eq!(
                    message,
                    format!("duplicate type parameter '{name}'"),
                    "{python_version}: {source:?}"
                );
                assert_eq!(&source[range], highlighted, "{python_version}: {source:?}");
            }
        }
    }

    #[test]
    fn unknown_future_feature_reports_native_message() {
        for (source, expected, span) in [
            (
                "from __future__ import undefined_feature\n",
                "future feature undefined_feature is not defined",
                "undefined_feature",
            ),
            (
                "from __future__ import annotations, undefined_feature\n",
                "future feature undefined_feature is not defined",
                "undefined_feature",
            ),
            (
                "from __future__ import undefined_feature, another_feature\n",
                "future feature undefined_feature is not defined",
                "undefined_feature",
            ),
            (
                "from __future__ import undefined_feature as alias\n",
                "future feature undefined_feature is not defined",
                "undefined_feature as alias",
            ),
            ("from __future__ import braces\n", "not a chance", "braces"),
            (
                "from __future__ import braces as alias\n",
                "not a chance",
                "braces as alias",
            ),
            (
                "from __future__ import ｂｒａｃｅｓ\n",
                "not a chance",
                "ｂｒａｃｅｓ",
            ),
        ] {
            let parsed = parse_module(source).unwrap();
            for python_version in TARGETS {
                let error = validate(source, &parsed.syntax().body, python_version).unwrap_err();
                let CompileError::InvalidSyntax { message, range } = error else {
                    panic!("unexpected {python_version} error for {source:?}: {error}");
                };
                assert_eq!(message, expected, "{python_version}: {source:?}");
                assert_eq!(&source[range], span, "{python_version}: {source:?}");
            }
        }
    }

    #[test]
    fn unknown_future_feature_names_are_truncated_as_utf8() {
        for (name, legacy_prefix, modern_prefix) in [
            ("a".repeat(101), "a".repeat(100), "a".repeat(100)),
            ("é".repeat(101), "é".repeat(50), "é".repeat(50)),
            (
                format!("{}ézzz", "a".repeat(99)),
                format!("{}�", "a".repeat(99)),
                "a".repeat(99),
            ),
            (
                format!("{}𐐀zzz", "a".repeat(98)),
                format!("{}�", "a".repeat(98)),
                "a".repeat(98),
            ),
            (
                format!("{}ﬃzzz", "a".repeat(99)),
                format!("{}f", "a".repeat(99)),
                format!("{}f", "a".repeat(99)),
            ),
        ] {
            let source = format!("from __future__ import {name}\n");
            let parsed = parse_module(&source).unwrap();
            for python_version in TARGETS {
                let error = validate(&source, &parsed.syntax().body, python_version).unwrap_err();
                let CompileError::InvalidSyntax { message, range } = error else {
                    panic!("unexpected {python_version} error for {source:?}: {error}");
                };
                let prefix =
                    if matches!(python_version, PythonVersion::Py312 | PythonVersion::Py313) {
                        &legacy_prefix
                    } else {
                        &modern_prefix
                    };
                assert_eq!(
                    message,
                    format!("future feature {prefix} is not defined"),
                    "{python_version}: {source:?}"
                );
                assert_eq!(&source[range], name, "{python_version}: {source:?}");
            }
        }
    }

    #[test]
    fn late_future_import_reports_native_message() {
        for (source, span) in [
            (
                "x = 1\nfrom __future__ import annotations\n",
                "from __future__ import annotations",
            ),
            (
                "x = 1\nfrom __future__ import generator_stop, annotations\n",
                "from __future__ import generator_stop, annotations",
            ),
            (
                "if False:\n    from __future__ import annotations\n",
                "from __future__ import annotations",
            ),
        ] {
            let parsed = parse_module(source).unwrap();
            for python_version in TARGETS {
                let error = validate(source, &parsed.syntax().body, python_version).unwrap_err();
                let CompileError::InvalidSyntax { message, range } = error else {
                    panic!("unexpected {python_version} error for {source:?}: {error}");
                };
                assert_eq!(
                    message, "from __future__ imports must occur at the beginning of the file",
                    "{python_version}: {source:?}"
                );
                assert_eq!(&source[range], span, "{python_version}: {source:?}");
            }
        }
    }

    #[test]
    fn declaration_checks_find_nested_statements_and_win_over_lowering_errors() {
        let valid = "'global nonlocal'\n# global value; nonlocal missing\nclass C:\n def method(self):\n  return 'nonglobal', 'nonlocal'\n";
        let parsed = parse_module(valid).unwrap();
        for python_version in TARGETS {
            validate(valid, &parsed.syntax().body, python_version).unwrap();
        }

        for (source, message) in [
            (
                "if True:\n class C:\n  def method(self):\n   if True:\n    nonlocal missing\n",
                "no binding for nonlocal 'missing' found",
            ),
            (
                "*unpacked\nnonlocal missing\n",
                "nonlocal declaration not allowed at module level",
            ),
            (
                "match subject:\n case _: pass\n case 1: pass\nnonlocal missing\n",
                "nonlocal declaration not allowed at module level",
            ),
        ] {
            let parsed = parse_module(source).unwrap();
            for python_version in TARGETS {
                let error = validate(source, &parsed.syntax().body, python_version).unwrap_err();
                let CompileError::InvalidSyntax {
                    message: actual,
                    range,
                } = error
                else {
                    panic!("unexpected error for {python_version}: {source:?}: {error}");
                };
                assert_eq!(actual, message, "{python_version}: {source:?}");
                assert_eq!(&source[range], "nonlocal missing");
            }
        }
    }

    #[test]
    fn many_distinct_surrogate_mapping_keys_remain_distinct() {
        let keys = (0..1024)
            .map(|index| {
                format!(
                    "'\\u{:04x}\\u{:04x}': _",
                    0xd800 + index / 32,
                    0xd800 + index % 32
                )
            })
            .collect::<Vec<_>>()
            .join(", ");
        for (suffix, duplicate) in [("", false), (", '\\ud800\\ud800': _", true)] {
            let source = format!("match subject:\n    case {{{keys}{suffix}}}: pass\n");
            let parsed = parse_module(&source).unwrap();
            for version in TARGETS {
                let result = validate(&source, &parsed.syntax().body, version);
                if duplicate {
                    assert!(result.unwrap_err().to_string().contains("duplicate key"));
                } else {
                    assert!(result.is_ok(), "{version}: {result:?}");
                }
            }
        }
    }

    #[test]
    fn surrogate_mapping_keys_in_many_cases_remain_independent() {
        let cases = (0..512)
            .map(|_| "    case {'\\ud800': _, '\\ud801': _}: pass\n")
            .collect::<String>();
        let source = format!("match subject:\n{cases}");
        let parsed = parse_module(&source).unwrap();
        for version in TARGETS {
            let result = validate(&source, &parsed.syntax().body, version);
            assert!(result.is_ok(), "{version}: {result:?}");
        }
    }

    #[test]
    fn comprehension_replay_rejects_uncertified_module_shapes() {
        for source in [
            "async def f(x, x):\n pass\n",
            "async def f(K, \u{212A}):\n pass\n",
            "async def f(__debug__):\n pass\n",
            "async def f(x: int):\n pass\n",
            "async def f(x=call()):\n pass\n",
            "async def f():\n __debug__ = 1\n",
            "async def f():\n obj.attr = 1\n",
            "async def f():\n obj[0] = 1\n",
            "return 1\n",
        ] {
            let parsed = parse_module(source).unwrap();
            assert!(
                !simple_comprehension_module(&parsed.syntax().body),
                "{source}"
            );
        }
    }

    #[test]
    fn bare_starred_errors_keep_cpython_validation_phase_order() {
        for python_version in TARGETS {
            let modern = python_version >= PythonVersion::Py314;
            for (source, message, highlighted) in [
                ("*first\n(yield second)\n", "starred", "*first"),
                ("(yield first)\n*second\n", "yield", "yield first"),
                ("*(yield item)\n", "starred", "*(yield item)"),
                (
                    "*first\nawait second\n",
                    if modern { "await" } else { "starred" },
                    if modern { "await second" } else { "*first" },
                ),
                (
                    "*((yield first), (await second))\n",
                    if modern { "await" } else { "starred" },
                    if modern {
                        "await second"
                    } else {
                        "*((yield first), (await second))"
                    },
                ),
                (
                    "*first\n(__debug__ := second)\n",
                    if modern { "__debug__" } else { "starred" },
                    if modern { "__debug__" } else { "*first" },
                ),
                ("first = *second = f'{*items}'\n", "starred", "*items"),
            ] {
                let parsed = parse_module(source).unwrap();
                let error = validate(source, &parsed.syntax().body, python_version).unwrap_err();
                let CompileError::InvalidSyntax {
                    message: actual,
                    range,
                } = error
                else {
                    panic!("unexpected error for {python_version}: {source:?}: {error}");
                };
                assert!(
                    actual.contains(message),
                    "{python_version}: {source:?}: {actual}"
                );
                assert_eq!(&source[range], highlighted, "{python_version}: {source:?}");
            }

            let source = "*first\n[x for x in (bound := values)]\n";
            let parsed = parse_module(source).unwrap();
            let error = validate(source, &parsed.syntax().body, python_version).unwrap_err();
            assert!(
                error.to_string().contains("assignment expression"),
                "{python_version}: {error}",
            );
        }
    }

    #[test]
    fn leaf_expressions_keep_debug_and_interpolated_expression_checks() {
        let valid = "ordinary = 1\ntext = 'left' 'right'\nraw = b'left' b'right'\nvalues = (ordinary, True, False, None, ..., 1.2, 3j, __debug__)\ndel ordinary\n";
        let parsed = parse_module(valid).unwrap();
        for python_version in TARGETS {
            validate(valid, &parsed.syntax().body, python_version).unwrap();
        }

        for (source, message) in [
            ("__debug__ = 1", "__debug__"),
            ("del __debug__", "__debug__"),
            ("(ordinary, __debug__) = (1, 2)", "__debug__"),
            ("value = f'{(__debug__ := 1)}'", "__debug__"),
            ("value = f'{(yield ordinary)}'", "yield"),
        ] {
            let parsed = parse_module(source).unwrap();
            for python_version in TARGETS {
                let error = validate(source, &parsed.syntax().body, python_version).unwrap_err();
                assert!(
                    error.to_string().contains(message),
                    "{python_version:?}: {source}: {error}",
                );
            }
        }
    }

    #[test]
    fn skipped_expression_wrappers_still_check_descendants_and_assignment_targets() {
        let valid = "left, right = (), ()\nvalues = (*left, *right), [*left, *right]\ndel (left, right)\nempty = lambda: __debug__\n";
        let parsed = parse_module(valid).unwrap();
        for python_version in TARGETS {
            validate(valid, &parsed.syntax().body, python_version).unwrap();
        }

        for (source, message) in [
            ("value = consume((yield item))", "yield"),
            ("value = (yield item).attribute", "yield"),
            ("value = not (other or 1 + (yield item))", "yield"),
            ("value = values[0:(yield item)]", "yield"),
            ("value = {'key': {item, (yield item)}}", "yield"),
            (
                "value = (bound := (yield item)) if flag else other",
                "yield",
            ),
            ("value = [(yield item) == other]", "yield"),
            ("value = consume((await item))", "await"),
            ("(*left, *right) = values", "starred"),
            ("[*left, *right] = values", "starred"),
            (
                "value = consume([item for item in (bound := values)])",
                "assignment expression",
            ),
        ] {
            let parsed = parse_module(source).unwrap();
            for python_version in TARGETS {
                let error = validate(source, &parsed.syntax().body, python_version).unwrap_err();
                assert!(
                    error.to_string().to_ascii_lowercase().contains(message),
                    "{python_version:?}: {source}: {error}",
                );
            }
        }
    }

    #[test]
    fn attribute_chains_keep_the_first_error_at_the_terminal_expression() {
        let valid = "normal.first.second.third = 1\ndel normal.first.second.third\nvalue = __debug__.first.second.third\nvalue = (lambda: 1).first.second.third\n";
        let parsed = parse_module(valid).unwrap();
        for python_version in TARGETS {
            validate(valid, &parsed.syntax().body, python_version).unwrap();
        }

        for (source, message, expected) in [
            (
                "value = ((yield first).a.b.c, (await second).d.e.f)",
                "'yield' outside function",
                "yield first",
            ),
            (
                "value = ((await first).a.b.c, (yield second).d.e.f)",
                "'await' outside function",
                "await first",
            ),
            (
                "value = ((__debug__ := first).a.b.c, (yield second).d.e.f)",
                "cannot assign to __debug__",
                "__debug__",
            ),
            (
                "value = ((yield first).a.b.c, (__debug__ := second).d.e.f)",
                "'yield' outside function",
                "yield first",
            ),
        ] {
            let parsed = parse_module(source).unwrap();
            for python_version in TARGETS {
                let error = validate(source, &parsed.syntax().body, python_version).unwrap_err();
                let CompileError::InvalidSyntax {
                    message: actual,
                    range,
                } = error
                else {
                    panic!("unexpected error for {source}: {error}");
                };
                assert_eq!(actual, message, "{python_version:?}: {source}");
                assert_eq!(
                    &source[usize::from(range.start())..usize::from(range.end())],
                    expected,
                    "{python_version:?}: {source}",
                );
            }
        }
    }

    #[test]
    fn pruned_statement_checks_match_the_standalone_checker_for_every_target() {
        for source in [
            "",
            "'module docstring'\nfrom __future__ import annotations\nfrom __future__ import division\nvalue = 1",
            "from __future__ import annotations\nfrom __future__ import division\nvalue = 1",
            "'first string'\n'second string'\nfrom __future__ import annotations",
            "from __future__ import annotations\n'not a docstring'\nfrom __future__ import division",
            "from .__future__ import annotations\nfrom __future__ import division",
            "'doc'\nfrom .__future__ import annotations\nfrom __future__ import division",
            "pass\nfrom __future__ import annotations",
            "if flag:\n 'nested string'\n from __future__ import annotations",
            "def ordinary():\n 'function docstring'\n from __future__ import annotations",
            "class Ordinary:\n 'class docstring'\n from __future__ import annotations",
            "lazy from __future__ import annotations\nfrom __future__ import division",
            "value = 0\nordinary = other\nordinary += 1\ndel ordinary\nassert True\nif flag: pass\nwhile False: pass",
            "value = 0\nordinary = (yield first)\n(__debug__ := second)",
            "value = 0\n__debug__ = other\n(yield second)",
            "value = 0\n*ordinary = other\n(yield second)",
            "value = 0\nordinary = *other\n(yield second)",
            "value = 0\n(*left, *right) = other\n(yield second)",
            "value = 0\nordinary += (yield first)\n(__debug__ := second)",
            "value = 0\ndel __debug__\n(yield second)",
            "value = 0\nassert (yield first)\n(__debug__ := second)",
            "value = 0\nif (yield first): pass\n(__debug__ := second)",
            "value = 0\nwhile (yield first): pass\n(__debug__ := second)",
            "value = 0\nraise (yield first)\n(__debug__ := second)",
            "value = 0\nwith context as __debug__: pass\n(yield second)",
            "value = 0\nasync with context: pass\n(yield second)",
            "value = 0\nfor __debug__ in other: pass\n(yield second)",
            "value = 0\nfor *ordinary in other: pass\n(yield second)",
            "value = 0\nfor ordinary in *other: pass\n(yield second)",
            "value = 0\nasync for ordinary in other: pass\n(yield second)",
            "value = 0\nreturn (yield first)\n(__debug__ := second)",
            "value = 0\nbreak\n(__debug__ := second)",
            "value = 0\ncontinue\n(__debug__ := second)",
            "def ordinary():\n for name in values:\n  if name: continue\n  break\n with context: pass\n return 1",
            "def ordinary():\n return *values\n (__debug__ := second)",
            "def ordinary():\n return (__debug__ := first)\n (__debug__ := second)",
            "def ordinary():\n while flag:\n  pass\n else:\n  break",
            "def ordinary():\n try: pass\n except* Error:\n  for value in values: break\n  return (__debug__ := first)",
            "async def ordinary():\n yield 1\n return (await first)",
            "def ordinary(value):\n pass\n global value\n (__debug__ := second)",
            "value = 0\ntry: pass\nexcept Error as __debug__: pass\n(yield second)",
        ] {
            let parsed = parse_module(source).unwrap_or_else(|error| panic!("{source}: {error}"));
            for python_version in TARGETS {
                let pruned = validate(source, &parsed.syntax().body, python_version);
                let reference = validate_without_statement_pruning(
                    source,
                    &parsed.syntax().body,
                    python_version,
                );
                assert_eq!(
                    format!("{pruned:?}"),
                    format!("{reference:?}"),
                    "{python_version:?}: {source}",
                );
            }
        }
    }

    #[test]
    fn non_mangling_parameters_keep_ordinary_duplicate_checks() {
        for source in [
            "class C:\n def f(__private): pass",
            "class C:\n def f(__dunder__, _C__dunder__, ordinary): pass",
            "class C:\n value = lambda __dunder__, _C__dunder__: None",
            "class ___:\n def f(__private, ____private, ordinary): pass",
            "class C[T]((lambda __private, _C__private: object)(0, 0)): pass",
        ] {
            let parsed = parse_module(source).unwrap();
            for python_version in TARGETS {
                validate(source, &parsed.syntax().body, python_version)
                    .unwrap_or_else(|error| panic!("{python_version:?}: {source}: {error}"));
            }
        }

        for source in [
            "class C:\n def f(ordinary, ordinary): pass",
            "class C:\n value = lambda ordinary, ordinary: None",
            "class C:\n def f(__dunder__, __dunder__): pass",
            "class ___:\n def f(__private, __private): pass",
        ] {
            let parsed = parse_module(source).unwrap();
            for python_version in TARGETS {
                let error = validate(source, &parsed.syntax().body, python_version).unwrap_err();
                assert!(
                    error.to_string().to_ascii_lowercase().contains("duplicate"),
                    "{python_version:?}: {source}: {error}",
                );
            }
        }
    }

    #[test]
    fn private_parameter_aliases_are_rejected_in_their_lexical_class() {
        for (source, duplicate) in [
            ("class C:\n def f(__x, _C__x): pass", "_C__x"),
            ("class C:\n def f(_C__x, __x): pass", "__x"),
            ("class C:\n def f(__x, /, _C__x): pass", "_C__x"),
            ("class C:\n def f(__x, *, _C__x): pass", "_C__x"),
            ("class C:\n def f(*__x, _C__x): pass", "__x"),
            ("class C:\n def f(*__x, **_C__x): pass", "_C__x"),
            ("class C:\n f = lambda __x, _C__x: None", "_C__x"),
            ("class C:\n def f():\n  def g(__x, _C__x): pass", "_C__x"),
            ("class C:\n def f[T](__x, _C__x): pass", "_C__x"),
            ("class __C:\n def f(__x, _C__x): pass", "_C__x"),
            ("class C:\n class D:\n  def f(__x, _D__x): pass", "_D__x"),
            (
                "class C:\n class D: pass\n def f(__x, _C__x): pass",
                "_C__x",
            ),
            (
                "class C:\n class D((lambda __x, _C__x: object)(0, 0)): pass",
                "_C__x",
            ),
            (
                "class C:\n @(lambda __x, _C__x: object)\n class D[T]: pass",
                "_C__x",
            ),
            (
                "class C[__x]((lambda __x, _C__x: object)(0, 0)): pass",
                "_C__x",
            ),
            (
                "class C[__x, T: (lambda __x, _C__x: object)]: pass",
                "_C__x",
            ),
        ] {
            let parsed = parse_module(source).unwrap();
            for python_version in TARGETS {
                let error = validate(source, &parsed.syntax().body, python_version).unwrap_err();
                let CompileError::InvalidSyntax { message, range } = error else {
                    panic!("unexpected error for {source}: {error}");
                };
                let kind = if python_version == PythonVersion::Py315 {
                    "parameter"
                } else {
                    "argument"
                };
                assert_eq!(
                    message,
                    format!("duplicate {kind} '{duplicate}' in function definition"),
                    "{python_version:?}: {source}",
                );
                assert_eq!(
                    &source[usize::from(range.start())..usize::from(range.end())],
                    duplicate,
                );
            }
        }
    }

    #[test]
    fn parameter_mangling_respects_class_headers_and_context_restoration() {
        for source in [
            "def f(__x, _C__x): pass",
            "class C: pass\ndef f(__x, _C__x): pass",
            "class ___:\n def f(__x, ____x): pass",
            "class C:\n class D:\n  def f(__x, _C__x): pass",
            "@(lambda __x, _C__x: object)\nclass C[T]: pass",
            "class C((lambda __x, _C__x: object)(0, 0)): pass",
            "class C[T]((lambda __x, _C__x: object)(0, 0)): pass",
            "class C[T: (lambda __x, _C__x: object), __x]: pass",
            "class C[__x: (lambda __y, _C__y: object)]: pass",
        ] {
            let parsed = parse_module(source).unwrap();
            for python_version in TARGETS {
                validate(source, &parsed.syntax().body, python_version)
                    .unwrap_or_else(|error| panic!("{python_version:?}: {source}: {error}"));
            }
        }
    }
}
