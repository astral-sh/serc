use std::borrow::Cow;
use std::cell::{Cell, OnceCell};
use std::collections::{BTreeMap, BTreeSet};
use std::hash::Hasher;
use std::marker::PhantomData;
use std::rc::Rc;

use hashbrown::HashTable;
use ruff_index::{IndexVec, newtype_index};
use ruff_python_ast::name::Name;
use ruff_python_ast::visitor::{Visitor, walk_expr, walk_pattern, walk_stmt};
use ruff_python_ast::{Expr, ExprContext, Pattern, Stmt, StmtClassDef, StmtFunctionDef, TypeParam};
use ruff_text_size::{Ranged, TextSize};
use rustc_hash::{FxHashMap, FxHashSet, FxHasher};
use smallvec::SmallVec;

use crate::target::code_flags::{CO_FUTURE_ANNOTATIONS, CO_FUTURE_BARRY_AS_BDFL};
use crate::{CompileError, PythonVersion};

use super::source::SourceAnalysis;
use super::symbol::mangle_name;
use super::{Compiler, SHADOWED_SUPER_SENTINEL, Scope, comprehension_parts};

#[cfg(test)]
thread_local! {
    static FORCE_GENERIC_SUSPENSION_SEARCH: Cell<bool> = const { Cell::new(false) };
    static FORCE_FULL_LOWERED_SCOPES: Cell<bool> = const { Cell::new(false) };
}

impl Compiler<'_> {
    pub(super) fn scope_arena(&self) -> &ScopeArena {
        &self.context.scopes
    }

    /// Whether a generator's enclosing lexical scopes bind a name before the module.
    pub(super) fn generator_has_enclosing_binding(&self, name: &str) -> bool {
        if self.can_provide_closure(name) {
            return true;
        }
        let arena = self.scope_arena();
        let name_id = arena
            .names
            .get(&self.mangled_name(name))
            .unwrap_or_else(|| self.required_name_id(name));
        // Lambda scopes are synthesized during lowering and do not have their own arena node.
        if self.unit.qualified_name.ends_with("<lambda>")
            && matches!(&self.unit.scope, Scope::Function { indices, .. } if indices.contains_key(&name_id))
        {
            return true;
        }
        arena.function_or_enclosing_binds(self.unit.scope_id, name_id)
    }

    /// Synthetic class-visible annotation scopes retain their enclosing class's scope ID.
    pub(super) fn class_scope_declares_global(&self, name: NameId) -> bool {
        self.scope_arena()
            .class(self.unit.scope_id)
            .is_some_and(|plan| {
                if !plan.globals.is_empty() {
                    let name = self.mangled_name_cow(self.resolve_name(name));
                    plan.canonical_globals
                        .contains(&self.required_name_id(&name))
                } else {
                    plan.globals.contains(&name)
                }
            })
    }

    /// Class namespace bindings exclude the temporary targets of inlined comprehensions.
    pub(super) fn class_scope_binds_name(&self, name: &str) -> bool {
        let arena = self.scope_arena();
        let name = mangle_name(name, self.unit.private_name.as_deref());
        arena.names.get(name.as_ref()).is_some_and(|name| {
            arena
                .class(self.unit.scope_id)
                .is_some_and(|plan| plan.namespace_bindings.contains(&name))
        })
    }

    /// Direct annotation references honor class bindings before enclosing closure cells.
    pub(super) fn class_scope_shadows_annotation_name(&self, name: NameId) -> bool {
        if self.unit.mangled_names.is_some() {
            // Generic class headers can use a different private-name context than their
            // enclosing class. Compare the emitted spelling with that class's bindings.
            let name = self.mangled_name_cow(self.resolve_name(name));
            return self
                .class_scope_shadows_unmangled_annotation_name(self.required_name_id(&name));
        }
        self.scope_arena()
            .class(self.unit.scope_id)
            .is_some_and(|plan| plan.globals.contains(&name) || plan.bound_names.contains(&name))
    }

    /// Compare an already resolved header spelling with emitted class bindings.
    pub(super) fn class_scope_shadows_unmangled_annotation_name(&self, name: NameId) -> bool {
        self.scope_arena()
            .class(self.unit.scope_id)
            .is_some_and(|plan| plan.canonical_annotation_shadows.contains(&name))
    }

    pub(super) fn function_scope_id(
        &self,
        definition: &StmtFunctionDef,
    ) -> Result<ScopeId, CompileError> {
        self.scope_arena()
            .child(self.unit.scope_id, ScopeOrigin::function(definition))
            .ok_or_else(|| {
                CompileError::Internal(format!(
                    "missing scope plan for nested function `{}`",
                    definition.name
                ))
            })
    }

    fn class_scope_id(&self, definition: &StmtClassDef) -> Result<ScopeId, CompileError> {
        self.scope_arena()
            .child(self.unit.scope_id, ScopeOrigin::class(definition))
            .ok_or_else(|| {
                CompileError::Internal(format!(
                    "missing scope plan for nested class `{}`",
                    definition.name
                ))
            })
    }

    pub(super) fn resolved_function_plan(
        &self,
        definition: &StmtFunctionDef,
    ) -> Result<(ScopeId, LoweringFunctionPlan), CompileError> {
        let scope_id = self.function_scope_id(definition)?;
        let arena = self.scope_arena();
        let source_plan = arena
            .function(scope_id)
            .ok_or_else(|| CompileError::Internal("function scope has no plan".to_string()))?;
        let mut plan = source_plan.clone_for_lowering();
        for &(name, canonical, comprehension_cell) in &source_plan.deferred_comprehension_globals {
            if arena.enclosing_function_binds(scope_id, canonical)
                || self.symbols.active_temporaries.contains(name)
            {
                continue;
            }
            let mut aliases = vec![name];
            for &(alias, original) in &plan.local_aliases {
                if alias == name || original == name {
                    aliases.extend([alias, original]);
                }
            }
            for alias in aliases {
                plan.comprehension_shadowed_targets.insert(alias);
                if !comprehension_cell {
                    plan.cellvars.remove(&alias);
                    plan.inlined_comprehension_cellvars.remove(&alias);
                }
                plan.mark_global(alias);
            }
        }
        plan.resolve_required(&arena.names, |name| match &self.unit.scope {
            Scope::Class { free_indices, .. } => {
                arena.names.get("__class__") == Some(name)
                    || matches!(
                        arena.names.resolve(name),
                        "__classdict__" | "__conditional_annotations__"
                    ) && self.is_cell_id(name)
                    || free_indices.contains_key(&name)
            }
            Scope::Module | Scope::Function { .. } => self.can_provide_closure_id(name),
        });
        if arena.deferred_annotations || definition.type_params.is_some() {
            #[expect(
                clippy::iter_over_hash_type,
                reason = "Annotation captures are inserted in lexical order."
            )]
            for &name in &source_plan.annotation_references {
                let captures_name = match &self.unit.scope {
                    // Method annotation thunks are created by the class body and can capture the
                    // class body's free variables, but not arbitrary class-local bindings.
                    Scope::Class { free_indices, .. } => {
                        free_indices.contains_key(&name)
                            || arena.names.get("__class__") == Some(name)
                                && self.is_cell_id(name)
                                && (arena
                                    .class(self.unit.scope_id)
                                    .is_some_and(|plan| !plan.bound_names.contains(&name))
                                    || function_annotation_expressions(definition).any(
                                        |annotation| {
                                            annotation_nested_required_names(annotation)
                                                .contains("__class__")
                                        },
                                    ))
                    }
                    Scope::Module | Scope::Function { .. } => self.can_provide_closure_id(name),
                };
                if captures_name {
                    plan.insert_annotation_freevar(&arena.names, name);
                }
            }
        }
        let mut plan = plan.into_lowering_plan();
        plan.free_aliases = self.coalesce_private_freevars(&mut plan.freevars);
        Ok((scope_id, plan))
    }

    /// Coalesce captured spellings only after closure eligibility has been resolved.
    pub(super) fn coalesce_private_freevars(
        &self,
        freevars: &mut Vec<NameId>,
    ) -> Vec<(NameId, NameId)> {
        if self.unit.private_name.is_none() || self.unit.mangled_names.is_some() {
            return Vec::new();
        }
        freevars.sort_by_cached_key(|name| {
            let raw = self.resolve_name(*name);
            let emitted = self.mangled_name_cow(raw);
            let is_alias = raw != emitted;
            (emitted, is_alias)
        });
        let mut emitted_names = FxHashMap::default();
        let mut aliases = Vec::new();
        freevars.retain(|name| {
            let emitted = self.mangled_name_cow(self.resolve_name(*name));
            if let Some(&original) = emitted_names.get(&emitted) {
                aliases.push((*name, original));
                false
            } else {
                emitted_names.insert(emitted, *name);
                true
            }
        });
        aliases
    }

    pub(super) fn class_plan(
        &self,
        definition: &StmtClassDef,
    ) -> Result<(ScopeId, LoweringClassPlan), CompileError> {
        let scope_id = self.class_scope_id(definition)?;
        let arena = self.scope_arena();
        let plan = arena
            .class(scope_id)
            .ok_or_else(|| CompileError::Internal("class scope has no plan".to_string()))?
            .lowering_plan();
        Ok((scope_id, plan))
    }
}

#[newtype_index]
pub(super) struct NameId;

impl From<NameId> for crate::code_object::MetadataId {
    fn from(id: NameId) -> Self {
        Self::from_u32(id.as_u32())
    }
}

const SCOPE_SEED_NAMES: [&str; 26] = [
    SHADOWED_SUPER_SENTINEL,
    "",
    ".0",
    ".defaults",
    ".format",
    ".generic_base",
    ".kwdefaults",
    ".type_params",
    "__class__",
    "__classdict__",
    "__classcell__",
    "__classdictcell__",
    "__conditional_annotations__",
    "__annotate__",
    "__annotate_func__",
    "__annotations__",
    "__doc__",
    "__firstlineno__",
    "__module__",
    "__name__",
    "__qualname__",
    "__static_attributes__",
    "__type_params__",
    "format",
    "join",
    "super",
];

#[derive(Debug, Default)]
pub(super) struct NameInterner {
    seed_names: &'static [&'static str],
    names: Vec<Name>,
    reverse: HashTable<NameId>,
    short_names: ShortNameCache,
}

/// The immutable value-to-ID index retained after lowering finishes.
/// Unlike the compiler's short-name cache, this lookup has no interior mutation.
#[derive(Debug)]
pub(crate) struct MarshalNameLookup {
    seed_names: &'static [&'static str],
    names: Vec<Name>,
    reverse: HashTable<NameId>,
}

impl MarshalNameLookup {
    pub(crate) fn len(&self) -> usize {
        self.seed_names.len() + self.names.len()
    }

    pub(crate) fn get(&self, name: &str) -> Option<crate::code_object::MetadataId> {
        if !self.seed_names.is_empty()
            && let Some(id) = NameInterner::seed_id(name)
        {
            return Some(id.into());
        }
        self.reverse
            .find(NameInterner::hash(name), |id| {
                self.names[id.index() - self.seed_names.len()] == name
            })
            .copied()
            .map(Into::into)
    }
}

const NAME_CACHE_BITS: u32 = 6;
const NAME_CACHE_SIZE: usize = 1 << NAME_CACHE_BITS;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ShortNameKey {
    packed: u64,
    length: u8,
}

impl ShortNameKey {
    #[inline]
    fn new(name: &str) -> Option<Self> {
        let bytes = name.as_bytes();
        let length = bytes.len();
        let packed = match length {
            1..=3 => {
                u64::from(bytes[0])
                    | (u64::from(bytes[length / 2]) << 8)
                    | (u64::from(bytes[length - 1]) << 16)
            }
            4..=8 => {
                u64::from(u32::from_ne_bytes(bytes[..4].try_into().unwrap()))
                    | (u64::from(u32::from_ne_bytes(bytes[length - 4..].try_into().unwrap())) << 32)
            }
            _ => return None,
        };
        Some(Self {
            packed,
            length: u8::try_from(length).unwrap(),
        })
    }

    #[inline]
    fn slot(self) -> usize {
        let mixed = (self.packed ^ u64::from(self.length).wrapping_mul(0x517c_c1b7_2722_0a95))
            .wrapping_mul(0x9e37_79b9_7f4a_7c15);
        usize::try_from(mixed >> (64 - NAME_CACHE_BITS)).unwrap()
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct MediumNameKey {
    first: u64,
    last: u64,
    length: u8,
}

impl MediumNameKey {
    #[inline]
    fn new(name: &str) -> Option<Self> {
        let bytes = name.as_bytes();
        let length = bytes.len();
        if !(9..=16).contains(&length) {
            return None;
        }
        let first = u64::from_ne_bytes(bytes[..8].try_into().unwrap());
        let last = u64::from_ne_bytes(bytes[length - 8..].try_into().unwrap());
        Some(Self {
            first,
            last,
            length: u8::try_from(length).unwrap(),
        })
    }

    #[inline]
    fn slot(self) -> usize {
        let mixed = self.first
            ^ self.last.rotate_left(37)
            ^ u64::from(self.length).wrapping_mul(0x517c_c1b7_2722_0a95);
        usize::try_from(mixed.wrapping_mul(0x9e37_79b9_7f4a_7c15) >> (64 - NAME_CACHE_BITS))
            .unwrap()
    }
}

/// Remembers exact spellings without hashing or probing the full interner again.
#[derive(Debug, Default)]
struct ShortNameCache(OnceCell<Box<NameCaches>>);

#[derive(Debug)]
struct NameCaches {
    short: [Cell<ShortNameEntry>; NAME_CACHE_SIZE],
    medium: OnceCell<Box<[Cell<MediumNameEntry>; NAME_CACHE_SIZE]>>,
}

#[derive(Clone, Copy, Debug)]
struct ShortNameEntry {
    packed: u64,
    id: Option<NameId>,
    length: u8,
}

#[derive(Clone, Copy, Debug)]
struct MediumNameEntry {
    first: u64,
    last: u64,
    id: Option<NameId>,
    length: u8,
}

impl Default for NameCaches {
    fn default() -> Self {
        Self {
            short: [const {
                Cell::new(ShortNameEntry {
                    packed: 0,
                    id: None,
                    length: 0,
                })
            }; NAME_CACHE_SIZE],
            medium: OnceCell::new(),
        }
    }
}

impl ShortNameCache {
    #[inline]
    fn get(&self, key: ShortNameKey) -> Option<NameId> {
        let entry = self.0.get()?.short[key.slot()].get();
        if entry.packed == key.packed && entry.length == key.length {
            entry.id
        } else {
            None
        }
    }

    #[inline]
    fn insert(&self, key: ShortNameKey, id: NameId) {
        self.0.get_or_init(Box::default).short[key.slot()].set(ShortNameEntry {
            packed: key.packed,
            id: Some(id),
            length: key.length,
        });
    }

    #[inline]
    fn get_medium(&self, key: MediumNameKey) -> Option<NameId> {
        let entry = self.0.get()?.medium.get()?[key.slot()].get();
        if entry.first == key.first && entry.last == key.last && entry.length == key.length {
            entry.id
        } else {
            None
        }
    }

    #[inline]
    fn insert_medium(&self, key: MediumNameKey, id: NameId) {
        let entries = self.0.get_or_init(Box::default).medium.get_or_init(|| {
            Box::new(
                [const {
                    Cell::new(MediumNameEntry {
                        first: 0,
                        last: 0,
                        id: None,
                        length: 0,
                    })
                }; NAME_CACHE_SIZE],
            )
        });
        entries[key.slot()].set(MediumNameEntry {
            first: key.first,
            last: key.last,
            id: Some(id),
            length: key.length,
        });
    }
}

#[derive(Clone, Debug, Default)]
pub(super) struct NameSet {
    // The last word, when present, is nonzero.
    words: Vec<u64>,
    aliases: Option<Rc<[(NameId, NameId)]>>,
}

impl NameSet {
    /// Raw private spellings share one symbol in an optimized function scope.
    pub(super) fn with_aliases(mut self, aliases: Option<&Rc<[(NameId, NameId)]>>) -> Self {
        let Some(aliases) = aliases else {
            return self;
        };
        let names = self.iter_unordered().collect::<Vec<_>>();
        self.words.clear();
        self.aliases = Some(Rc::clone(aliases));
        self.extend(names);
        self
    }

    pub(super) fn with_aliases_from(self, names: &Self) -> Self {
        self.with_aliases(names.aliases.as_ref())
    }

    fn canonical(&self, name: NameId) -> NameId {
        self.aliases
            .as_deref()
            .and_then(|aliases| aliases.iter().find(|(alias, _)| *alias == name))
            .map_or(name, |(_, original)| *original)
    }

    pub(super) fn contains(&self, name: NameId) -> bool {
        let index = self.canonical(name).index();
        self.words
            .get(index / u64::BITS as usize)
            .is_some_and(|word| word & (1 << (index % u64::BITS as usize)) != 0)
    }

    pub(super) fn is_empty(&self) -> bool {
        self.words.is_empty()
    }

    pub(super) fn insert(&mut self, name: NameId) -> bool {
        let index = self.canonical(name).index();
        let word_index = index / u64::BITS as usize;
        if word_index >= self.words.len() {
            self.words.resize(word_index + 1, 0);
        }
        let bit = 1 << (index % u64::BITS as usize);
        let inserted = self.words[word_index] & bit == 0;
        self.words[word_index] |= bit;
        inserted
    }

    pub(super) fn remove(&mut self, name: NameId) -> bool {
        let index = self.canonical(name).index();
        let word_index = index / u64::BITS as usize;
        let word_count = self.words.len();
        let Some(word) = self.words.get_mut(word_index) else {
            return false;
        };
        let bit = 1 << (index % u64::BITS as usize);
        let removed = *word & bit != 0;
        *word &= !bit;
        if *word == 0 && word_index + 1 == word_count {
            while self.words.last() == Some(&0) {
                self.words.pop();
            }
        }
        removed
    }

    pub(super) fn iter_unordered(&self) -> impl Iterator<Item = NameId> + '_ {
        self.words
            .iter()
            .enumerate()
            .flat_map(|(word_index, &word)| {
                let mut remaining = word;
                std::iter::from_fn(move || {
                    if remaining == 0 {
                        return None;
                    }
                    let bit = remaining.trailing_zeros();
                    remaining &= remaining - 1;
                    Some(NameId::from_usize(
                        word_index * u64::BITS as usize + bit as usize,
                    ))
                })
            })
    }
}

impl Extend<NameId> for NameSet {
    fn extend<T: IntoIterator<Item = NameId>>(&mut self, iter: T) {
        for name in iter {
            self.insert(name);
        }
    }
}

impl FromIterator<NameId> for NameSet {
    fn from_iter<T: IntoIterator<Item = NameId>>(iter: T) -> Self {
        let mut names = Self::default();
        names.extend(iter);
        names
    }
}

impl NameInterner {
    pub(super) fn into_marshal_lookup(self) -> MarshalNameLookup {
        MarshalNameLookup {
            seed_names: self.seed_names,
            names: self.names,
            reverse: self.reverse,
        }
    }

    fn seeded() -> Self {
        Self {
            seed_names: &SCOPE_SEED_NAMES,
            ..Self::default()
        }
    }

    fn seed_id(name: &str) -> Option<NameId> {
        let bytes = name.as_bytes();
        let index = match bytes.first() {
            None => 1,
            Some(b'\0') if name == SHADOWED_SUPER_SENTINEL => 0,
            Some(b'.') => match name {
                ".0" => 2,
                ".defaults" => 3,
                ".format" => 4,
                ".generic_base" => 5,
                ".kwdefaults" => 6,
                ".type_params" => 7,
                _ => return None,
            },
            Some(b'_') if bytes.get(1) == Some(&b'_') => match name {
                "__class__" => 8,
                "__classdict__" => 9,
                "__classcell__" => 10,
                "__classdictcell__" => 11,
                "__conditional_annotations__" => 12,
                "__annotate__" => 13,
                "__annotate_func__" => 14,
                "__annotations__" => 15,
                "__doc__" => 16,
                "__firstlineno__" => 17,
                "__module__" => 18,
                "__name__" => 19,
                "__qualname__" => 20,
                "__static_attributes__" => 21,
                "__type_params__" => 22,
                _ => return None,
            },
            Some(b'f') if name == "format" => 23,
            Some(b'j') if name == "join" => 24,
            Some(b's') if name == "super" => 25,
            _ => return None,
        };
        Some(NameId::from_usize(index))
    }

    pub(super) fn intern(&mut self, name: &str) -> NameId {
        if let Some(id) = self.get(name) {
            return id;
        }
        self.insert(Name::new(name))
    }

    fn intern_name(&mut self, name: &Name, spelling: &str) -> NameId {
        debug_assert_eq!(name.as_str(), spelling);
        if let Some(id) = self.get(spelling) {
            return id;
        }
        self.insert(name.clone())
    }

    fn intern_owned(&mut self, name: String) -> NameId {
        if let Some(id) = self.get(&name) {
            return id;
        }
        self.insert(Name::from(name))
    }

    /// Stores dynamic spellings once; seed IDs resolve from the static table.
    fn insert(&mut self, name: Name) -> NameId {
        let seed_count = self.seed_names.len();
        let id = NameId::from_usize(seed_count + self.names.len());
        self.reverse.insert_unique(Self::hash(&name), id, |id| {
            Self::hash(&self.names[id.index() - seed_count])
        });
        if let Some(key) = ShortNameKey::new(&name) {
            self.short_names.insert(key, id);
        } else if let Some(key) = MediumNameKey::new(&name) {
            self.short_names.insert_medium(key, id);
        }
        self.names.push(name);
        id
    }

    pub(super) fn get(&self, name: &str) -> Option<NameId> {
        // Before the first dynamic insertion, only static seeds can match.
        if self.reverse.is_empty() {
            return self.get_uncached(name);
        }
        if let Some(key) = ShortNameKey::new(name) {
            if let Some(id) = self.short_names.get(key) {
                return Some(id);
            }
        } else if let Some(key) = MediumNameKey::new(name) {
            if let Some(id) = self.short_names.get_medium(key) {
                return Some(id);
            }
        } else {
            return self.get_uncached(name);
        }
        self.get_and_cache(name)
    }

    // Keep cache population out of the cache-hit path's stack frame.
    #[inline(never)]
    fn get_and_cache(&self, name: &str) -> Option<NameId> {
        let id = self.get_uncached(name)?;
        if let Some(key) = ShortNameKey::new(name) {
            self.short_names.insert(key, id);
        } else if let Some(key) = MediumNameKey::new(name) {
            self.short_names.insert_medium(key, id);
        }
        Some(id)
    }

    fn get_uncached(&self, name: &str) -> Option<NameId> {
        if !self.seed_names.is_empty()
            && let Some(id) = Self::seed_id(name)
        {
            return Some(id);
        }
        if self.reverse.is_empty() {
            return None;
        }
        self.reverse
            .find(Self::hash(name), |id| {
                self.names[id.index() - self.seed_names.len()] == name
            })
            .copied()
    }

    fn hash(name: &str) -> u64 {
        let mut hasher = FxHasher::default();
        hasher.write(name.as_bytes());
        hasher.finish()
    }

    fn intern_set(&mut self, names: impl IntoIterator<Item = String>) -> FxHashSet<NameId> {
        names
            .into_iter()
            .map(|name| self.intern_owned(name))
            .collect()
    }

    pub(super) fn resolve(&self, id: NameId) -> &str {
        let index = id.index();
        if let Some(name) = self.seed_names.get(index) {
            name
        } else {
            &self.names[index - self.seed_names.len()]
        }
    }

    /// Retains a spelling without copying a heap-backed name's contents.
    #[inline]
    pub(super) fn clone_name(&self, id: NameId) -> Name {
        let index = id.index();
        if let Some(name) = self.seed_names.get(index) {
            Name::new_static(name)
        } else {
            self.names[index - self.seed_names.len()].clone()
        }
    }

    pub(super) fn len(&self) -> usize {
        self.seed_names.len() + self.names.len()
    }

    pub(super) fn insert_lexical(&self, names: &mut Vec<NameId>, id: NameId) {
        let spelling = self.resolve(id);
        match names.binary_search_by(|candidate| self.resolve(*candidate).cmp(spelling)) {
            Ok(_) => {}
            Err(index) => names.insert(index, id),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum AssertionMode {
    Keep,
    Elide,
}

#[derive(Clone, Debug, Default)]
pub(super) struct FunctionPlan {
    pub(super) locals: Vec<NameId>,
    pub(super) local_aliases: Vec<(NameId, NameId)>,
    /// Function bindings, excluding temporary comprehension targets.
    pub(super) lexical_bindings: FxHashSet<NameId>,
    /// Comprehension targets whose independent references may resolve globally.
    pub(super) deferred_comprehension_globals: Vec<(NameId, NameId, bool)>,
    pub(super) cell_sort_names: FxHashMap<NameId, String>,
    pub(super) globals: FxHashSet<NameId>,
    pub(super) annotation_references: FxHashSet<NameId>,
    pub(super) cellvars: FxHashSet<NameId>,
    pub(super) inlined_comprehension_cellvars: FxHashSet<NameId>,
    pub(super) freevars: Vec<NameId>,
    pub(super) annotation_freevars: Vec<NameId>,
    pub(super) comprehension_shadowed_targets: FxHashSet<NameId>,
    pub(super) required: FxHashSet<NameId>,
    pub(super) type_parameter_names: FxHashSet<NameId>,
}

// These facts share the same current-scope traversal boundary. Named function and class bodies
// belong to their own `ScopeArena` nodes; only their headers contribute facts to the parent.
#[derive(Debug, Default)]
pub(super) struct ScopeBodyFacts {
    pub(super) globals: FxHashSet<String>,
    pub(super) nonlocals: FxHashSet<String>,
    pub(super) references: FxHashSet<String>,
    outside_inlined_comprehension_references: FxHashSet<String>,
    outside_inlined_comprehension_requirements: FxHashSet<String>,
    later_comprehension_references: FxHashSet<String>,
    class_inlined_comprehension_references: FxHashSet<String>,
    explicit_dunder_class_reference: bool,
    pub(super) nested_lambda_requirements: BTreeSet<String>,
    pub(super) nested_generator_requirements: BTreeSet<String>,
    pub(super) nested_annotation_scope_requirements: BTreeSet<String>,
    unmangled_class_header_requirements: BTreeSet<String>,
    unmangled_class_header_captures: BTreeSet<String>,
    nested_annotation_class_closure: bool,
    annotation_class_reference: bool,
    annotation_comprehension_requirements: AnnotationComprehensionRequirements,
    pub(super) generator_named_targets: FxHashSet<String>,
    pub(super) inlined_comprehension_cellvars: FxHashSet<String>,
    pub(super) has_function_definition: bool,
    pub(super) has_generic_definition: bool,
    pub(super) has_type_alias: bool,
    pub(super) has_annotations: bool,
    has_assertions: bool,
    has_inlined_comprehension: bool,
    local_annotation_references: BTreeSet<String>,
    local_annotation_bindings: FxHashSet<String>,
    local_annotation_cellvars: FxHashSet<String>,
}

/// Separate storage is needed only while pending private declarations can make
/// emitted names differ from the frozen symbol table. Canonical header scopes
/// use the ordinary function layout without changing their capture analysis.
#[derive(Clone, Debug, Default)]
pub(super) struct HeaderLocalStoragePlan {
    /// Physical fast-local names in emission order, including frozen parameter names.
    pub(super) fast_locals: Vec<NameId>,
    /// Comprehension declaration symbols and the names of their save/restore slots.
    ///
    /// A later private type parameter can have a raw declaration symbol and a
    /// mangled save slot. Distinct symbols can also save the same physical slot.
    pub(super) comprehension_slots: Vec<(NameId, NameId)>,
    /// Additional physical cells created for comprehension save slots.
    ///
    /// These cells do not introduce declaration symbols or closure bindings.
    pub(super) cellvars: FxHashSet<NameId>,
}

#[derive(Clone, Debug, Default)]
pub(super) struct LoweringFunctionPlan {
    pub(super) locals: Vec<NameId>,
    /// Separates generic-header declaration symbols from generated storage names.
    pub(super) header_local_storage: Option<HeaderLocalStoragePlan>,
    pub(super) local_aliases: Vec<(NameId, NameId)>,
    pub(super) free_aliases: Vec<(NameId, NameId)>,
    pub(super) cell_sort_names: FxHashMap<NameId, String>,
    pub(super) globals: FxHashSet<NameId>,
    pub(super) annotation_references: FxHashSet<NameId>,
    pub(super) cellvars: FxHashSet<NameId>,
    pub(super) inlined_comprehension_cellvars: FxHashSet<NameId>,
    pub(super) freevars: Vec<NameId>,
    pub(super) annotation_freevars: Vec<NameId>,
    pub(super) required: FxHashSet<NameId>,
}

impl LoweringFunctionPlan {
    pub(super) fn absorb_child_requirements(
        &mut self,
        required_names: impl IntoIterator<Item = NameId>,
        annotation_references: impl IntoIterator<Item = NameId>,
    ) {
        let mut child_names = required_names
            .into_iter()
            .chain(annotation_references)
            .peekable();
        if child_names.peek().is_none() {
            return;
        }
        let local_names: FxHashSet<_> = self
            .locals
            .iter()
            .copied()
            .chain(self.local_aliases.iter().map(|(alias, _)| *alias))
            .collect();
        for name in child_names {
            if local_names.contains(&name) {
                self.cellvars.insert(name);
            } else if !self.globals.contains(&name) {
                self.required.insert(name);
            }
        }
    }

    pub(super) fn insert_freevar(&mut self, names: &NameInterner, name: NameId) {
        names.insert_lexical(&mut self.freevars, name);
    }

    pub(super) fn mark_global(&mut self, name: NameId) {
        self.annotation_freevars
            .retain(|candidate| *candidate != name);
        if self.locals.contains(&name) || self.local_aliases.iter().any(|(alias, _)| *alias == name)
        {
            return;
        }
        self.freevars.retain(|candidate| *candidate != name);
        self.globals.insert(name);
        self.required.remove(&name);
    }
}

impl FunctionPlan {
    fn absorb_child_requirements(
        &mut self,
        required_names: impl IntoIterator<Item = NameId>,
        annotation_references: impl IntoIterator<Item = NameId>,
    ) {
        let mut child_names = required_names
            .into_iter()
            .chain(annotation_references)
            .peekable();
        if child_names.peek().is_none() {
            return;
        }
        let local_names: FxHashSet<_> = self
            .locals
            .iter()
            .copied()
            .chain(self.local_aliases.iter().map(|(alias, _)| *alias))
            .collect();
        for name in child_names {
            if local_names.contains(&name) && !self.comprehension_shadowed_targets.contains(&name) {
                self.cellvars.insert(name);
            } else if !self.globals.contains(&name) {
                self.required.insert(name);
            }
        }
    }

    /// Header annotations are analyzed separately from a nongeneric function's runtime body.
    fn annotation_references(
        definition: &StmtFunctionDef,
        private_name: Option<&str>,
    ) -> FxHashSet<String> {
        let annotation_required = |expression: &Expr| {
            private_name.map_or_else(
                || expression_required_names(expression),
                |private_name| {
                    contextual_expression_requirements(
                        expression,
                        &|name| mangle_name(name, Some(private_name)).into_owned(),
                        expression_required_names,
                    )
                },
            )
        };
        let mut annotation_references = FxHashSet::default();
        for parameter in definition
            .parameters
            .posonlyargs
            .iter()
            .chain(&definition.parameters.args)
        {
            if let Some(annotation) = parameter.parameter.annotation.as_deref() {
                annotation_references.extend(annotation_required(annotation));
            }
        }
        if let Some(parameter) = &definition.parameters.vararg
            && let Some(annotation) = parameter.annotation.as_deref()
        {
            annotation_references.extend(annotation_required(annotation));
        }
        for parameter in &definition.parameters.kwonlyargs {
            if let Some(annotation) = parameter.parameter.annotation.as_deref() {
                annotation_references.extend(annotation_required(annotation));
            }
        }
        if let Some(parameter) = &definition.parameters.kwarg
            && let Some(annotation) = parameter.annotation.as_deref()
        {
            annotation_references.extend(annotation_required(annotation));
        }
        if let Some(annotation) = definition.returns.as_deref() {
            annotation_references.extend(annotation_required(annotation));
        }
        annotation_references
    }

    fn build(
        names: &mut NameInterner,
        definition: &StmtFunctionDef,
        module_parent: bool,
        future_annotations: bool,
        eager_annotations: bool,
        assertion_mode: AssertionMode,
        facts: ScopeBodyFacts,
        private_name: Option<&str>,
        nested_function_requirements: &FxHashSet<NameId>,
        nested_function_annotation_references: &FxHashSet<NameId>,
        class_requirements: &FxHashSet<NameId>,
    ) -> Self {
        let ScopeBodyFacts {
            mut globals,
            mut nonlocals,
            mut references,
            mut outside_inlined_comprehension_references,
            outside_inlined_comprehension_requirements,
            later_comprehension_references,
            explicit_dunder_class_reference,
            nested_lambda_requirements: lambda_requirements,
            nested_generator_requirements: generator_requirements,
            nested_annotation_scope_requirements: annotation_scope_requirements,
            generator_named_targets,
            inlined_comprehension_cellvars,
            has_assertions,
            has_inlined_comprehension,
            local_annotation_references,
            local_annotation_bindings,
            local_annotation_cellvars,
            ..
        } = facts;

        // Native declarations and name lookups use the same mangled symbol identity.
        // Keep both source spellings available to the raw-name lowering maps.
        if let Some(private_name) =
            private_name.filter(|_| !globals.is_empty() || !nonlocals.is_empty())
        {
            let prefix = format!("_{}", private_name.trim_start_matches('_'));
            for declarations in [&mut globals, &mut nonlocals] {
                for name in declarations.iter().cloned().collect::<Vec<_>>() {
                    let canonical = mangle_name(&name, Some(private_name)).into_owned();
                    if let Some(alias) = canonical.strip_prefix(&prefix)
                        && mangle_name(alias, Some(private_name)) == canonical
                    {
                        declarations.insert(alias.to_string());
                    }
                    declarations.insert(canonical);
                }
            }
        }
        // A declaration establishes the outer binding for every private spelling,
        // including when an inlined comprehension temporarily shadows that name.
        outside_inlined_comprehension_references.extend(nonlocals.iter().cloned());

        // Record potential local loads and actual bindings in one source-order pass. Filtering the
        // potential names after the pass preserves CPython's load-before-store local ordering
        // without walking the body once just to discover its complete binding set.
        let shadowed_nonlocal_cells = inlined_comprehension_cellvars
            .iter()
            .filter(|name| {
                nonlocals.contains(*name)
                    && outside_inlined_comprehension_references.contains(*name)
            })
            .cloned()
            .collect();
        let mut locals = LocalCollector {
            candidate_bindings: Some(FxHashMap::default()),
            shadowed_nonlocal_cells,
            global_comprehension_saves: !globals.is_empty(),
            globals,
            private_name: private_name.map(str::to_string),
            has_inlined_comprehension,
            ignore_generator_body_comprehension_targets: generator_named_targets.is_empty(),
            nonlocals,
            eager_function_annotations: eager_annotations,
            ..LocalCollector::default()
        };
        for parameter in parameters_in_locals_order(&definition.parameters) {
            locals.insert(parameter.name.as_str());
        }
        let mut parameter_names = locals.names.iter().cloned().collect::<FxHashSet<_>>();
        #[expect(
            clippy::iter_over_hash_type,
            reason = "Runtime uses claim source-order positions; unused names are filtered and capture-only cells are sorted during lowering."
        )]
        for name in local_annotation_bindings {
            locals.insert_annotation_only(&name);
        }
        let mut optimized_locals = (assertion_mode == AssertionMode::Elide && has_assertions)
            .then(|| {
                let mut optimized = locals.clone();
                optimized.elide_assertions = true;
                optimized.collect_suite(&definition.body);
                optimized
            })
            .filter(|locals| locals.elided_assertion);
        locals.collect_suite(&definition.body);
        if let Some(optimized) = &mut optimized_locals {
            if let Some(candidates) = &mut optimized.candidate_bindings {
                for name in &optimized.names {
                    if let Some(bound) = candidates.get_mut(name) {
                        *bound |= locals.non_comprehension_bindings.contains(name);
                    }
                }
            }
            optimized.retain_bindings();
        }
        locals.retain_bindings();
        let emitted_locals = optimized_locals.as_ref().unwrap_or(&locals);
        let comprehension_fast_bindings = emitted_locals.comprehension_iteration_targets.clone();
        let comprehension_target_predecessors =
            emitted_locals.comprehension_target_predecessors.clone();
        let comprehension_annotation_only_predecessors = emitted_locals
            .comprehension_annotation_only_predecessors
            .clone();

        // Child references in a module-level function resolve globally before comprehensions
        // are inlined. A temporary target cannot turn those references into closure captures.
        // Enclosing function bindings have different cell promotion during CPython's inlining.
        let mut outside_names = outside_inlined_comprehension_references
            .iter()
            .map(|name| mangle_name(name, private_name))
            .collect::<FxHashSet<_>>();
        if module_parent {
            outside_names.extend(
                outside_inlined_comprehension_requirements
                    .iter()
                    .chain(&later_comprehension_references)
                    .map(|name| mangle_name(name, private_name)),
            );
            outside_names.extend(
                class_requirements
                    .iter()
                    .chain(nested_function_requirements)
                    .chain(nested_function_annotation_references)
                    .map(|name| mangle_name(names.resolve(*name), private_name)),
            );
        }
        let non_comprehension_names = locals
            .non_comprehension_bindings
            .iter()
            .map(|name| mangle_name(name.as_str(), private_name))
            .collect::<FxHashSet<_>>();
        // Descendants and later comprehensions can refer to a temporary's global namesake.
        // Preserve native cell promotion when an enclosing function actually binds that name.
        let deferred_comprehension_globals = if module_parent {
            Vec::new()
        } else {
            let mut outside_names = outside_inlined_comprehension_requirements
                .iter()
                .chain(&later_comprehension_references)
                .map(|name| mangle_name(name, private_name))
                .collect::<FxHashSet<_>>();
            outside_names.extend(
                class_requirements
                    .iter()
                    .chain(nested_function_requirements)
                    .chain(nested_function_annotation_references)
                    .map(|name| mangle_name(names.resolve(*name), private_name)),
            );
            locals
                .comprehension_targets
                .iter()
                .filter_map(|name| {
                    let canonical = mangle_name(name.as_str(), private_name);
                    (outside_names.contains(&canonical)
                        && !non_comprehension_names.contains(&canonical))
                    .then(|| {
                        let comprehension_cell = inlined_comprehension_cellvars
                            .iter()
                            .chain(&local_annotation_cellvars)
                            .any(|candidate| mangle_name(candidate, private_name) == canonical);
                        (name.to_string(), canonical.into_owned(), comprehension_cell)
                    })
                })
                .collect()
        };
        let lexical_bindings = non_comprehension_names
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>();
        let mut comprehension_shadowed_targets = locals
            .comprehension_targets
            .iter()
            .filter(|name| {
                let canonical = mangle_name(name.as_str(), private_name);
                outside_names.contains(&canonical) && !non_comprehension_names.contains(&canonical)
            })
            .cloned()
            .collect::<FxHashSet<_>>();
        comprehension_shadowed_targets.extend(
            locals
                .comprehension_targets
                .iter()
                .filter(|name| locals.globals.contains(name.as_str()))
                .cloned(),
        );
        let deferred_comprehension_globals = deferred_comprehension_globals
            .into_iter()
            .map(|(name, canonical, comprehension_cell)| {
                (
                    names.intern(&name),
                    names.intern(&canonical),
                    comprehension_cell,
                )
            })
            .collect();
        let lexical_bindings = names.intern_set(lexical_bindings);
        let mut local_aliases = coalesce_private_locals(
            &mut locals.names,
            private_name,
            references
                .iter()
                .chain(&lambda_requirements)
                .chain(&generator_requirements)
                .chain(&annotation_scope_requirements)
                .map(String::as_str)
                .chain(
                    nested_function_requirements
                        .iter()
                        .map(|name| names.resolve(*name)),
                )
                .chain(
                    nested_function_annotation_references
                        .iter()
                        .map(|name| names.resolve(*name)),
                ),
        );
        for (alias, original) in &local_aliases {
            if parameter_names.contains(alias) || parameter_names.contains(original) {
                parameter_names.extend([alias.clone(), original.clone()]);
            }
            if comprehension_shadowed_targets.contains(alias)
                || comprehension_shadowed_targets.contains(original)
            {
                comprehension_shadowed_targets.extend([alias.clone(), original.clone()]);
            }
        }

        let annotation_references = if future_annotations {
            FxHashSet::default()
        } else {
            Self::annotation_references(definition, private_name)
        };

        if locals.annotation_only.contains("__class__") && !explicit_dunder_class_reference {
            references.remove("__class__");
        }
        let local_names: FxHashSet<_> = locals
            .names
            .iter()
            .cloned()
            .chain(local_aliases.iter().map(|(alias, _)| alias.clone()))
            .collect();
        locals.names.retain(|name| {
            !locals.annotation_only.contains(name)
                || references.contains(name.as_str())
                    && (name != "__class__" || explicit_dunder_class_reference)
                || names
                    .get(name)
                    .is_some_and(|name| class_requirements.contains(&name))
                || lambda_requirements.contains(name.as_str())
                || generator_requirements.contains(name.as_str())
                || annotation_scope_requirements.contains(name.as_str())
                || names.get(name).is_some_and(|name| {
                    nested_function_requirements.contains(&name)
                        || nested_function_annotation_references.contains(&name)
                })
        });
        local_aliases.retain(|(_, original)| locals.names.contains(original));
        let mut annotation_cell_locals = local_annotation_cellvars
            .iter()
            .filter(|name| !local_names.contains(name.as_str()))
            .cloned()
            .collect::<Vec<_>>();
        annotation_cell_locals.sort();
        // These comprehension cells exist even though no annotation code executes. Their
        // names must not replace a global or free variable used by the actual function body.
        comprehension_shadowed_targets.extend(
            annotation_cell_locals
                .iter()
                .map(|name| Name::from(name.as_str())),
        );
        locals
            .names
            .extend(annotation_cell_locals.into_iter().map(Name::from));
        references.extend(
            class_requirements
                .iter()
                .map(|name| names.resolve(*name).to_string()),
        );
        references.extend(lambda_requirements.iter().cloned());
        references.extend(generator_requirements.iter().cloned());
        references.extend(annotation_scope_requirements.iter().cloned());
        references.extend(local_annotation_references);
        let is_closure_local = |name: &str| {
            local_names.contains(name) && !comprehension_shadowed_targets.contains(name)
        };
        let mut cellvars = generator_named_targets
            .into_iter()
            .filter(|name| is_closure_local(name))
            .collect::<FxHashSet<_>>();
        cellvars.extend(local_annotation_cellvars);
        cellvars.extend(
            class_requirements
                .iter()
                .map(|name| names.resolve(*name))
                .filter(|name| is_closure_local(name))
                .map(str::to_string),
        );
        cellvars.extend(
            lambda_requirements
                .into_iter()
                .filter(|name| is_closure_local(name)),
        );
        cellvars.extend(
            generator_requirements
                .into_iter()
                .filter(|name| is_closure_local(name)),
        );
        cellvars.extend(
            annotation_scope_requirements
                .into_iter()
                .filter(|name| is_closure_local(name)),
        );
        // A captured comprehension target still needs a cell when an unrelated outer
        // reference resolves globally. Its cell is active only inside the comprehension.
        cellvars.extend(
            inlined_comprehension_cellvars
                .iter()
                .filter(|name| comprehension_shadowed_targets.contains(name.as_str()))
                .cloned(),
        );
        let retained_local_names: FxHashSet<_> = locals
            .names
            .iter()
            .map(Name::as_str)
            .chain(
                local_aliases
                    .iter()
                    .filter(|(_, original)| locals.names.contains(original))
                    .map(|(alias, _)| alias.as_str()),
            )
            .collect();
        let required: BTreeSet<_> = references
            .iter()
            .chain(&locals.nonlocals)
            .filter(|name| {
                (comprehension_shadowed_targets.contains(name.as_str())
                    || if eager_annotations {
                        !local_names.contains(name.as_str())
                    } else {
                        !retained_local_names.contains(name.as_str())
                    })
                    && !locals.globals.contains(*name)
            })
            .cloned()
            .collect();
        let type_parameter_names = definition
            .type_params
            .iter()
            .flat_map(|parameters| parameters.iter())
            .map(|parameter| parameter.name().as_str().to_string())
            .collect::<Vec<_>>();
        let mut plan = Self {
            locals: locals
                .names
                .into_iter()
                .map(|name| names.intern(name.as_str()))
                .collect(),
            local_aliases: local_aliases
                .into_iter()
                .map(|(alias, original)| {
                    (
                        names.intern(alias.as_str()),
                        names.intern(original.as_str()),
                    )
                })
                .collect(),
            lexical_bindings,
            deferred_comprehension_globals,
            globals: names.intern_set(locals.globals),
            cell_sort_names: FxHashMap::default(),
            annotation_references: names.intern_set(annotation_references),
            cellvars: names.intern_set(cellvars),
            inlined_comprehension_cellvars: names.intern_set(inlined_comprehension_cellvars),
            freevars: Vec::new(),
            annotation_freevars: Vec::new(),
            comprehension_shadowed_targets: comprehension_shadowed_targets
                .into_iter()
                .map(|name| names.intern(name.as_str()))
                .collect(),
            required: names.intern_set(required),
            type_parameter_names: names.intern_set(type_parameter_names),
        };
        plan.absorb_child_requirements(
            nested_function_requirements.iter().copied(),
            nested_function_annotation_references.iter().copied(),
        );
        // Captures use either spelling, while emitted metadata retains one native slot.
        for &(alias, original) in &plan.local_aliases {
            if plan.comprehension_shadowed_targets.contains(&alias)
                || plan.comprehension_shadowed_targets.contains(&original)
            {
                plan.comprehension_shadowed_targets
                    .extend([alias, original]);
            }
            if plan.cellvars.contains(&alias) || plan.cellvars.contains(&original) {
                plan.cellvars.extend([alias, original]);
            }
            if plan.inlined_comprehension_cellvars.contains(&alias)
                || plan.inlined_comprehension_cellvars.contains(&original)
            {
                plan.inlined_comprehension_cellvars
                    .extend([alias, original]);
            }
        }
        if let Some(optimized) = optimized_locals {
            let mut retained = optimized
                .names
                .iter()
                .filter_map(|name| names.get(name))
                .map(|name| {
                    plan.local_aliases
                        .iter()
                        .find(|(alias, _)| *alias == name)
                        .map_or(name, |(_, original)| *original)
                })
                .filter(|name| plan.locals.contains(name))
                .collect::<Vec<_>>();
            retained.dedup();
            for &name in &plan.locals {
                if plan.cellvars.contains(&name) && !retained.contains(&name) {
                    retained.push(name);
                }
            }
            plan.locals = retained;
            plan.inlined_comprehension_cellvars.retain(|name| {
                optimized
                    .comprehension_iteration_targets
                    .iter()
                    .any(|target| names.get(target) == Some(*name))
            });
        }
        let canonical_local = |name| {
            plan.local_aliases
                .iter()
                .find(|(alias, _)| *alias == name)
                .map_or(name, |(_, original)| *original)
        };
        let comprehension_fast_cellvars = comprehension_fast_bindings
            .iter()
            .filter_map(|name| names.get(name))
            .map(canonical_local)
            .filter(|name| plan.cellvars.contains(name))
            .collect::<Vec<_>>();
        let mut seen_reordered = FxHashSet::default();
        let comprehension_reordered_fast_locals = comprehension_fast_bindings
            .iter()
            .filter(|name| !parameter_names.contains(*name))
            .filter_map(|name| {
                let id = canonical_local(names.get(name)?);
                // Explicit globals were reserved at their first comprehension save;
                // ordinary global operations never claimed an earlier fast-local slot.
                if plan.globals.contains(&id) {
                    return None;
                }
                // Global and cell operations do not reserve the fast-local slot used to
                // save a later comprehension temporary with the same name.
                (plan.comprehension_shadowed_targets.contains(&id) || plan.cellvars.contains(&id))
                    .then_some(id)
            })
            .filter(|name| seen_reordered.insert(*name))
            .collect::<Vec<_>>();
        let mut comprehension_fast_predecessors = FxHashMap::default();
        for name in &comprehension_fast_bindings {
            let Some(id) = names.get(name).map(canonical_local) else {
                continue;
            };
            let Some(predecessors) = comprehension_target_predecessors.get(name) else {
                continue;
            };
            let annotation_only = comprehension_annotation_only_predecessors.get(name);
            // Aliases share the reservation made by the first source-order target.
            comprehension_fast_predecessors
                .entry(id)
                .or_insert_with(|| {
                    predecessors
                        .iter()
                        .filter(|predecessor| {
                            annotation_only.is_none_or(|names| !names.contains(*predecessor))
                        })
                        .filter_map(|predecessor| names.get(predecessor))
                        .map(canonical_local)
                        .filter(|predecessor| *predecessor != id)
                        .collect()
                });
        }
        reorder_comprehension_fast_cells(
            &mut plan.locals,
            &comprehension_reordered_fast_locals,
            &comprehension_fast_predecessors,
        );
        plan.inlined_comprehension_cellvars
            .extend(comprehension_fast_cellvars);
        if !plan.local_aliases.is_empty() {
            plan.cell_sort_names = plan
                .locals
                .iter()
                .copied()
                .map(|name| {
                    (
                        name,
                        mangle_name(names.resolve(name), private_name).into_owned(),
                    )
                })
                .collect();
        }
        plan
    }

    pub(super) fn insert_freevar(&mut self, names: &NameInterner, name: NameId) {
        names.insert_lexical(&mut self.freevars, name);
    }

    fn insert_annotation_freevar(&mut self, names: &NameInterner, name: NameId) {
        names.insert_lexical(&mut self.annotation_freevars, name);
    }

    fn resolve_required(&mut self, names: &NameInterner, mut captures: impl FnMut(NameId) -> bool) {
        if self.required.is_empty() {
            return;
        }

        // Most required names resolve to globals. Reuse their cloned table and only allocate
        // replacement requirements for captures and locals that cannot be marked global.
        let mut global_candidates = std::mem::take(&mut self.required);
        global_candidates.retain(|&name| {
            if captures(name) {
                self.insert_freevar(names, name);
            } else if self.prepare_to_mark_global(name) {
                return true;
            }
            self.required.insert(name);
            false
        });
        if self.globals.is_empty() {
            self.globals = global_candidates;
        } else {
            self.globals.extend(global_candidates);
        }
    }

    fn prepare_to_mark_global(&mut self, name: NameId) -> bool {
        self.annotation_freevars
            .retain(|candidate| *candidate != name);
        if (self.locals.contains(&name)
            || self.local_aliases.iter().any(|(alias, _)| *alias == name))
            && !self.comprehension_shadowed_targets.contains(&name)
        {
            return false;
        }
        self.freevars.retain(|candidate| *candidate != name);
        true
    }

    pub(super) fn mark_global(&mut self, name: NameId) {
        if self.prepare_to_mark_global(name) {
            self.globals.insert(name);
            self.required.remove(&name);
        }
    }

    /// Copies only the state consumed by late closure resolution and lowering.
    #[inline(never)]
    fn clone_for_lowering(&self) -> Self {
        Self {
            locals: self.locals.clone(),
            local_aliases: self.local_aliases.clone(),
            lexical_bindings: FxHashSet::default(),
            deferred_comprehension_globals: Vec::new(),
            cell_sort_names: self.cell_sort_names.clone(),
            globals: self.globals.clone(),
            annotation_references: self.annotation_references.clone(),
            cellvars: self.cellvars.clone(),
            inlined_comprehension_cellvars: self.inlined_comprehension_cellvars.clone(),
            freevars: self.freevars.clone(),
            annotation_freevars: self.annotation_freevars.clone(),
            comprehension_shadowed_targets: self.comprehension_shadowed_targets.clone(),
            required: self.required.clone(),
            type_parameter_names: FxHashSet::default(),
        }
    }

    pub(super) fn into_lowering_plan(self) -> LoweringFunctionPlan {
        LoweringFunctionPlan {
            locals: self.locals,
            header_local_storage: None,
            local_aliases: self.local_aliases,
            free_aliases: Vec::new(),
            cell_sort_names: self.cell_sort_names,
            globals: self.globals,
            annotation_references: self.annotation_references,
            cellvars: self.cellvars,
            inlined_comprehension_cellvars: self.inlined_comprehension_cellvars,
            freevars: self.freevars,
            annotation_freevars: self.annotation_freevars,
            required: self.required,
        }
    }
}

#[derive(Clone, Debug, Default)]
struct ClassPlan {
    globals: FxHashSet<NameId>,
    canonical_globals: FxHashSet<NameId>,
    nonlocals: FxHashSet<NameId>,
    bound_names: FxHashSet<NameId>,
    canonical_annotation_shadows: FxHashSet<NameId>,
    namespace_bindings: FxHashSet<NameId>,
    comprehension_targets: Vec<(NameId, bool)>,
    comprehension_cells: FxHashSet<NameId>,
    required: FxHashSet<NameId>,
    type_parameter_names: FxHashSet<NameId>,
    canonical_type_parameter_names: FxHashSet<NameId>,
    unmangled_required: FxHashSet<NameId>,
    enclosing_names: FxHashMap<NameId, NameId>,
    needs_class_closure: bool,
    needs_classdict: bool,
    has_conditional_annotations: bool,
}

#[derive(Clone, Debug, Default)]
pub(super) struct LoweringClassPlan {
    pub(super) globals: FxHashSet<NameId>,
    pub(super) nonlocals: FxHashSet<NameId>,
    pub(super) bound_names: FxHashSet<NameId>,
    pub(super) comprehension_targets: Vec<(NameId, bool)>,
    pub(super) comprehension_cells: FxHashSet<NameId>,
    pub(super) required: FxHashSet<NameId>,
    pub(super) unmangled_required: FxHashSet<NameId>,
    pub(super) enclosing_names: FxHashMap<NameId, NameId>,
    pub(super) needs_class_closure: bool,
    pub(super) needs_classdict: bool,
    pub(super) has_conditional_annotations: bool,
}

impl ClassPlan {
    fn build(
        names: &mut NameInterner,
        definition: &StmtClassDef,
        future_annotations: bool,
        deferred_annotations: bool,
        facts: ScopeBodyFacts,
        method_requirements: &FxHashSet<NameId>,
        method_annotation_references: &FxHashSet<NameId>,
        nested_class_requirements: &FxHashSet<NameId>,
        nested_unmangled_requirements: &FxHashSet<NameId>,
        child_needs_class_closure: bool,
    ) -> Self {
        // Symbol analysis records every annotation in a compound statement, even
        // a non-simple target that emits no annotation thunk. Future annotations
        // retain this cell as well, although the thunk does not capture it.
        let has_conditional_annotations = deferred_annotations
            && definition.body.iter().any(|statement| {
                !matches!(statement, Stmt::AnnAssign(_))
                    && has_annotations(std::slice::from_ref(statement))
            });
        let ScopeBodyFacts {
            globals,
            nonlocals,
            references,
            class_inlined_comprehension_references,
            explicit_dunder_class_reference,
            nested_lambda_requirements,
            nested_generator_requirements,
            nested_annotation_scope_requirements: annotation_scope_requirements,
            unmangled_class_header_requirements,
            unmangled_class_header_captures,
            nested_annotation_class_closure,
            annotation_class_reference,
            annotation_comprehension_requirements,
            has_function_definition,
            has_generic_definition,
            has_type_alias,
            has_annotations,
            inlined_comprehension_cellvars,
            ..
        } = facts;
        let mut locals = LocalCollector {
            globals,
            nonlocals,
            ignore_generator_body_comprehension_targets: true,
            eager_function_annotations: !deferred_annotations && !future_annotations,
            eager_statement_annotations: !deferred_annotations && !future_annotations,
            legacy_class_comprehension_symbols: (!deferred_annotations).then(Vec::new),
            ..LocalCollector::default()
        };
        locals.collect_suite(&definition.body);

        // Symbol analysis compares the canonical spelling of private aliases before
        // deciding whether a direct class reference can escape to an enclosing scope.
        // Comprehension iteration targets do not bind the class namespace.
        let private_name = (!deferred_annotations).then_some(definition.name.as_str());
        let bound_names = private_name.map(|_| {
            locals
                .seen
                .iter()
                .filter(|name| locals.non_comprehension_bindings.contains(*name))
                .map(|name| mangle_name(name.as_str(), private_name))
                .collect::<FxHashSet<_>>()
        });
        let global_names = locals
            .globals
            .iter()
            .map(|name| mangle_name(name, Some(definition.name.as_str())))
            .collect::<FxHashSet<_>>();
        let nonlocal_names = private_name.map(|_| {
            locals
                .nonlocals
                .iter()
                .map(|name| mangle_name(name, private_name))
                .collect::<FxHashSet<_>>()
        });
        let is_bound = |name: &str| {
            bound_names.as_ref().map_or_else(
                || locals.seen.contains(name) && locals.non_comprehension_bindings.contains(name),
                |names| names.contains(mangle_name(name, private_name).as_ref()),
            )
        };
        let is_global = |name: &str| {
            global_names.contains(mangle_name(name, Some(definition.name.as_str())).as_ref())
        };
        let is_nonlocal = |name: &str| {
            nonlocal_names.as_ref().map_or_else(
                || locals.nonlocals.contains(name),
                |names| names.contains(mangle_name(name, private_name).as_ref()),
            )
        };
        let body_explicitly_references_dunder_class = explicit_dunder_class_reference;
        let mut required = references
            .into_iter()
            .filter(|name| is_nonlocal(name) || (!is_global(name) && !is_bound(name)))
            .collect::<BTreeSet<_>>();
        required.extend(locals.nonlocals.iter().cloned());
        let body_requires_classdict = required.contains("__classdict__");
        let body_requires_conditional_annotations =
            required.contains("__conditional_annotations__");
        let nested_requires = |name: &str| {
            nested_lambda_requirements.contains(name)
                || nested_generator_requirements.contains(name)
                || names.get(name).is_some_and(|name| {
                    method_requirements.contains(&name) || nested_class_requirements.contains(&name)
                })
        };
        let nested_requires_classdict = nested_requires("__classdict__");
        let nested_requires_conditional_annotations =
            nested_requires("__conditional_annotations__");
        let has_conditional_annotations = has_conditional_annotations
            || deferred_annotations && nested_requires_conditional_annotations;
        let annotation_requires_class = !is_bound("__class__")
            && !is_global("__class__")
            && !is_nonlocal("__class__")
            && annotation_class_reference;
        required.extend(
            annotation_scope_requirements
                .into_iter()
                .filter(|name| !is_bound(name) && !is_global(name)),
        );
        // A generic class header restricts mangling to its own type parameters.
        // Its other private spellings are raw names, independent of body bindings.
        let mut unmangled_required = unmangled_class_header_requirements
            .into_iter()
            .filter(|name| {
                !locals.seen.iter().any(|bound| {
                    mangle_name(bound.as_str(), Some(definition.name.as_str())) == name.as_str()
                }) && !locals.globals.iter().any(|global| {
                    mangle_name(global, Some(definition.name.as_str())) == name.as_str()
                })
            })
            .collect::<BTreeSet<_>>();
        unmangled_required.extend(unmangled_class_header_captures);
        unmangled_required.extend(
            nested_unmangled_requirements
                .iter()
                .map(|name| names.resolve(*name).to_string()),
        );
        let body_requires_dunder_class =
            body_explicitly_references_dunder_class && required.contains("__class__");

        // Inlined comprehension bodies retain function-style lookup: class bindings and
        // global declarations do not prevent them from capturing enclosing function locals.
        required.extend(class_inlined_comprehension_references);
        required.extend(nested_lambda_requirements.iter().cloned());
        required.extend(nested_generator_requirements.iter().cloned());
        required.extend(
            method_requirements
                .iter()
                .map(|name| names.resolve(*name).to_string()),
        );
        if !future_annotations {
            required.extend(
                method_annotation_references
                    .iter()
                    .map(|name| names.resolve(*name))
                    .filter(|name| !is_bound(name) && !is_global(name))
                    .map(str::to_string),
            );
        }
        required.extend(
            nested_class_requirements
                .iter()
                .map(|name| names.resolve(*name).to_string()),
        );
        if !body_requires_dunder_class && !locals.nonlocals.contains("__class__") {
            required.remove("__class__");
        }
        if !body_requires_classdict {
            required.remove("__classdict__");
        }
        if deferred_annotations && !body_requires_conditional_annotations {
            required.remove("__conditional_annotations__");
        }

        let comprehension_needs_class = annotation_comprehension_requirements
            .captures
            .contains("__class__")
            || annotation_comprehension_requirements.first_iterable_needs_class
                && !is_global("__class__");
        // The annotation captures the class being defined, not an outer __class__ binding.
        if comprehension_needs_class
            && !body_requires_dunder_class
            && !locals.nonlocals.contains("__class__")
        {
            required.remove("__class__");
        }
        // Separate comprehensions skip class bindings when capturing enclosing locals.
        let needs_class_closure = child_needs_class_closure
            || nested_lambda_requirements.contains("__class__")
            || nested_generator_requirements.contains("__class__")
            || nested_annotation_class_closure
            || annotation_requires_class
            || comprehension_needs_class;
        required.extend(
            annotation_comprehension_requirements
                .captures
                .into_iter()
                .filter(|name| name != "__class__"),
        );
        let needs_classdict = nested_requires_classdict
            || has_type_alias
            || has_generic_definition
            || deferred_annotations
                && !future_annotations
                && (has_function_definition || has_annotations);
        let comprehension_targets = locals
            .legacy_class_comprehension_symbols
            .take()
            .unwrap_or_else(|| {
                std::mem::take(&mut locals.comprehension_targets)
                    .into_iter()
                    .map(|name| (name, false))
                    .collect()
            })
            .into_iter()
            .map(|(name, requires_free)| (names.intern(name.as_str()), requires_free))
            .collect();
        let canonical_globals = locals
            .globals
            .iter()
            .map(|name| names.intern(&mangle_name(name.as_str(), Some(definition.name.as_str()))))
            .collect::<FxHashSet<_>>();
        let canonical_annotation_shadows = locals
            .seen
            .iter()
            .map(|name| names.intern(&mangle_name(name.as_str(), Some(definition.name.as_str()))))
            .chain(canonical_globals.iter().copied())
            .collect();
        Self {
            canonical_globals,
            canonical_annotation_shadows,
            namespace_bindings: locals
                .non_comprehension_bindings
                .iter()
                .filter(|name| locals.seen.contains(name.as_str()))
                .map(|name| {
                    names
                        .intern(mangle_name(name.as_str(), Some(definition.name.as_str())).as_ref())
                })
                .collect(),
            globals: names.intern_set(locals.globals),
            nonlocals: names.intern_set(locals.nonlocals),
            bound_names: locals
                .seen
                .into_iter()
                .map(|name| names.intern(name.as_str()))
                .collect(),
            comprehension_targets,
            comprehension_cells: names.intern_set(inlined_comprehension_cellvars),
            required: names.intern_set(required),
            unmangled_required: names.intern_set(unmangled_required),
            type_parameter_names: definition
                .type_params
                .iter()
                .flat_map(|parameters| parameters.iter())
                .map(|parameter| names.intern(parameter.name().as_str()))
                .collect(),
            canonical_type_parameter_names: definition
                .type_params
                .iter()
                .flat_map(|parameters| parameters.iter())
                .map(|parameter| {
                    names.intern(&mangle_name(
                        parameter.name().as_str(),
                        Some(definition.name.as_str()),
                    ))
                })
                .collect(),
            enclosing_names: FxHashMap::default(),
            needs_class_closure,
            needs_classdict,
            has_conditional_annotations,
        }
    }

    fn lowering_plan(&self) -> LoweringClassPlan {
        LoweringClassPlan {
            globals: self.globals.clone(),
            nonlocals: self.nonlocals.clone(),
            bound_names: self.bound_names.clone(),
            comprehension_targets: self.comprehension_targets.clone(),
            comprehension_cells: self.comprehension_cells.clone(),
            required: self.required.clone(),
            enclosing_names: self.enclosing_names.clone(),
            unmangled_required: self.unmangled_required.clone(),
            needs_class_closure: self.needs_class_closure,
            needs_classdict: self.needs_classdict,
            has_conditional_annotations: self.has_conditional_annotations,
        }
    }
}

#[newtype_index]
pub(super) struct ScopeId;

impl ScopeId {
    pub(super) const MODULE: Self = Self::from_u32(0);
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum ScopeOrigin {
    Function(u32, u32),
    Class(u32, u32),
}

impl ScopeOrigin {
    fn function(definition: &StmtFunctionDef) -> Self {
        Self::Function(
            u32::from(definition.range.start()),
            u32::from(definition.range.end()),
        )
    }

    fn class(definition: &StmtClassDef) -> Self {
        Self::Class(
            u32::from(definition.range.start()),
            u32::from(definition.range.end()),
        )
    }
}

#[derive(Debug)]
enum ScopePlan {
    // Filled after the scope's children have been analyzed.
    Pending,
    Module,
    Function(FunctionPlan),
    Class(ClassPlan),
}

#[derive(Debug)]
struct ScopeNode {
    parent: Option<ScopeId>,
    plan: ScopePlan,
    children: Vec<ScopeId>,
}

#[derive(Debug)]
pub(super) struct ScopeArena {
    pub(super) names: NameInterner,
    module: ModulePlan,
    nodes: IndexVec<ScopeId, ScopeNode>,
    by_parent_and_origin: FxHashMap<(ScopeId, ScopeOrigin), ScopeId>,
    elided_comprehension_cells: FxHashMap<ScopeId, Vec<NameId>>,
    deferred_annotations: bool,
    python_version: PythonVersion,
    assertion_mode: AssertionMode,
}

/// The only optimized scope facts retained after restoring the original symbol table.
pub(super) struct LoweredScopeFacts {
    names: NameInterner,
    module_targets: Vec<NameId>,
    classes: FxHashMap<ScopeOrigin, Vec<(NameId, bool)>>,
    has_nested_classes: bool,
}

impl LoweredScopeFacts {
    pub(super) fn analyze<'ast>(
        body: &'ast [Stmt],
        python_version: PythonVersion,
        source: &mut SourceAnalysis<'ast>,
        original: &ScopeArena,
    ) -> Self {
        let has_original_class_comprehensions = original.module.has_class_comprehensions;
        let empty_targets =
            !has_original_class_comprehensions && original.module.comprehension_targets.is_empty();
        #[cfg(test)]
        let empty_targets = empty_targets && !FORCE_FULL_LOWERED_SCOPES.get();
        if empty_targets {
            // Without comprehension locals, only source-dependent metadata needs another walk.
            source.visit_body(body);
            return Self {
                names: NameInterner::seeded(),
                module_targets: Vec::new(),
                classes: original
                    .by_parent_and_origin
                    .keys()
                    .filter_map(|&(_, origin)| match origin {
                        ScopeOrigin::Class(..) => Some((origin, Vec::new())),
                        ScopeOrigin::Function(..) => None,
                    })
                    .collect(),
                has_nested_classes: original.has_nested_class_scopes(),
            };
        }

        // Class comprehensions can require a full rebuild; retain its reusable function inputs.
        let inputs = ScopeInputs::collect(
            body,
            python_version,
            source,
            AssertionMode::Keep,
            has_original_class_comprehensions,
        );
        let has_nested_classes = inputs.definitions.iter().any(|input| {
            input.parent != ScopeId::MODULE
                && matches!(input.definition, ScopeDefinition::Class(..))
        });
        let full_analysis = inputs.facts.has_class_comprehensions;
        #[cfg(test)]
        let full_analysis = full_analysis || FORCE_FULL_LOWERED_SCOPES.get();
        if full_analysis {
            let mut arena = inputs.build();
            let classes = arena
                .by_parent_and_origin
                .iter()
                .filter_map(|((_, origin), &id)| {
                    let ScopePlan::Class(plan) = &mut arena.nodes[id].plan else {
                        return None;
                    };
                    Some((*origin, std::mem::take(&mut plan.comprehension_targets)))
                })
                .collect();
            return Self {
                names: arena.names,
                module_targets: arena.module.comprehension_targets,
                classes,
                has_nested_classes,
            };
        }

        // Without class comprehensions, no child scope plan can affect these facts.
        let classes = inputs
            .definitions
            .iter()
            .filter_map(|input| match input.definition {
                ScopeDefinition::Class(definition, _) => {
                    Some((ScopeOrigin::class(definition), Vec::new()))
                }
                ScopeDefinition::Function(..) => None,
            })
            .collect();
        let module_targets = inputs
            .bindings
            .comprehension_targets
            .iter()
            .map(|name| {
                inputs
                    .arena
                    .names
                    .get(name.as_str())
                    .expect("module comprehension names are interned")
            })
            .collect();
        Self {
            names: inputs.arena.names,
            module_targets,
            classes,
            has_nested_classes,
        }
    }

    pub(super) fn has_class_scopes(&self) -> bool {
        !self.classes.is_empty()
    }

    pub(super) const fn has_nested_class_scopes(&self) -> bool {
        self.has_nested_classes
    }
}

#[derive(Debug, Default)]
pub(super) struct ModulePlan {
    pub(super) future_flags: u32,
    pub(super) module_globals: NameSet,
    pub(super) imported_scope_names: NameSet,
    pub(super) comprehension_targets: Vec<NameId>,
    pub(super) comprehension_cell_names: NameSet,
    pub(super) has_annotations: bool,
    pub(super) has_simple_annotations: bool,
    pub(super) has_class_comprehensions: bool,
    has_suspension_expressions: bool,
    yield_offsets: Vec<TextSize>,
}

#[derive(Debug, Default)]
struct ModulePlanBuilder {
    module_globals: FxHashSet<String>,
    imported_scope_names: FxHashSet<String>,
    comprehension_cell_names: FxHashSet<String>,
    has_annotations: bool,
    has_simple_annotations: bool,
    has_suspension_expressions: bool,
    has_class_comprehensions: bool,
    yield_offsets: Vec<TextSize>,
}

impl ModulePlan {
    /// The scope-aware suspension walker can succeed only for an `await` or async comprehension.
    pub(super) fn has_suspension_expressions(&self) -> bool {
        #[cfg(test)]
        if FORCE_GENERIC_SUSPENSION_SEARCH.get() {
            return true;
        }
        self.has_suspension_expressions
    }

    /// Statement ranges include nested definition decorators and headers. Nested bodies can produce
    /// false positives; the scope-aware walk remains authoritative.
    pub(super) fn may_contain_yield(&self, body: &[Stmt]) -> bool {
        #[cfg(test)]
        if FORCE_GENERIC_SUSPENSION_SEARCH.get() {
            return true;
        }
        if self.yield_offsets.is_empty() {
            return false;
        }
        let (Some(first), Some(last)) = (body.first(), body.last()) else {
            return false;
        };
        let start = first.start();
        let end = last.end();
        let index = self.yield_offsets.partition_point(|offset| *offset < start);
        self.yield_offsets
            .get(index)
            .is_some_and(|offset| *offset < end)
    }

    fn build(
        names: &NameInterner,
        future_flags: u32,
        mut facts: ModulePlanBuilder,
        bindings: LocalCollector,
    ) -> Self {
        let name_id = |name: String| {
            names
                .get(&name)
                .unwrap_or_else(|| panic!("module analysis did not intern `{name}`"))
        };
        let mut imported_scope_names: NameSet =
            facts.imported_scope_names.drain().map(&name_id).collect();
        // Native super-call specialization requires the module symbol to be absent,
        // including USE-only references and globals declared by nested scopes.
        if bindings.seen.contains("super")
            || bindings.module_references_super == Some(true)
            || facts.module_globals.contains("super")
        {
            imported_scope_names.insert(
                names
                    .get(SHADOWED_SUPER_SENTINEL)
                    .expect("module analysis should intern the shadowed-super sentinel"),
            );
        }
        // The AST visitor follows evaluation order for some expressions, not source order.
        facts.yield_offsets.sort_unstable();
        facts.yield_offsets.dedup();
        Self {
            future_flags,
            module_globals: facts.module_globals.drain().map(&name_id).collect(),
            imported_scope_names,
            comprehension_targets: bindings
                .comprehension_targets
                .into_iter()
                .map(|name| {
                    names
                        .get(name.as_str())
                        .unwrap_or_else(|| panic!("module analysis did not intern `{name}`"))
                })
                .collect(),
            comprehension_cell_names: facts
                .comprehension_cell_names
                .drain()
                .map(name_id)
                .collect(),
            has_annotations: facts.has_annotations,
            has_simple_annotations: facts.has_simple_annotations,
            has_class_comprehensions: facts.has_class_comprehensions,
            has_suspension_expressions: facts.has_suspension_expressions,
            yield_offsets: facts.yield_offsets,
        }
    }
}

impl Default for ScopeArena {
    fn default() -> Self {
        Self {
            names: NameInterner::default(),
            module: ModulePlan::default(),
            nodes: IndexVec::from([ScopeNode {
                parent: None,
                plan: ScopePlan::Module,
                children: Vec::new(),
            }]),
            by_parent_and_origin: FxHashMap::default(),
            elided_comprehension_cells: FxHashMap::default(),
            deferred_annotations: true,
            python_version: PythonVersion::Py314,
            assertion_mode: AssertionMode::Keep,
        }
    }
}

impl ScopeArena {
    /// Captured temporaries from removed assertions remain cells in the enclosing code object.
    pub(super) fn elided_comprehension_cells(&self, scope: ScopeId) -> &[NameId] {
        self.elided_comprehension_cells
            .get(&scope)
            .map_or(&[], Vec::as_slice)
    }

    /// Comprehension temporaries are allocated during lowering, after assertion removal.
    pub(super) fn retain_lowered_comprehension_locals(&mut self, lowered: &LoweredScopeFacts) {
        let original_name = |name| {
            self.names
                .get(lowered.names.resolve(name))
                .expect("a lowered comprehension name occurs in the original scope")
        };
        let lowered_module_targets = lowered
            .module_targets
            .iter()
            .copied()
            .map(original_name)
            .collect::<Vec<_>>();
        let elided_module_cells = self
            .module
            .comprehension_targets
            .iter()
            .copied()
            .filter(|name| {
                self.module.comprehension_cell_names.contains(*name)
                    && !lowered_module_targets.contains(name)
            })
            .collect();
        self.elided_comprehension_cells
            .insert(ScopeId::MODULE, elided_module_cells);
        self.module.comprehension_targets = lowered_module_targets;
        let mut original_scopes = self
            .by_parent_and_origin
            .iter()
            .map(|((_, origin), &id)| (*origin, id))
            .collect::<Vec<_>>();
        original_scopes.sort_unstable_by_key(|(_, id)| id.index());
        for (origin, id) in original_scopes {
            let Some(lowered_targets) = lowered.classes.get(&origin) else {
                continue;
            };
            if let ScopePlan::Class(plan) = &mut self.nodes[id].plan {
                let lowered_targets = lowered_targets
                    .iter()
                    .map(|&(name, requires_free)| {
                        let name = original_name(name);
                        plan.comprehension_targets
                            .iter()
                            .find(|&&(target, _)| target == name)
                            .copied()
                            .unwrap_or((name, requires_free))
                    })
                    .collect::<Vec<_>>();
                let mut seen_cells = FxHashSet::default();
                let elided_cells = plan
                    .comprehension_targets
                    .iter()
                    .filter(|(name, _)| {
                        plan.comprehension_cells.contains(name)
                            && !lowered_targets.iter().any(|(target, _)| target == name)
                    })
                    .map(|&(name, _)| name)
                    .filter(|name| seen_cells.insert(*name))
                    .collect();
                self.elided_comprehension_cells.insert(id, elided_cells);
                plan.comprehension_targets = lowered_targets;
            }
        }
    }

    pub(super) fn has_class_scopes(&self) -> bool {
        self.nodes
            .iter()
            .any(|node| matches!(node.plan, ScopePlan::Class(_)))
    }

    pub(super) fn has_nested_class_scopes(&self) -> bool {
        self.by_parent_and_origin.keys().any(|(parent, origin)| {
            *parent != ScopeId::MODULE && matches!(origin, ScopeOrigin::Class(_, _))
        })
    }

    #[cfg(test)]
    pub(super) fn analyze(body: &[Stmt]) -> Self {
        Self::analyze_with_python_version(body, PythonVersion::Py314)
    }

    #[cfg(test)]
    pub(super) fn analyze_with_python_version(
        body: &[Stmt],
        python_version: PythonVersion,
    ) -> Self {
        Self::analyze_with_source(
            body,
            python_version,
            &mut SourceAnalysis::new(python_version, 0),
        )
    }

    pub(super) fn analyze_with_source<'ast>(
        body: &'ast [Stmt],
        python_version: PythonVersion,
        source: &mut SourceAnalysis<'ast>,
    ) -> Self {
        Self::analyze_with_source_options(body, python_version, source, AssertionMode::Keep)
    }

    pub(super) fn analyze_with_optimized_assertions<'ast>(
        body: &'ast [Stmt],
        python_version: PythonVersion,
        source: &mut SourceAnalysis<'ast>,
    ) -> Self {
        Self::analyze_with_source_options(body, python_version, source, AssertionMode::Elide)
    }

    fn analyze_with_source_options<'ast>(
        body: &'ast [Stmt],
        python_version: PythonVersion,
        source: &mut SourceAnalysis<'ast>,
        assertion_mode: AssertionMode,
    ) -> Self {
        ScopeInputs::collect(body, python_version, source, assertion_mode, true).build()
    }

    pub(super) const fn module(&self) -> &ModulePlan {
        &self.module
    }

    fn build_scopes(&mut self, definitions: Vec<ScopeBuildInput<'_>>, future_annotations: bool) {
        self.nodes.raw.reserve(definitions.len());
        self.by_parent_and_origin.reserve(definitions.len());
        for (index, input) in definitions.iter().enumerate() {
            let origin = match input.definition {
                ScopeDefinition::Function(definition, _, _) => ScopeOrigin::function(definition),
                ScopeDefinition::Class(definition, _) => ScopeOrigin::class(definition),
            };
            let id = self.add_scope(input.parent, origin);
            debug_assert_eq!(id.index(), index + 1);
        }

        for (index, input) in definitions.into_iter().enumerate().rev() {
            let id = ScopeId::from_usize(index + 1);
            debug_assert!(
                self.nodes[id]
                    .children
                    .iter()
                    .all(|child| !matches!(self.nodes[*child].plan, ScopePlan::Pending))
            );
            match input.definition {
                ScopeDefinition::Function(definition, flat, private_name) => {
                    self.build_function(
                        id,
                        input.parent,
                        definition,
                        flat,
                        future_annotations,
                        private_name.as_deref(),
                    );
                }
                ScopeDefinition::Class(definition, enclosing_private_name) => {
                    self.build_class(
                        id,
                        definition,
                        future_annotations,
                        enclosing_private_name.as_deref(),
                    );
                }
            }
        }
    }

    fn add_scope(&mut self, parent: ScopeId, origin: ScopeOrigin) -> ScopeId {
        let id = self.nodes.next_index();
        self.nodes.push(ScopeNode {
            parent: Some(parent),
            plan: ScopePlan::Pending,
            children: Vec::new(),
        });
        self.nodes[parent].children.push(id);
        self.by_parent_and_origin.insert((parent, origin), id);
        id
    }

    fn build_function(
        &mut self,
        id: ScopeId,
        parent: ScopeId,
        definition: &StmtFunctionDef,
        flat: Option<FlatFunctionInputs>,
        future_annotations: bool,
        private_name: Option<&str>,
    ) {
        // Flat bodies have no closure or evaluation-order edge cases. Their runtime bindings
        // were already collected; a nongeneric function's own annotations are separate.
        // Eliding assertions preserves local ordering when each bound name first occurs outside
        // them. Private aliases can share a binding, so keep those scopes on the complete path.
        if let Some(inputs) = flat.filter(|inputs| {
            self.assertion_mode == AssertionMode::Keep
                || !inputs.has_assertions
                || inputs.names.iter().all(|(_, bound, in_assertion)| {
                    !bound || (!in_assertion && private_name.is_none())
                })
        }) {
            let annotation_references = if inputs.has_annotations && !future_annotations {
                self.names.intern_set(FunctionPlan::annotation_references(
                    definition,
                    private_name,
                ))
            } else {
                FxHashSet::default()
            };
            if private_name.is_none()
                || !inputs.names.iter().any(|(name, ..)| {
                    mangle_name(self.names.resolve(*name), private_name)
                        != self.names.resolve(*name)
                })
            {
                let mut locals = Vec::with_capacity(inputs.names.len());
                let mut required = FxHashSet::default();
                required.reserve(inputs.names.len());
                for (name, bound, _) in inputs.names {
                    if bound {
                        locals.push(name);
                    } else {
                        required.insert(name);
                    }
                }
                if inputs.implicit_class_reference {
                    let class = self.names.get("__class__").expect("__class__ is seeded");
                    if !locals.contains(&class) {
                        required.insert(class);
                    }
                }
                let lexical_bindings = locals.iter().copied().collect();
                self.nodes[id].plan = ScopePlan::Function(FunctionPlan {
                    locals,
                    lexical_bindings,
                    annotation_references,
                    required,
                    ..FunctionPlan::default()
                });
                return;
            }
            let mut ordered_names: Vec<_> = inputs
                .names
                .iter()
                .map(|(name, ..)| Name::new(self.names.resolve(*name)))
                .collect();
            let local_aliases =
                coalesce_private_locals(&mut ordered_names, private_name, std::iter::empty());
            let bound: FxHashSet<_> = inputs
                .names
                .iter()
                .filter(|(_, bound, _)| *bound)
                .map(|(name, ..)| mangle_name(self.names.resolve(*name), private_name).into_owned())
                .collect();
            let mut locals = Vec::with_capacity(inputs.names.len());
            let mut required = FxHashSet::default();
            required.reserve(inputs.names.len());
            for name in ordered_names {
                let id = self.names.get(&name).expect("collected names are interned");
                if bound.contains(mangle_name(&name, private_name).as_ref()) {
                    locals.push(id);
                }
            }
            required.extend(
                inputs
                    .names
                    .iter()
                    .filter(|(name, ..)| {
                        !bound
                            .contains(mangle_name(self.names.resolve(*name), private_name).as_ref())
                    })
                    .map(|(name, ..)| *name),
            );
            if inputs.implicit_class_reference {
                let class = self.names.get("__class__").expect("__class__ is seeded");
                if !locals.contains(&class) {
                    required.insert(class);
                }
            }
            let local_aliases = local_aliases
                .into_iter()
                .filter_map(|(alias, original)| {
                    let original = self
                        .names
                        .get(&original)
                        .expect("alias representative is interned");
                    locals
                        .contains(&original)
                        .then(|| (self.names.get(&alias).expect("alias is interned"), original))
                })
                .collect();
            let lexical_bindings = locals
                .iter()
                .map(|name| {
                    let spelling = mangle_name(self.names.resolve(*name), private_name);
                    self.names
                        .get(&spelling)
                        .expect("canonical local names are interned")
                })
                .collect();
            self.nodes[id].plan = ScopePlan::Function(FunctionPlan {
                locals,
                local_aliases,
                lexical_bindings,
                annotation_references,
                required,
                ..FunctionPlan::default()
            });
            return;
        }

        let eager_annotations = !self.deferred_annotations && !future_annotations;
        let facts = ScopeBodyFactsCollector::collect(
            &definition.body,
            true,
            ScopeBodyContext::Function,
            eager_annotations,
            self.deferred_annotations && !future_annotations,
            private_name,
        );
        let (nested_function_requirements, nested_function_annotation_references) =
            self.nested_function_requirements(id);
        let (mut class_requirements, unmangled_requirements) = self.nested_class_requirements(id);
        class_requirements.extend(unmangled_requirements);
        let plan = FunctionPlan::build(
            &mut self.names,
            definition,
            parent == ScopeId::MODULE,
            future_annotations,
            eager_annotations,
            self.assertion_mode,
            facts,
            private_name,
            &nested_function_requirements,
            &nested_function_annotation_references,
            &class_requirements,
        );
        self.nodes[id].plan = ScopePlan::Function(plan);
    }

    fn build_class(
        &mut self,
        id: ScopeId,
        definition: &StmtClassDef,
        future_annotations: bool,
        enclosing_private_name: Option<&str>,
    ) {
        let mut facts = ScopeBodyFactsCollector::collect(
            &definition.body,
            future_annotations,
            ScopeBodyContext::Class,
            !self.deferred_annotations && !future_annotations,
            false,
            Some(definition.name.as_str()),
        );
        if self.python_version == PythonVersion::Py312 {
            // Python 3.12 rejects comprehensions in class-visible annotation scopes.
            facts.annotation_comprehension_requirements =
                AnnotationComprehensionRequirements::default();
        }
        let (method_requirements, method_annotation_references) =
            self.nested_function_requirements(id);
        let (nested_class_requirements, nested_unmangled_requirements) =
            self.nested_class_requirements(id);
        let dunder_class = self.names.get("__class__");
        let child_needs_class_closure = self.nodes[id].children.iter().any(|child| {
            dunder_class.is_some_and(|dunder_class| match &self.nodes[*child].plan {
                ScopePlan::Function(plan) => plan.required.contains(&dunder_class),
                ScopePlan::Class(plan) => plan.required.contains(&dunder_class),
                ScopePlan::Module => false,
                ScopePlan::Pending => unreachable!("child scope plan is not built"),
            })
        });
        let mut plan = ClassPlan::build(
            &mut self.names,
            definition,
            future_annotations,
            self.deferred_annotations,
            facts,
            &method_requirements,
            &method_annotation_references,
            &nested_class_requirements,
            &nested_unmangled_requirements,
            child_needs_class_closure,
        );
        if enclosing_private_name.map(|name| name.trim_start_matches('_'))
            != Some(definition.name.as_str().trim_start_matches('_'))
        {
            // Keep raw identifiers inside the class, but resolve its private requirements
            // in the enclosing scope using the spelling established by this class.
            plan.enclosing_names = plan
                .required
                .iter()
                .filter_map(|&name| {
                    let spelling = self.names.resolve(name);
                    if definition.type_params.as_ref().is_some_and(|parameters| {
                        parameters
                            .iter()
                            .any(|parameter| parameter.name().as_str() == spelling)
                    }) {
                        return None;
                    }
                    let Cow::Owned(mangled) = mangle_name(spelling, Some(definition.name.as_str()))
                    else {
                        return None;
                    };
                    let enclosing = self
                        .names
                        .get(&mangled)
                        .expect("class name collection interns mangled requirements");
                    Some((name, enclosing))
                })
                .collect();
        }
        self.nodes[id].plan = ScopePlan::Class(plan);
    }

    fn nested_function_requirements(
        &self,
        parent: ScopeId,
    ) -> (FxHashSet<NameId>, FxHashSet<NameId>) {
        let mut required = FxHashSet::default();
        let mut annotation_references = FxHashSet::default();
        for child in &self.nodes[parent].children {
            let ScopePlan::Function(plan) = &self.nodes[*child].plan else {
                continue;
            };
            required.extend(
                plan.required
                    .iter()
                    .filter(|name| !plan.type_parameter_names.contains(*name))
                    .copied(),
            );
            if self.deferred_annotations || !plan.type_parameter_names.is_empty() {
                annotation_references.extend(
                    plan.annotation_references
                        .iter()
                        .filter(|name| !plan.type_parameter_names.contains(*name))
                        .copied(),
                );
            }
        }
        (required, annotation_references)
    }

    fn nested_class_requirements(&self, parent: ScopeId) -> (FxHashSet<NameId>, FxHashSet<NameId>) {
        let mut required = FxHashSet::default();
        let mut unmangled_required = FxHashSet::default();
        for child in &self.nodes[parent].children {
            let ScopePlan::Class(plan) = &self.nodes[*child].plan else {
                continue;
            };
            required.extend(
                plan.required
                    .iter()
                    // The synthetic generic scope provides these cells to the class.
                    .filter(|name| {
                        !plan.type_parameter_names.contains(*name)
                            && !plan.canonical_type_parameter_names.contains(*name)
                    })
                    .map(|name| plan.enclosing_names.get(name).copied().unwrap_or(*name)),
            );
            unmangled_required.extend(
                plan.unmangled_required
                    .iter()
                    .filter(|name| !plan.canonical_type_parameter_names.contains(*name))
                    .copied(),
            );
        }
        (required, unmangled_required)
    }

    fn child(&self, parent: ScopeId, origin: ScopeOrigin) -> Option<ScopeId> {
        self.by_parent_and_origin.get(&(parent, origin)).copied()
    }

    /// Class locals do not bind names for methods. An explicit function global stops
    /// the search even when an outer function happens to bind the same name.
    fn enclosing_function_binds(&self, id: ScopeId, name: NameId) -> bool {
        let mut parent = self.nodes[id].parent;
        while let Some(id) = parent {
            let node = &self.nodes[id];
            match &node.plan {
                ScopePlan::Pending => unreachable!("scope plan is not built"),
                ScopePlan::Module => return false,
                ScopePlan::Function(plan) => {
                    if plan.globals.contains(&name) {
                        return false;
                    }
                    if plan.lexical_bindings.contains(&name)
                        || plan.type_parameter_names.contains(&name)
                    {
                        return true;
                    }
                }
                ScopePlan::Class(plan) => {
                    if self.names.resolve(name) == "__class__"
                        || plan.type_parameter_names.contains(&name)
                    {
                        return true;
                    }
                }
            }
            parent = node.parent;
        }
        false
    }

    fn function_or_enclosing_binds(&self, id: ScopeId, name: NameId) -> bool {
        match &self.nodes[id].plan {
            ScopePlan::Pending => unreachable!("scope plan is not built"),
            ScopePlan::Module => return false,
            ScopePlan::Function(plan) => {
                if plan.globals.contains(&name) {
                    return false;
                }
                if plan.lexical_bindings.contains(&name)
                    || plan.type_parameter_names.contains(&name)
                {
                    return true;
                }
            }
            ScopePlan::Class(plan) => {
                if self.names.resolve(name) == "__class__"
                    || plan.type_parameter_names.contains(&name)
                {
                    return true;
                }
            }
        }
        self.enclosing_function_binds(id, name)
    }

    pub(super) fn function(&self, id: ScopeId) -> Option<&FunctionPlan> {
        match &self.nodes.get(id)?.plan {
            ScopePlan::Pending => unreachable!("scope plan is not built"),
            ScopePlan::Function(plan) => Some(plan),
            ScopePlan::Module | ScopePlan::Class(_) => None,
        }
    }

    fn class(&self, id: ScopeId) -> Option<&ClassPlan> {
        match &self.nodes.get(id)?.plan {
            ScopePlan::Pending => unreachable!("scope plan is not built"),
            ScopePlan::Class(plan) => Some(plan),
            ScopePlan::Module | ScopePlan::Function(_) => None,
        }
    }
}

struct ScopeInputs<'ast> {
    arena: ScopeArena,
    facts: ModulePlanBuilder,
    bindings: LocalCollector,
    definitions: Vec<ScopeBuildInput<'ast>>,
    future_flags: u32,
}

impl<'ast> ScopeInputs<'ast> {
    fn collect(
        body: &'ast [Stmt],
        python_version: PythonVersion,
        source: &mut SourceAnalysis<'ast>,
        assertion_mode: AssertionMode,
        collect_flat_inputs: bool,
    ) -> Self {
        #[cfg(test)]
        let collect_flat_inputs = collect_flat_inputs || FORCE_FULL_LOWERED_SCOPES.get();
        let future_flags = future_feature_flags(body);
        let future_annotations = future_flags & CO_FUTURE_ANNOTATIONS != 0;
        let deferred_annotations =
            !matches!(python_version, PythonVersion::Py312 | PythonVersion::Py313);
        let eager_annotations = !deferred_annotations && !future_annotations;
        let mut arena = ScopeArena {
            names: NameInterner::seeded(),
            deferred_annotations,
            python_version,
            assertion_mode,
            ..ScopeArena::default()
        };
        let (facts, definitions, requires_module_bindings) =
            ModuleNameCollector::collect_with_source(
                &mut arena.names,
                body,
                eager_annotations,
                source,
                collect_flat_inputs,
            );
        let mut bindings = LocalCollector {
            eager_function_annotations: eager_annotations,
            eager_statement_annotations: eager_annotations,
            module_references_super: Some(false),
            global_comprehension_saves: true,
            ..LocalCollector::default()
        };
        if requires_module_bindings {
            bindings.collect_suite(body);
        }
        Self {
            arena,
            facts,
            bindings,
            definitions,
            future_flags,
        }
    }

    fn build(mut self) -> ScopeArena {
        // Preorder allocation followed by reverse construction preserves lexical child order
        // and closure requirements without walking the statement tree a second time.
        self.arena.build_scopes(
            self.definitions,
            self.future_flags & CO_FUTURE_ANNOTATIONS != 0,
        );
        self.arena.module = ModulePlan::build(
            &self.arena.names,
            self.future_flags,
            self.facts,
            self.bindings,
        );
        self.arena
    }
}

struct ScopeBuildInput<'ast> {
    parent: ScopeId,
    definition: ScopeDefinition<'ast>,
}

enum ScopeDefinition<'ast> {
    Function(
        &'ast StmtFunctionDef,
        Option<FlatFunctionInputs>,
        Option<String>,
    ),
    Class(&'ast StmtClassDef, Option<String>),
}

struct ModuleNameCollector<'a, 'ast> {
    names: &'a mut NameInterner,
    source: &'a mut SourceAnalysis<'ast>,
    private_name: Option<String>,
    facts: ModulePlanBuilder,
    nested_scope_depth: usize,
    comprehension_depth: usize,
    generator_depth: usize,
    current_scope: ScopeId,
    in_module_header: bool,
    in_class_body: bool,
    requires_module_bindings: bool,
    flat_function: Option<FlatFunctionInputs>,
    collect_flat_inputs: bool,
    definitions: Vec<ScopeBuildInput<'ast>>,
    eager_annotations: bool,
}

#[derive(Debug)]
struct FlatFunctionInputs {
    // Preserve the first runtime occurrence of each name; a later store upgrades the existing
    // entry without moving it, matching CPython's load-before-store local ordering. The final bit
    // records whether that first occurrence was in an assertion.
    names: Vec<(NameId, bool, bool)>,
    name_positions: Option<FxHashMap<NameId, usize>>,
    has_annotations: bool,
    has_assertions: bool,
    in_assertion: bool,
    implicit_class_reference: bool,
    complex: bool,
}

impl FlatFunctionInputs {
    const LINEAR_SEARCH_LIMIT: usize = 8;

    fn record(&mut self, name: NameId, bound: bool) {
        if self.complex {
            return;
        }

        if let Some(name_positions) = &mut self.name_positions {
            if let Some(position) = name_positions.get(&name).copied() {
                self.names[position].1 |= bound;
            } else {
                name_positions.insert(name, self.names.len());
                self.names.push((name, bound, self.in_assertion));
            }
            return;
        }

        if let Some((_, was_bound, _)) = self
            .names
            .iter_mut()
            .find(|(existing, ..)| *existing == name)
        {
            *was_bound |= bound;
            return;
        }

        if self.names.len() < Self::LINEAR_SEARCH_LIMIT {
            self.names.push((name, bound, self.in_assertion));
            return;
        }

        let mut name_positions = FxHashMap::default();
        name_positions.reserve(self.names.len() + 1);
        name_positions.extend(
            self.names
                .iter()
                .enumerate()
                .map(|(position, (name, ..))| (*name, position)),
        );
        name_positions.insert(name, self.names.len());
        self.names.push((name, bound, self.in_assertion));
        self.name_positions = Some(name_positions);
    }

    fn mark_complex(&mut self) {
        if self.complex {
            return;
        }

        self.complex = true;
        self.names.clear();
        self.name_positions = None;
    }
}

/// An ordinary local annotation has no runtime names, but nested scopes and bindings still
/// participate in symbol analysis. Keep those annotations on the complete analysis path.
fn annotation_requires_full_scope_analysis(annotation: &Expr) -> bool {
    struct Collector(bool);

    impl<'ast> Visitor<'ast> for Collector {
        fn visit_expr(&mut self, expression: &'ast Expr) {
            if crate::stack_growth_required() {
                return crate::grow_stack(|| self.visit_expr(expression));
            }

            self.0 |= matches!(
                expression,
                Expr::Lambda(_)
                    | Expr::Generator(_)
                    | Expr::ListComp(_)
                    | Expr::SetComp(_)
                    | Expr::DictComp(_)
                    | Expr::Named(_)
                    | Expr::Await(_)
                    | Expr::Yield(_)
                    | Expr::YieldFrom(_)
            );
            if !self.0 {
                walk_expr(self, expression);
            }
        }
    }

    let mut collector = Collector(false);
    collector.visit_expr(annotation);
    collector.0
}

impl<'a, 'ast> ModuleNameCollector<'a, 'ast> {
    #[cfg(test)]
    fn collect(
        names: &'a mut NameInterner,
        body: &'ast [Stmt],
        eager_annotations: bool,
    ) -> (ModulePlanBuilder, Vec<ScopeBuildInput<'ast>>, bool) {
        ModuleNameCollector::collect_with_source(
            names,
            body,
            eager_annotations,
            &mut SourceAnalysis::new(PythonVersion::Py314, 0),
            true,
        )
    }

    fn collect_with_source(
        names: &'a mut NameInterner,
        body: &'ast [Stmt],
        eager_annotations: bool,
        source: &'a mut SourceAnalysis<'ast>,
        collect_flat_inputs: bool,
    ) -> (ModulePlanBuilder, Vec<ScopeBuildInput<'ast>>, bool) {
        let mut collector = Self {
            names,
            source,
            private_name: None,
            facts: ModulePlanBuilder::default(),
            nested_scope_depth: 0,
            comprehension_depth: 0,
            generator_depth: 0,
            current_scope: ScopeId::MODULE,
            in_module_header: false,
            in_class_body: false,
            requires_module_bindings: false,
            flat_function: None,
            collect_flat_inputs,
            definitions: Vec::new(),
            eager_annotations,
        };
        collector.collect_suite(body);
        (
            collector.facts,
            collector.definitions,
            collector.requires_module_bindings,
        )
    }

    fn intern(&mut self, name: &str) -> NameId {
        self.intern_with(name, |names| names.intern(name))
    }

    fn intern_name(&mut self, name: &Name) -> NameId {
        self.intern_name_with_spelling(name, name.as_str())
    }

    fn intern_name_with_spelling(&mut self, name: &Name, spelling: &str) -> NameId {
        self.intern_with(spelling, |names| names.intern_name(name, spelling))
    }

    fn intern_with(
        &mut self,
        name: &str,
        intern: impl FnOnce(&mut NameInterner) -> NameId,
    ) -> NameId {
        // A module symbol named `super` disables specialized super calls. Be conservative
        // about nested/header occurrences so the module-local walk can be skipped
        // only when the sentinel is definitely irrelevant.
        self.requires_module_bindings |= name == "super";
        if self.private_name.is_none() {
            return intern(self.names);
        }

        let mangled = mangle_name(name, self.private_name.as_deref());
        let id = intern(self.names);
        if let Cow::Owned(mangled) = mangled {
            self.names.intern_owned(mangled);
        }
        id
    }

    fn record_flat(&mut self, name: NameId, bound: bool) {
        if self.collect_flat_inputs
            && let Some(flat) = &mut self.flat_function
        {
            flat.record(name, bound);
        }
    }

    fn record_flat_name(&mut self, name: &ruff_python_ast::ExprName) -> NameId {
        let spelling = name.id.as_str();
        let id = self.intern_name_with_spelling(&name.id, spelling);
        if spelling == "super" && name.ctx == ExprContext::Load {
            if let Some(flat) = &mut self.flat_function {
                // A load of super also requests __class__, even when super is shadowed.
                // Keep this out of the runtime name order: it is not a local occurrence.
                flat.implicit_class_reference = true;
            }
        }
        self.record_flat(id, name.ctx != ExprContext::Load);
        id
    }

    fn mark_flat_complex(&mut self) {
        if let Some(flat) = &mut self.flat_function {
            flat.mark_complex();
        }
    }

    fn collect_suite(&mut self, body: &'ast [Stmt]) {
        for statement in body {
            self.visit_stmt(statement);
        }
    }

    fn collect_parameters(&mut self, parameters: &ruff_python_ast::Parameters) {
        for parameter in parameters_in_locals_order(parameters) {
            self.intern_name(&parameter.name.id);
        }
    }

    fn collect_type_parameters(&mut self, parameters: Option<&ruff_python_ast::TypeParams>) {
        if let Some(parameters) = parameters {
            for parameter in parameters {
                self.intern_name(&parameter.name().id);
            }
        }
    }
}

impl<'ast> Visitor<'ast> for ModuleNameCollector<'_, 'ast> {
    fn visit_stmt(&mut self, statement: &'ast Stmt) {
        if crate::stack_growth_required() {
            return crate::grow_stack(|| self.visit_stmt(statement));
        }

        self.source.observe_stmt(statement);
        let at_module_scope = self.nested_scope_depth == 0;
        if matches!(
            statement,
            Stmt::Match(_)
                | Stmt::Global(_)
                | Stmt::Nonlocal(_)
                | Stmt::TypeAlias(_)
                | Stmt::ClassDef(_)
        ) || matches!(statement, Stmt::Try(statement) if !statement.orelse.is_empty() || !statement.finalbody.is_empty())
        {
            self.mark_flat_complex();
        }
        match statement {
            Stmt::Assert(_) => {
                if let Some(flat) = &mut self.flat_function {
                    flat.has_assertions = true;
                    flat.in_assertion = true;
                }
                walk_stmt(self, statement);
                if let Some(flat) = &mut self.flat_function {
                    flat.in_assertion = false;
                }
                return;
            }
            Stmt::AnnAssign(assignment)
                if self
                    .flat_function
                    .as_ref()
                    .is_some_and(|flat| !flat.complex) =>
            {
                if !self.eager_annotations
                    && matches!(assignment.target.as_ref(), Expr::Name(_))
                    && let Some(value) = &assignment.value
                    && !annotation_requires_full_scope_analysis(&assignment.annotation)
                {
                    self.visit_expr(value);
                    // Preserve Ruff's value/annotation/target interning order, while excluding
                    // annotation names from the function's runtime local order and requirements.
                    let flat = self.flat_function.take();
                    self.visit_annotation(&assignment.annotation);
                    self.flat_function = flat;
                    self.visit_expr(&assignment.target);
                    return;
                }
                self.mark_flat_complex();
            }
            Stmt::AugAssign(assignment)
                if self
                    .flat_function
                    .as_ref()
                    .is_some_and(|flat| !flat.complex) =>
            {
                // Unlike ordinary assignment, the target is evaluated before the value. Ruff's
                // generic visitor visits them in the reverse order, which would reorder locals.
                self.visit_expr(&assignment.target);
                self.visit_expr(&assignment.value);
                return;
            }
            Stmt::FunctionDef(definition) => {
                self.mark_flat_complex();
                self.intern_name(&definition.name.id);
                let parent = self.current_scope;
                let scope = ScopeId::from_usize(self.definitions.len() + 1);
                self.definitions.push(ScopeBuildInput {
                    parent,
                    definition: ScopeDefinition::Function(
                        definition,
                        None,
                        self.private_name.clone(),
                    ),
                });
                self.current_scope = scope;
                let outer_flat = self.flat_function.take();
                let generic = definition.type_params.is_some();
                let mut flat = FlatFunctionInputs {
                    names: if self.collect_flat_inputs {
                        Vec::with_capacity(8)
                    } else {
                        Vec::new()
                    },
                    name_positions: None,
                    has_annotations: !generic
                        && (definition.returns.is_some()
                            || definition
                                .parameters
                                .iter()
                                .any(|parameter| parameter.annotation().is_some())),
                    has_assertions: false,
                    in_assertion: false,
                    implicit_class_reference: false,
                    complex: generic,
                };
                for parameter in parameters_in_locals_order(&definition.parameters) {
                    let name = self.intern_name(&parameter.name.id);
                    if self.collect_flat_inputs {
                        flat.record(name, true);
                    }
                }
                self.collect_type_parameters(definition.type_params.as_deref());
                self.nested_scope_depth += 1;
                let outer_header = self.in_module_header;
                self.in_module_header |= at_module_scope;
                for decorator in &definition.decorator_list {
                    if at_module_scope {
                        self.facts.comprehension_cell_names.extend(
                            inlined_comprehension_cell_names_in_expression(&decorator.expression),
                        );
                    }
                    self.visit_decorator(decorator);
                }
                if at_module_scope {
                    for default in function_default_expressions(definition) {
                        self.facts
                            .comprehension_cell_names
                            .extend(inlined_comprehension_cell_names_in_expression(default));
                    }
                    if self.eager_annotations && definition.type_params.is_none() {
                        for annotation in function_annotation_expressions(definition) {
                            self.facts
                                .comprehension_cell_names
                                .extend(inlined_comprehension_cell_names_in_expression(annotation));
                        }
                    }
                }
                if let Some(type_params) = definition.type_params.as_deref() {
                    self.visit_type_params(type_params);
                }
                self.visit_parameters(&definition.parameters);
                if let Some(returns) = definition.returns.as_deref() {
                    self.visit_annotation(returns);
                }
                self.in_module_header = outer_header;
                // Keep traversal decisions identical even when the collected records are unused.
                self.flat_function = Some(flat);
                let outer_class_body = std::mem::replace(&mut self.in_class_body, false);
                self.collect_suite(&definition.body);
                self.in_class_body = outer_class_body;
                self.nested_scope_depth -= 1;
                let flat = self
                    .flat_function
                    .take()
                    .expect("function name collection should retain its flat inputs");
                if self.collect_flat_inputs && !flat.complex {
                    let ScopeDefinition::Function(_, inputs, _) =
                        &mut self.definitions[scope.index() - 1].definition
                    else {
                        unreachable!("function definition changed while collecting its body");
                    };
                    *inputs = Some(flat);
                }
                self.flat_function = outer_flat;
                self.current_scope = parent;
                return;
            }
            Stmt::ClassDef(definition) => {
                self.intern_name(&definition.name.id);
                let outer_class_body = std::mem::replace(&mut self.in_class_body, true);
                let parent = self.current_scope;
                self.current_scope = ScopeId::from_usize(self.definitions.len() + 1);
                self.definitions.push(ScopeBuildInput {
                    parent,
                    definition: ScopeDefinition::Class(definition, self.private_name.clone()),
                });
                self.nested_scope_depth += 1;
                let outer_header = self.in_module_header;
                self.in_module_header |= at_module_scope;
                for decorator in &definition.decorator_list {
                    if at_module_scope {
                        self.facts.comprehension_cell_names.extend(
                            inlined_comprehension_cell_names_in_expression(&decorator.expression),
                        );
                    }
                    self.visit_decorator(decorator);
                }
                // A generic class header executes in its own annotation scope, whose
                // private-name context is the class being defined. Decorators still
                // belong to the enclosing scope.
                let outer_source_class = self.source.enter_class_header(definition);
                let outer_private_name = self.private_name.clone();
                if definition.type_params.is_some() {
                    self.private_name = Some(definition.name.as_str().to_string());
                }
                self.collect_type_parameters(definition.type_params.as_deref());
                if let Some(type_params) = definition.type_params.as_deref() {
                    self.visit_type_params(type_params);
                }
                if let Some(arguments) = definition.arguments.as_deref() {
                    if at_module_scope && definition.type_params.is_none() {
                        for argument in &arguments.args {
                            self.facts
                                .comprehension_cell_names
                                .extend(inlined_comprehension_cell_names_in_expression(argument));
                        }
                        for keyword in &arguments.keywords {
                            self.facts.comprehension_cell_names.extend(
                                inlined_comprehension_cell_names_in_expression(&keyword.value),
                            );
                        }
                    }
                    self.visit_arguments(arguments);
                }
                self.in_module_header = outer_header;
                self.private_name = Some(definition.name.as_str().to_string());
                self.source.enter_class_body(definition);
                self.collect_suite(&definition.body);
                self.source.leave_class(outer_source_class);
                self.in_class_body = outer_class_body;
                self.private_name = outer_private_name;
                self.nested_scope_depth -= 1;
                self.current_scope = parent;
                return;
            }
            Stmt::TypeAlias(statement) => {
                self.collect_type_parameters(statement.type_params.as_deref());
            }
            Stmt::AnnAssign(annotation) if at_module_scope => {
                self.facts.has_annotations = true;
                self.facts.has_simple_annotations |= annotation.simple;
            }
            Stmt::Global(statement) => {
                for name in &statement.names {
                    self.intern_name(&name.id);
                    self.facts.module_globals.insert(
                        mangle_name(name.as_str(), self.private_name.as_deref()).into_owned(),
                    );
                }
            }
            Stmt::Nonlocal(statement) => {
                for name in &statement.names {
                    self.intern_name(&name.id);
                }
            }
            Stmt::Import(statement) => {
                for alias in &statement.names {
                    let module = alias.name.as_str();
                    self.intern_name(&alias.name.id);
                    for part in module.split('.').skip(1) {
                        self.intern(part);
                    }
                    let bound_name = alias.asname.as_ref().map_or_else(
                        || alias.name.as_str().split('.').next().unwrap_or(""),
                        |name| name.as_str(),
                    );
                    let id = self.intern(bound_name);
                    self.record_flat(id, true);
                    if at_module_scope {
                        self.facts
                            .imported_scope_names
                            .insert(bound_name.to_string());
                    }
                }
            }
            Stmt::ImportFrom(statement) => {
                self.intern(
                    statement
                        .module
                        .as_ref()
                        .map_or("", |module| module.as_str()),
                );
                for alias in &statement.names {
                    if alias.name.as_str() != "*" {
                        self.intern_name(&alias.name.id);
                        let bound_name = alias
                            .asname
                            .as_ref()
                            .map_or(alias.name.as_str(), |name| name.as_str());
                        let id = self.intern(bound_name);
                        self.record_flat(id, true);
                        // CPython's method-call optimization queries DEF_IMPORT on the module
                        // symbol table, where future feature names and aliases remain imports.
                        if at_module_scope {
                            self.facts
                                .imported_scope_names
                                .insert(bound_name.to_string());
                        }
                    }
                }
            }
            Stmt::Try(statement) => {
                for handler in &statement.handlers {
                    if let Some(handler) = handler.as_except_handler()
                        && let Some(name) = &handler.name
                    {
                        self.intern_name(&name.id);
                    }
                }
                if self
                    .flat_function
                    .as_ref()
                    .is_some_and(|flat| !flat.complex)
                {
                    // With no else or copied finally, runtime local order follows Ruff's body and
                    // handler traversal. Exception aliases bind after their handler's type.
                    self.visit_body(&statement.body);
                    for handler in &statement.handlers {
                        self.source.observe_except_handler(handler);
                        if let Some(handler) = handler.as_except_handler() {
                            if let Some(exception_type) = &handler.type_ {
                                self.visit_expr(exception_type);
                            }
                            if let Some(name) = &handler.name {
                                let spelling = name.as_str();
                                if spelling == "super" {
                                    self.mark_flat_complex();
                                }
                                let id = self.intern_name(&name.id);
                                self.record_flat(id, true);
                            }
                            self.visit_body(&handler.body);
                        }
                    }
                    return;
                }
            }
            _ => {}
        }
        walk_stmt(self, statement);
    }

    fn visit_expr(&mut self, expression: &'ast Expr) {
        if crate::stack_growth_required() {
            return crate::grow_stack(|| self.visit_expr(expression));
        }

        match expression {
            Expr::Name(name) => {
                let id = self.record_flat_name(name);
                self.source.observe_name_with_id(name, id);
                return;
            }
            Expr::Attribute(attribute) => {
                let id = self.intern_name(&attribute.attr.id);
                self.source.observe_attribute_with_id(attribute, id);
                if let Expr::Name(name) = attribute.value.as_ref() {
                    let id = self.record_flat_name(name);
                    self.source.observe_name_with_id(name, id);
                } else {
                    self.visit_expr(&attribute.value);
                }
                return;
            }
            Expr::StringLiteral(_)
            | Expr::BytesLiteral(_)
            | Expr::NumberLiteral(_)
            | Expr::BooleanLiteral(_)
            | Expr::NoneLiteral(_)
            | Expr::EllipsisLiteral(_)
            | Expr::IpyEscapeCommand(_) => return,
            _ => self.source.observe_expr(expression),
        }

        if matches!(expression, Expr::Yield(_) | Expr::YieldFrom(_)) {
            self.facts.yield_offsets.push(expression.start());
        }
        if self.in_class_body
            && matches!(
                expression,
                Expr::ListComp(_) | Expr::SetComp(_) | Expr::DictComp(_) | Expr::Generator(_)
            )
        {
            self.facts.has_class_comprehensions = true;
        }
        if !self.facts.has_suspension_expressions {
            let generators = match expression {
                Expr::Await(_) => {
                    self.facts.has_suspension_expressions = true;
                    None
                }
                Expr::ListComp(comprehension) => Some(&comprehension.generators[..]),
                Expr::SetComp(comprehension) => Some(&comprehension.generators[..]),
                Expr::DictComp(comprehension) => Some(&comprehension.generators[..]),
                _ => None,
            };
            if let Some(generators) = generators {
                self.facts.has_suspension_expressions |=
                    generators.iter().any(|generator| generator.is_async);
            }
        }
        self.requires_module_bindings |= (self.nested_scope_depth == 0 || self.in_module_header)
            && matches!(
                expression,
                Expr::ListComp(_) | Expr::SetComp(_) | Expr::DictComp(_)
            );
        if matches!(
            expression,
            Expr::Lambda(_)
                | Expr::Generator(_)
                | Expr::ListComp(_)
                | Expr::SetComp(_)
                | Expr::DictComp(_)
                | Expr::Named(_)
        ) {
            self.mark_flat_complex();
        }
        if let Expr::Lambda(lambda) = expression {
            if let Some(parameters) = lambda.parameters.as_deref() {
                self.collect_parameters(parameters);
            }
            self.nested_scope_depth += 1;
            let outer_header = self.in_module_header;
            self.in_module_header |= self.nested_scope_depth == 1;
            walk_expr(self, expression);
            self.in_module_header = outer_header;
            self.nested_scope_depth -= 1;
            return;
        }

        if self.nested_scope_depth == 0 && self.generator_depth == 0 {
            match expression {
                Expr::ListComp(comprehension) => {
                    self.facts
                        .comprehension_cell_names
                        .extend(comprehension_cell_names(
                            &comprehension.generators[..],
                            None,
                            &comprehension.elt,
                        ));
                }
                Expr::SetComp(comprehension) => {
                    self.facts
                        .comprehension_cell_names
                        .extend(comprehension_cell_names(
                            &comprehension.generators[..],
                            None,
                            &comprehension.elt,
                        ));
                }
                Expr::DictComp(comprehension) => {
                    self.facts
                        .comprehension_cell_names
                        .extend(comprehension_cell_names(
                            &comprehension.generators[..],
                            comprehension.key.as_deref(),
                            &comprehension.value,
                        ));
                }
                _ => {}
            }
        }
        if self.nested_scope_depth == 0
            && self.comprehension_depth > 0
            && let Expr::Named(named) = expression
            && let Expr::Name(name) = named.target.as_ref()
        {
            self.facts
                .module_globals
                .insert(name.id.as_str().to_string());
        }

        let is_generator = matches!(expression, Expr::Generator(_));
        let is_comprehension = is_generator
            || matches!(
                expression,
                Expr::ListComp(_) | Expr::SetComp(_) | Expr::DictComp(_)
            );
        if is_comprehension {
            self.comprehension_depth += 1;
            self.generator_depth += usize::from(is_generator);
            walk_expr(self, expression);
            self.generator_depth -= usize::from(is_generator);
            self.comprehension_depth -= 1;
            return;
        }
        walk_expr(self, expression);
    }

    fn visit_pattern(&mut self, pattern: &'ast Pattern) {
        self.source.observe_pattern(pattern);
        let name = match pattern {
            Pattern::MatchAs(pattern) => pattern.name.as_ref(),
            Pattern::MatchStar(pattern) => pattern.name.as_ref(),
            Pattern::MatchMapping(pattern) => pattern.rest.as_ref(),
            _ => None,
        };
        if let Some(name) = name {
            self.intern_name(&name.id);
        }
        walk_pattern(self, pattern);
    }

    fn visit_parameters(&mut self, parameters: &'ast ruff_python_ast::Parameters) {
        self.source.observe_parameters(parameters);
        ruff_python_ast::visitor::walk_parameters(self, parameters);
    }

    fn visit_parameter(&mut self, parameter: &'ast ruff_python_ast::Parameter) {
        self.source.observe_parameter(parameter);
        ruff_python_ast::visitor::walk_parameter(self, parameter);
    }

    fn visit_except_handler(&mut self, handler: &'ast ruff_python_ast::ExceptHandler) {
        self.source.observe_except_handler(handler);
        ruff_python_ast::visitor::walk_except_handler(self, handler);
    }

    fn visit_type_param(&mut self, parameter: &'ast TypeParam) {
        self.source.observe_type_param(parameter);
        ruff_python_ast::visitor::walk_type_param(self, parameter);
    }

    fn visit_keyword(&mut self, keyword: &'ast ruff_python_ast::Keyword) {
        self.source.observe_keyword(keyword);
        ruff_python_ast::visitor::walk_keyword(self, keyword);
    }

    fn visit_alias(&mut self, alias: &'ast ruff_python_ast::Alias) {
        self.source.observe_alias(alias);
        ruff_python_ast::visitor::walk_alias(self, alias);
    }

    fn visit_pattern_keyword(&mut self, keyword: &'ast ruff_python_ast::PatternKeyword) {
        self.source.observe_pattern_keyword(keyword);
        ruff_python_ast::visitor::walk_pattern_keyword(self, keyword);
    }
}

/// Visits parameters in CPython's local-slot order: positional-only, positional,
/// keyword-only, then variadic positional and keyword parameters. Keyword-only
/// parameters precede `*args` even though they follow it in the source.
///
/// ```python
/// def f(x, *args, flag=False, **kwargs): ...  # locals: x, flag, args, kwargs
/// ```
fn parameters_in_locals_order(
    parameters: &ruff_python_ast::Parameters,
) -> impl Iterator<Item = &ruff_python_ast::Parameter> {
    parameters
        .iter_non_variadic_params()
        .map(|parameter| &parameter.parameter)
        .chain(parameters.vararg.as_deref())
        .chain(parameters.kwarg.as_deref())
}

fn function_default_expressions(definition: &StmtFunctionDef) -> impl Iterator<Item = &Expr> {
    parameter_default_expressions(&definition.parameters)
}

// Eager annotation code generation evaluates ordinary arguments before positional-only
// arguments. Symbol analysis visits them in parameter order instead.
pub(super) fn function_annotation_expressions(
    definition: &StmtFunctionDef,
) -> impl Iterator<Item = &Expr> {
    definition
        .parameters
        .args
        .iter()
        .chain(&definition.parameters.posonlyargs)
        .filter_map(|parameter| parameter.parameter.annotation.as_deref())
        .chain(
            definition
                .parameters
                .vararg
                .iter()
                .filter_map(|parameter| parameter.annotation.as_deref()),
        )
        .chain(
            definition
                .parameters
                .kwonlyargs
                .iter()
                .filter_map(|parameter| parameter.parameter.annotation.as_deref()),
        )
        .chain(
            definition
                .parameters
                .kwarg
                .iter()
                .filter_map(|parameter| parameter.annotation.as_deref()),
        )
        .chain(definition.returns.as_deref())
}

pub(super) fn parameter_default_expressions(
    parameters: &ruff_python_ast::Parameters,
) -> impl Iterator<Item = &Expr> {
    parameters
        .iter_non_variadic_params()
        .filter_map(|parameter| parameter.default.as_deref())
}

fn visit_lambda_defaults<'ast>(
    visitor: &mut impl Visitor<'ast>,
    lambda: &'ast ruff_python_ast::ExprLambda,
) {
    if let Some(parameters) = lambda.parameters.as_deref() {
        for default in parameter_default_expressions(parameters) {
            visitor.visit_expr(default);
        }
    }
}

#[derive(Clone, Copy)]
enum LocalUnwind<'a> {
    Finally(&'a [Stmt]),
    Loop,
}

/// Preserve the first symbol position while making private spellings share its slot.
fn coalesce_private_locals<'a>(
    locals: &mut Vec<Name>,
    private_name: Option<&str>,
    references: impl IntoIterator<Item = &'a str>,
) -> Vec<(Name, Name)> {
    let Some(private_name) = private_name else {
        return Vec::new();
    };
    let mut groups: FxHashMap<String, Vec<Name>> = FxHashMap::default();
    locals.retain(|name| {
        let canonical = mangle_name(name, Some(private_name)).into_owned();
        let group = groups.entry(canonical).or_default();
        group.push(name.clone());
        group.len() == 1
    });
    for name in references {
        let canonical = mangle_name(name, Some(private_name));
        if let Some(group) = groups.get_mut(canonical.as_ref())
            && !group.iter().any(|existing| existing == name)
        {
            group.push(Name::new(name));
        }
    }
    let mut aliases = Vec::new();
    for original in locals.iter_mut() {
        let canonical = mangle_name(original, Some(private_name));
        let group = &groups[canonical.as_ref()];
        if group.len() > 1 {
            let representative = Name::new(canonical.as_ref());
            aliases.extend(
                group
                    .iter()
                    .filter(|name| **name != representative)
                    .map(|name| (name.clone(), representative.clone())),
            );
            *original = representative;
        }
    }
    aliases
}

#[derive(Clone, Debug, Default)]
struct LocalCollector {
    names: Vec<Name>,
    seen: FxHashSet<Name>,
    comprehension_targets: Vec<Name>,
    comprehension_iteration_targets: Vec<Name>,
    seen_comprehension_iteration_targets: FxHashSet<Name>,
    comprehension_annotation_only_predecessors: FxHashMap<Name, Vec<Name>>,
    seen_comprehension_targets: FxHashSet<Name>,
    comprehension_late_bindings: FxHashSet<Name>,
    comprehension_target_predecessors: FxHashMap<Name, Vec<Name>>,
    shadowed_nonlocal_cells: FxHashSet<String>,
    non_comprehension_bindings: FxHashSet<Name>,
    candidate_bindings: Option<FxHashMap<Name, bool>>,
    annotation_only: FxHashSet<Name>,
    globals: FxHashSet<String>,
    nonlocals: FxHashSet<String>,
    has_inlined_comprehension: bool,
    ignore_generator_body_comprehension_targets: bool,
    eager_function_annotations: bool,
    eager_statement_annotations: bool,
    module_references_super: Option<bool>,
    global_comprehension_saves: bool,
    private_name: Option<String>,
    legacy_class_comprehension_symbols: Option<Vec<(Name, bool)>>,
    elide_assertions: bool,
    elided_assertion: bool,
}

/// Returns the only other spelling with the same private symbol identity.
fn private_name_alias<'name>(name: &'name str, private_name: &str) -> Option<Cow<'name, str>> {
    match mangle_name(name, Some(private_name)) {
        Cow::Owned(canonical) => Some(Cow::Owned(canonical)),
        Cow::Borrowed(_) => name
            .strip_prefix('_')
            .and_then(|name| name.strip_prefix(private_name.trim_start_matches('_')))
            .filter(|raw| mangle_name(raw, Some(private_name)) == name)
            .map(Cow::Borrowed),
    }
}

fn reorder_comprehension_fast_cells<T>(
    locals: &mut Vec<T>,
    fast_cells: &[T],
    target_predecessors: &FxHashMap<T, Vec<T>>,
) where
    T: Clone + Eq + std::hash::Hash,
{
    let mut placed = FxHashSet::default();
    for cell in fast_cells {
        locals.retain(|candidate| candidate != cell);
        let mut predecessors = target_predecessors
            .get(cell)
            .into_iter()
            .flatten()
            .cloned()
            .collect::<FxHashSet<_>>();
        predecessors.extend(placed.iter().cloned());
        let index = locals
            .iter()
            .rposition(|candidate| predecessors.contains(candidate))
            .map_or(0, |index| index + 1);
        locals.insert(index, cell.clone());
        placed.insert(cell.clone());
    }
}

impl LocalCollector {
    fn deferred_nonlocal_comprehension_names(
        &self,
        generators: &[ruff_python_ast::Comprehension],
        key: Option<&Expr>,
        value: &Expr,
    ) -> FxHashSet<String> {
        if self.nonlocals.is_empty() {
            return FxHashSet::default();
        }
        let captured = comprehension_cell_names(generators, key, value);
        comprehension_name_bindings(generators, key, value)
            .into_iter()
            .filter_map(|(name, bound)| {
                (!bound
                    && self.nonlocals.contains(&name)
                    && (!captured.contains(&name) || self.shadowed_nonlocal_cells.contains(&name)))
                .then_some(name)
            })
            .collect()
    }

    /// Reserve only actual scope saves when a nested comprehension runs in a first iterable.
    fn collect_nested_comprehension_saves(&self, expression: &Expr, names: &mut Vec<String>) {
        struct Collector<'a> {
            locals: &'a LocalCollector,
            names: &'a mut Vec<String>,
        }

        impl<'ast> Visitor<'ast> for Collector<'_> {
            fn visit_expr(&mut self, expression: &'ast Expr) {
                if crate::stack_growth_required() {
                    return crate::grow_stack(|| self.visit_expr(expression));
                }

                let Some((generators, key, value)) = comprehension_parts(expression) else {
                    match expression {
                        Expr::Generator(generator) => {
                            if let Some(first) = generator.generators.first() {
                                self.visit_expr(&first.iter);
                            }
                            return;
                        }
                        Expr::Lambda(lambda) => {
                            visit_lambda_defaults(self, lambda);
                            return;
                        }
                        _ => {
                            walk_expr(self, expression);
                            return;
                        }
                    }
                };
                if let Some(first) = generators.first() {
                    self.visit_expr(&first.iter);
                }
                let deferred = self
                    .locals
                    .deferred_nonlocal_comprehension_names(generators, key, value);
                self.names.extend(
                    comprehension_temporary_names(generators, key, value)
                        .into_iter()
                        .filter(|name| !deferred.contains(name)),
                );
                // The first iterable was visited before this scope's saves. Walk only
                // the remaining runtime expressions so nested first iterables run once.
                for (index, generator) in generators.iter().enumerate() {
                    if index > 0 {
                        self.visit_expr(&generator.iter);
                    }
                    self.visit_expr(&generator.target);
                    for condition in &generator.ifs {
                        self.visit_expr(condition);
                    }
                }
                if let Some(key) = key {
                    self.visit_expr(key);
                }
                self.visit_expr(value);
            }
        }

        Collector {
            locals: self,
            names,
        }
        .visit_expr(expression);
    }

    fn insert_comprehension_target(&mut self, name: Name) {
        if self.seen_comprehension_targets.insert(name.clone()) {
            self.comprehension_annotation_only_predecessors
                .insert(name.clone(), self.annotation_only.iter().cloned().collect());
            if self.non_comprehension_bindings.contains(&name) {
                self.comprehension_late_bindings.insert(name.clone());
            }
            self.comprehension_target_predecessors.insert(
                name.clone(),
                self.names
                    .iter()
                    .filter(|predecessor| *predecessor != &name)
                    .cloned()
                    .collect(),
            );
            self.comprehension_targets.push(name);
        }
    }
    fn insert_comprehension_iteration_target(&mut self, name: Name) {
        if !self.seen_comprehension_iteration_targets.contains(&name)
            && self.seen_comprehension_targets.contains(&name)
        {
            // A containing-scope walrus store can precede the first inlined save of the
            // same name. Only the latter reserves its temporary fast-local position.
            self.comprehension_target_predecessors.insert(
                name.clone(),
                self.names
                    .iter()
                    .filter(|predecessor| *predecessor != &name)
                    .cloned()
                    .collect(),
            );
        }
        self.insert_comprehension_target(name.clone());
        if self
            .seen_comprehension_iteration_targets
            .insert(name.clone())
        {
            self.comprehension_iteration_targets.push(name);
        }
    }

    fn mark_binding(&mut self, name: &str) -> bool {
        if self.globals.contains(name) || self.nonlocals.contains(name) {
            return false;
        }
        self.mark_local_binding(name)
    }

    fn mark_local_binding(&mut self, name: &str) -> bool {
        if let Some(candidate_bindings) = &mut self.candidate_bindings {
            if let Some(binding) = candidate_bindings.get_mut(name) {
                *binding = true;
                return false;
            }
            candidate_bindings.insert(Name::new(name), true);
            self.names.push(Name::new(name));
            return true;
        }
        if self.seen.insert(Name::new(name)) {
            self.names.push(Name::new(name));
            true
        } else {
            false
        }
    }

    fn insert_candidate(&mut self, name: &str) {
        if self.globals.contains(name) || self.nonlocals.contains(name) {
            return;
        }
        self.claim_annotation_only_position(name);
        if self
            .candidate_bindings
            .as_ref()
            .is_some_and(|candidate_bindings| candidate_bindings.contains_key(name))
        {
            return;
        }
        let Some(candidate_bindings) = &mut self.candidate_bindings else {
            return;
        };
        candidate_bindings.insert(Name::new(name), false);
        self.names.push(Name::new(name));
    }

    fn claim_annotation_only_position(&mut self, name: &str) {
        // A no-value function annotation emits no fast-local operation in CPython. Keep its
        // symbol-table position provisional until the first runtime load or binding claims it.
        if self.annotation_only.is_empty() {
            return;
        }
        let annotation = if self.annotation_only.contains(name) {
            Name::new(name)
        } else if let Some(private_name) = self.private_name.as_deref() {
            let Some(annotation) = private_name_alias(name, private_name)
                .and_then(|alias| self.annotation_only.get(alias.as_ref()))
                .cloned()
            else {
                return;
            };
            annotation
        } else {
            return;
        };
        self.annotation_only.remove(&annotation);
        let index = self
            .names
            .iter()
            .position(|candidate| *candidate == annotation)
            .expect("an annotation-only local should have a candidate position");
        let name = self.names.remove(index);
        self.names.push(name);
    }

    fn retain_bindings(&mut self) {
        let Some(candidate_bindings) = self.candidate_bindings.take() else {
            return;
        };
        debug_assert_eq!(candidate_bindings.len(), self.names.len());
        if let Some(private_name) = self.private_name.as_deref() {
            self.names.retain(|name| {
                candidate_bindings[name]
                    || private_name_alias(name, private_name).is_some_and(|alias| {
                        candidate_bindings
                            .get(alias.as_ref())
                            .copied()
                            .unwrap_or_default()
                    })
            });
        } else {
            self.names.retain(|name| candidate_bindings[name]);
        }
    }

    fn insert(&mut self, name: &str) {
        // A nonlocal store does not bind the hidden fast local used by a later comprehension.
        if !self.nonlocals.contains(name) {
            self.non_comprehension_bindings.insert(Name::new(name));
        }
        self.claim_annotation_only_position(name);
        self.mark_binding(name);
    }

    fn insert_annotation_only(&mut self, name: &str) {
        self.non_comprehension_bindings.insert(Name::new(name));
        if self.mark_binding(name) {
            self.annotation_only.insert(Name::new(name));
        }
    }

    fn collect_suite(&mut self, body: &[Stmt]) {
        self.collect_suite_with_unwind(body, &[]);
    }

    fn collect_suite_with_unwind<'a>(&mut self, body: &'a [Stmt], unwind: &[LocalUnwind<'a>]) {
        for statement in body {
            match statement {
                Stmt::Assign(assignment) => {
                    if self.candidate_bindings.is_none() || !self.has_inlined_comprehension {
                        self.collect_expression(&assignment.value);
                    } else {
                        let mut bindings = FxHashSet::default();
                        for target in &assignment.targets {
                            let mut names = Vec::new();
                            collect_target_names(target, &mut names);
                            bindings.extend(names.into_iter().map(Name::from));
                        }
                        self.collect_assignment_expression(&assignment.value, bindings);
                    }
                    for target in &assignment.targets {
                        self.collect_target(target);
                    }
                }
                Stmt::AugAssign(assignment) => {
                    self.collect_target(&assignment.target);
                    self.collect_expression(&assignment.value);
                }
                Stmt::AnnAssign(assignment) => {
                    if let Some(value) = &assignment.value {
                        if self.candidate_bindings.is_none() || !self.has_inlined_comprehension {
                            self.collect_expression(value);
                        } else {
                            let mut names = Vec::new();
                            collect_target_names(&assignment.target, &mut names);
                            self.collect_assignment_expression(
                                value,
                                names.into_iter().map(Name::from).collect(),
                            );
                        }
                        self.collect_target(&assignment.target);
                    } else {
                        match assignment.target.as_ref() {
                            Expr::Name(name) if assignment.simple => {
                                self.insert_annotation_only(name.id.as_str());
                            }
                            Expr::Name(_) => {}
                            target => self.collect_target(target),
                        }
                    }
                    if self.eager_statement_annotations {
                        self.collect_expression(&assignment.annotation);
                    }
                }
                Stmt::FunctionDef(definition) => {
                    for decorator in &definition.decorator_list {
                        self.collect_definition_header_expression(&decorator.expression);
                    }
                    for default in function_default_expressions(definition) {
                        self.collect_definition_header_expression(default);
                    }
                    if self.eager_function_annotations && definition.type_params.is_none() {
                        for annotation in function_annotation_expressions(definition) {
                            self.collect_definition_header_expression(annotation);
                        }
                    }
                    self.insert(definition.name.as_str());
                }
                Stmt::ClassDef(definition) => {
                    for decorator in &definition.decorator_list {
                        self.collect_definition_header_expression(&decorator.expression);
                    }
                    if definition.type_params.is_none()
                        && let Some(arguments) = definition.arguments.as_deref()
                    {
                        for argument in &arguments.args {
                            self.collect_definition_header_expression(argument);
                        }
                        for keyword in &arguments.keywords {
                            self.collect_definition_header_expression(&keyword.value);
                        }
                    }
                    self.insert(definition.name.as_str());
                }
                Stmt::Delete(statement) => {
                    for target in &statement.targets {
                        self.collect_target(target);
                    }
                }
                Stmt::TypeAlias(statement) => {
                    if let Expr::Name(name) = statement.name.as_ref() {
                        self.insert(name.id.as_str());
                    }
                    // The value executes in its own annotation scope, so its
                    // comprehension targets cannot claim enclosing local slots.
                }
                Stmt::For(statement) => {
                    self.collect_expression(&statement.iter);
                    self.collect_target(&statement.target);
                    let mut loop_unwind = unwind.to_vec();
                    loop_unwind.push(LocalUnwind::Loop);
                    self.collect_suite_with_unwind(&statement.body, &loop_unwind);
                    self.collect_suite_with_unwind(&statement.orelse, unwind);
                }
                Stmt::Import(statement) => {
                    for alias in &statement.names {
                        self.insert(alias.asname.as_ref().map_or_else(
                            || alias.name.as_str().split('.').next().unwrap_or(""),
                            |name| name.as_str(),
                        ));
                    }
                }
                Stmt::ImportFrom(statement) => {
                    for alias in &statement.names {
                        if alias.name.as_str() != "*" {
                            self.insert(
                                alias
                                    .asname
                                    .as_ref()
                                    .map_or(alias.name.as_str(), |name| name.as_str()),
                            );
                        }
                    }
                }
                Stmt::If(statement) => {
                    self.collect_expression(&statement.test);
                    self.collect_suite_with_unwind(&statement.body, unwind);
                    for clause in &statement.elif_else_clauses {
                        if let Some(test) = &clause.test {
                            self.collect_expression(test);
                        }
                        self.collect_suite_with_unwind(&clause.body, unwind);
                    }
                }
                Stmt::While(statement) => {
                    self.collect_expression(&statement.test);
                    let mut loop_unwind = unwind.to_vec();
                    loop_unwind.push(LocalUnwind::Loop);
                    self.collect_suite_with_unwind(&statement.body, &loop_unwind);
                    self.collect_suite_with_unwind(&statement.orelse, unwind);
                }
                Stmt::Try(statement) => {
                    let mut finally_unwind = unwind.to_vec();
                    if !statement.finalbody.is_empty() {
                        finally_unwind.push(LocalUnwind::Finally(&statement.finalbody));
                    }
                    self.collect_suite_with_unwind(&statement.body, &finally_unwind);
                    // CPython emits the normal else path before moving exception handlers into
                    // cold blocks, so locals first bound there precede handler-only locals.
                    self.collect_suite_with_unwind(&statement.orelse, &finally_unwind);
                    for handler in &statement.handlers {
                        if let Some(handler) = handler.as_except_handler() {
                            if let Some(exception_type) = &handler.type_ {
                                self.collect_expression(exception_type);
                            }
                            if let Some(name) = &handler.name {
                                self.insert(name.as_str());
                            }
                            self.collect_suite_with_unwind(&handler.body, &finally_unwind);
                        }
                    }
                    self.collect_suite_with_unwind(&statement.finalbody, unwind);
                }
                Stmt::With(statement) => {
                    for item in &statement.items {
                        self.collect_expression(&item.context_expr);
                        if let Some(target) = &item.optional_vars {
                            self.collect_target(target);
                        }
                    }
                    self.collect_suite_with_unwind(&statement.body, unwind);
                }
                Stmt::Match(statement) => {
                    self.collect_expression(&statement.subject);
                    for case in &statement.cases {
                        self.collect_pattern(&case.pattern);
                        if let Some(guard) = &case.guard {
                            self.collect_expression(guard);
                        }
                        self.collect_suite_with_unwind(&case.body, unwind);
                    }
                }
                Stmt::Assert(statement) => {
                    if self.elide_assertions {
                        self.elided_assertion = true;
                        continue;
                    }
                    self.collect_expression(&statement.test);
                    if let Some(message) = &statement.msg {
                        self.collect_expression(message);
                    }
                }
                Stmt::Expr(statement) => self.collect_expression(&statement.value),
                Stmt::Raise(statement) => {
                    if let Some(exception) = &statement.exc {
                        self.collect_expression(exception);
                    }
                    if let Some(cause) = &statement.cause {
                        self.collect_expression(cause);
                    }
                }
                Stmt::Return(statement) => {
                    if let Some(value) = &statement.value {
                        self.collect_expression(value);
                    }
                    self.collect_unwind(unwind, false);
                }
                Stmt::Break(_) | Stmt::Continue(_) => self.collect_unwind(unwind, true),
                _ => {}
            }
        }
    }

    fn collect_unwind(&mut self, unwind: &[LocalUnwind<'_>], loop_exit: bool) {
        // CPython allocates fast locals when it first emits their operations. Cleanup copied
        // onto an early exit therefore claims its local positions before the remaining body.
        for (index, frame) in unwind.iter().enumerate().rev() {
            match frame {
                LocalUnwind::Finally(body) => {
                    self.collect_suite_with_unwind(body, &unwind[..index]);
                }
                LocalUnwind::Loop if loop_exit => break,
                LocalUnwind::Loop => {}
            }
        }
    }

    fn collect_target(&mut self, target: &Expr) {
        match target {
            Expr::Name(name) => self.insert(name.id.as_str()),
            Expr::List(list) => {
                for element in &list.elts {
                    self.collect_target(element);
                }
            }
            Expr::Tuple(tuple) => {
                for element in &tuple.elts {
                    self.collect_target(element);
                }
            }
            Expr::Starred(starred) => self.collect_target(&starred.value),
            Expr::Attribute(attribute) => self.collect_expression(&attribute.value),
            Expr::Subscript(subscript) => {
                self.collect_expression(&subscript.value);
                self.collect_expression(&subscript.slice);
            }
            _ => {}
        }
    }

    fn collect_expression(&mut self, expression: &Expr) {
        NamedExpressionCollector {
            collector: self,
            in_inlined_comprehension: false,
            in_generator_body: false,
            collect_known_loads: true,
            named_target_after_value: false,
            known_assignment_bindings: FxHashSet::default(),
            ignored_candidate_loads: FxHashSet::default(),
        }
        .visit_expr(expression);
    }

    fn collect_assignment_expression(
        &mut self,
        expression: &Expr,
        known_assignment_bindings: FxHashSet<Name>,
    ) {
        NamedExpressionCollector {
            collector: self,
            in_inlined_comprehension: false,
            in_generator_body: false,
            collect_known_loads: true,
            named_target_after_value: false,
            known_assignment_bindings,
            ignored_candidate_loads: FxHashSet::default(),
        }
        .visit_expr(expression);
    }

    fn collect_definition_header_expression(&mut self, expression: &Expr) {
        NamedExpressionCollector {
            collector: self,
            in_inlined_comprehension: false,
            in_generator_body: false,
            collect_known_loads: true,
            named_target_after_value: true,
            known_assignment_bindings: FxHashSet::default(),
            ignored_candidate_loads: FxHashSet::default(),
        }
        .visit_expr(expression);
    }

    fn collect_pattern(&mut self, pattern: &Pattern) {
        match pattern {
            Pattern::MatchValue(pattern) => self.collect_expression(&pattern.value),
            Pattern::MatchSingleton(_) => {}
            Pattern::MatchSequence(pattern) => {
                for pattern in &pattern.patterns {
                    self.collect_pattern(pattern);
                }
            }
            Pattern::MatchMapping(pattern) => {
                for key in &pattern.keys {
                    self.collect_expression(key);
                }
                for pattern in &pattern.patterns {
                    self.collect_pattern(pattern);
                }
                if let Some(rest) = &pattern.rest {
                    self.insert(rest.as_str());
                }
            }
            Pattern::MatchClass(pattern) => {
                self.collect_expression(&pattern.cls);
                for argument in &pattern.arguments.patterns {
                    self.collect_pattern(argument);
                }
                for keyword in &pattern.arguments.keywords {
                    self.collect_pattern(&keyword.pattern);
                }
            }
            Pattern::MatchStar(pattern) => {
                if let Some(name) = &pattern.name {
                    self.insert(name.as_str());
                }
            }
            Pattern::MatchAs(pattern) => {
                if let Some(inner) = &pattern.pattern {
                    self.collect_pattern(inner);
                }
                if let Some(name) = &pattern.name {
                    self.insert(name.as_str());
                }
            }
            Pattern::MatchOr(pattern) => {
                for pattern in &pattern.patterns {
                    self.collect_pattern(pattern);
                }
            }
        }
    }
}

struct NamedExpressionCollector<'a> {
    collector: &'a mut LocalCollector,
    in_inlined_comprehension: bool,
    in_generator_body: bool,
    collect_known_loads: bool,
    named_target_after_value: bool,
    known_assignment_bindings: FxHashSet<Name>,
    ignored_candidate_loads: FxHashSet<Name>,
}

/// Scope collectors ignore attribute spellings and expression contexts along the chain.
#[inline]
fn attribute_base(attribute: &ruff_python_ast::ExprAttribute) -> &Expr {
    let mut base = attribute.value.as_ref();
    while let Expr::Attribute(attribute) = base {
        base = attribute.value.as_ref();
    }
    base
}

impl<'ast> Visitor<'ast> for NamedExpressionCollector<'_> {
    fn visit_expr(&mut self, expression: &'ast Expr) {
        if crate::stack_growth_required() {
            return crate::grow_stack(|| self.visit_expr(expression));
        }

        match expression {
            Expr::Name(name) => {
                if self.collect_known_loads && name.ctx == ExprContext::Load {
                    if let Some(references_super) = &mut self.collector.module_references_super {
                        *references_super |= name.id.as_str() == "super";
                    }
                    if !self.ignored_candidate_loads.contains(name.id.as_str()) {
                        self.collector.insert_candidate(name.id.as_str());
                    }
                }
                return;
            }
            Expr::Attribute(attribute) => {
                self.visit_expr(attribute_base(attribute));
                return;
            }
            Expr::StringLiteral(_)
            | Expr::BytesLiteral(_)
            | Expr::NumberLiteral(_)
            | Expr::BooleanLiteral(_)
            | Expr::NoneLiteral(_)
            | Expr::EllipsisLiteral(_)
            | Expr::IpyEscapeCommand(_) => return,
            _ => {}
        }
        if let Expr::Lambda(lambda) = expression {
            visit_lambda_defaults(self, lambda);
            return;
        }
        if let Expr::Generator(generator) = expression {
            let previous = self.in_inlined_comprehension;
            if let Some(first) = generator.generators.first() {
                self.visit_expr(&first.iter);
            }
            self.in_inlined_comprehension = false;
            let previous_loads = std::mem::replace(&mut self.collect_known_loads, false);
            let previous_generator = std::mem::replace(&mut self.in_generator_body, true);
            if !self.collector.ignore_generator_body_comprehension_targets {
                walk_expr(self, expression);
            }
            self.in_generator_body = previous_generator;
            self.collect_known_loads = previous_loads;
            self.in_inlined_comprehension = previous;
            return;
        }
        if self.named_target_after_value
            && let Expr::Named(named) = expression
        {
            self.visit_expr(&named.value);
            if self.in_inlined_comprehension
                && let Expr::Name(name) = named.target.as_ref()
            {
                self.collector
                    .insert_comprehension_target(Name::new(name.id.as_str()));
            }
            self.collector.collect_target(&named.target);
            return;
        }
        let generators = match expression {
            Expr::ListComp(comprehension) => Some(&comprehension.generators[..]),
            Expr::SetComp(comprehension) => Some(&comprehension.generators[..]),
            Expr::DictComp(comprehension) => Some(&comprehension.generators[..]),
            _ => None,
        };
        if let Some(generators) = generators {
            if self.in_generator_body {
                // Walrus targets bind in the containing function, but temporary locals in
                // comprehensions evaluated by a generator belong to the generator's scope.
                walk_expr(self, expression);
                return;
            }
            if !self.in_inlined_comprehension {
                // CPython evaluates the outermost iterable before reserving the inlined targets.
                // Target names without a known outer binding are ignored during this early walk
                // so a global reference does not claim the later temporary's fast-local position.
                let mut target_names = Vec::new();
                for generator in generators {
                    collect_target_names(&generator.target, &mut target_names);
                }
                let previous_ignored = self.ignored_candidate_loads.clone();
                self.ignored_candidate_loads.extend(
                    target_names.into_iter().map(Name::from).filter(|name| {
                        !self.collector.non_comprehension_bindings.contains(name)
                            && !self.known_assignment_bindings.contains(name)
                    }),
                );
                if let Some(first) = generators.first() {
                    self.visit_expr(&first.iter);
                }
                self.ignored_candidate_loads = previous_ignored;
            }

            if let Some(first) = generators.first() {
                let mut names = Vec::new();
                if self.collector.nonlocals.is_empty() {
                    collect_nested_comprehension_target_names(&first.iter, &mut names);
                } else {
                    self.collector
                        .collect_nested_comprehension_saves(&first.iter, &mut names);
                }
                for name in names.into_iter().map(Name::from) {
                    // The first iterable executes before the enclosing comprehension binds its
                    // target. Inlined comprehensions there therefore allocate their temporary
                    // fast locals first; the later full expression walk only observes them
                    // after the enclosing targets have already been collected.
                    self.collector
                        .insert_comprehension_iteration_target(name.clone());
                    self.collector.claim_annotation_only_position(&name);
                    self.collector.mark_binding(&name);
                }
            }
            let (key, value) = match expression {
                Expr::ListComp(comprehension) => (None, comprehension.elt.as_ref()),
                Expr::SetComp(comprehension) => (None, comprehension.elt.as_ref()),
                Expr::DictComp(comprehension) => {
                    (comprehension.key.as_deref(), comprehension.value.as_ref())
                }
                _ => unreachable!(),
            };
            if !self.in_inlined_comprehension
                && let Some(symbols) = &mut self.collector.legacy_class_comprehension_symbols
            {
                for (name, requires_free) in
                    legacy_class_comprehension_names(generators, key, value)
                {
                    let symbol = (Name::from(name), requires_free);
                    if !symbols.contains(&symbol) {
                        symbols.push(symbol);
                    }
                }
            }
            let deferred_nonlocal_names = self
                .collector
                .deferred_nonlocal_comprehension_names(generators, key, value);
            // Reserve current-scope saves before visiting children. An explicit nonlocal
            // reference retains its outer value until the child that actually binds it.
            let iteration_names = comprehension_temporary_names(generators, key, value);
            let module_saves = self
                .collector
                .global_comprehension_saves
                .then(|| {
                    global_comprehension_temporary_names(
                        generators,
                        key,
                        value,
                        |name| {
                            self.collector.candidate_bindings.is_none()
                                || self.collector.globals.contains(name)
                        },
                        self.collector.private_name.as_deref(),
                    )
                })
                .flatten();
            let module_iteration_names = module_saves
                .as_ref()
                .map(|_| iteration_names.iter().cloned().collect::<FxHashSet<_>>());
            let temporary_names = module_saves.unwrap_or(iteration_names);
            let mut previous_target_names = Vec::new();
            for name in temporary_names
                .into_iter()
                .filter(|name| !deferred_nonlocal_names.contains(name))
                .map(Name::from)
            {
                let is_new_target = !self.collector.seen_comprehension_targets.contains(&name);
                if module_iteration_names
                    .as_ref()
                    .is_none_or(|names| names.contains(name.as_str()))
                {
                    self.collector
                        .insert_comprehension_iteration_target(name.clone());
                } else {
                    self.collector.insert_comprehension_target(name.clone());
                }
                if is_new_target
                    && self.collector.comprehension_late_bindings.contains(&name)
                    && let Some(predecessors) = self
                        .collector
                        .comprehension_target_predecessors
                        .get_mut(&name)
                {
                    predecessors.extend(previous_target_names.iter().cloned());
                }
                previous_target_names.push(name.clone());
                self.collector.claim_annotation_only_position(&name);
                if self.collector.global_comprehension_saves
                    && self.collector.globals.contains(name.as_str())
                {
                    self.collector.mark_local_binding(&name);
                } else {
                    self.collector.mark_binding(&name);
                }
            }
            let previous = std::mem::replace(&mut self.in_inlined_comprehension, true);
            walk_expr(self, expression);
            self.in_inlined_comprehension = previous;
            return;
        }
        if let Expr::Named(named) = expression {
            // CPython allocates locals referenced by the value before the walrus target.
            walk_expr(self, expression);

            if self.in_inlined_comprehension
                && let Expr::Name(name) = named.target.as_ref()
            {
                self.collector
                    .insert_comprehension_target(Name::new(name.id.as_str()));
            }
            self.collector.collect_target(&named.target);
            return;
        }
        walk_expr(self, expression);
    }
}

#[cfg(test)]
impl ScopeBodyFacts {
    pub(super) fn for_function(body: &[Stmt]) -> Self {
        ScopeBodyFactsCollector::collect(body, true, ScopeBodyContext::Function, false, true, None)
    }

    pub(super) fn for_class(body: &[Stmt], future_annotations: bool) -> Self {
        ScopeBodyFactsCollector::collect(
            body,
            future_annotations,
            ScopeBodyContext::Class,
            false,
            false,
            None,
        )
    }
}

#[derive(Clone, Copy)]
enum ScopeBodyContext {
    Function,
    Class,
}

struct ScopeBodyFactsCollector<'ast> {
    facts: ScopeBodyFacts,
    references: FxHashSet<&'ast str>,
    outside_inlined_comprehension_references: Option<FxHashSet<Cow<'ast, str>>>,
    skip_annotations: bool,
    collect_function_scope_facts: bool,
    eager_function_annotations: bool,
    deferred_local_annotations: bool,
    class_scope: bool,
    generator_depth: usize,
    inlined_comprehension_depth: usize,
    seen_inlined_comprehension_targets: FxHashSet<String>,
    class_comprehension_targets: Vec<String>,
    private_name: Option<String>,
}

#[derive(Default)]
struct LocalAnnotationBindings(FxHashSet<String>);

impl<'ast> Visitor<'ast> for LocalAnnotationBindings {
    fn visit_expr(&mut self, expression: &'ast Expr) {
        if crate::stack_growth_required() {
            return crate::grow_stack(|| self.visit_expr(expression));
        }

        if let Expr::Lambda(lambda) = expression {
            visit_lambda_defaults(self, lambda);
            return;
        }
        if let Expr::Named(named) = expression
            && let Expr::Name(name) = named.target.as_ref()
        {
            self.0.insert(name.id.as_str().to_string());
        }
        walk_expr(self, expression);
    }
}

impl<'ast> ScopeBodyFactsCollector<'ast> {
    fn collect(
        body: &'ast [Stmt],
        skip_annotations: bool,
        context: ScopeBodyContext,
        eager_function_annotations: bool,
        deferred_local_annotations: bool,
        private_name: Option<&str>,
    ) -> ScopeBodyFacts {
        let collect_function_scope_facts = matches!(context, ScopeBodyContext::Function);
        let class_scope = matches!(context, ScopeBodyContext::Class);
        let mut collector = Self {
            facts: ScopeBodyFacts::default(),
            references: FxHashSet::default(),
            outside_inlined_comprehension_references: None,
            skip_annotations,
            collect_function_scope_facts,
            eager_function_annotations,
            deferred_local_annotations,
            class_scope,
            generator_depth: 0,
            inlined_comprehension_depth: 0,
            seen_inlined_comprehension_targets: FxHashSet::default(),
            class_comprehension_targets: Vec::new(),
            private_name: private_name.map(str::to_owned),
        };
        for statement in body {
            collector.visit_stmt(statement);
        }
        collector.facts.references = collector
            .references
            .into_iter()
            .map(str::to_string)
            .collect();
        collector.facts.outside_inlined_comprehension_references = collector
            .outside_inlined_comprehension_references
            .unwrap_or_default()
            .into_iter()
            .map(Cow::into_owned)
            .collect();
        if collect_function_scope_facts {
            // A nonlocal declaration establishes an own-scope free symbol even if
            // every use occurs under an inlined comprehension target.
            collector
                .facts
                .outside_inlined_comprehension_references
                .extend(collector.facts.nonlocals.iter().cloned());
        }
        collector.facts
    }

    fn expression_requirements(
        &self,
        expression: &Expr,
        collect: impl Fn(&Expr) -> BTreeSet<String>,
    ) -> BTreeSet<String> {
        let Some(private_name) = self.private_name.as_deref() else {
            return collect(expression);
        };
        contextual_expression_requirements(
            expression,
            &|name| mangle_name(name, Some(private_name)).into_owned(),
            collect,
        )
    }

    fn collect_annotation_comprehensions(
        &mut self,
        expression: &Expr,
        type_params: Option<&ruff_python_ast::TypeParams>,
    ) {
        if !self.collect_function_scope_facts {
            let mut requirements = annotation_comprehension_requirements(expression);
            if self.private_name.is_some() {
                requirements.captures = self.expression_requirements(expression, |expression| {
                    annotation_comprehension_requirements(expression).captures
                });
            }
            let is_type_parameter = |name: &str| {
                type_params.is_some_and(|parameters| {
                    parameters
                        .iter()
                        .any(|parameter| parameter.name().as_str() == name)
                })
            };
            self.facts
                .annotation_comprehension_requirements
                .first_iterable_needs_class |=
                requirements.first_iterable_needs_class && !is_type_parameter("__class__");
            self.facts
                .annotation_comprehension_requirements
                .captures
                .extend(
                    requirements
                        .captures
                        .into_iter()
                        .filter(|name| !is_type_parameter(name)),
                );
        }
    }

    fn collect_type_parameter_comprehensions(&mut self, parameters: &ruff_python_ast::TypeParams) {
        for parameter in parameters {
            if let TypeParam::TypeVar(parameter) = parameter
                && let Some(bound) = &parameter.bound
            {
                self.collect_annotation_comprehensions(bound, Some(parameters));
            }
            if let Some(default) = parameter.default() {
                self.collect_annotation_comprehensions(default, Some(parameters));
            }
        }
    }

    fn collect_function_header(&mut self, definition: &'ast StmtFunctionDef) {
        if !self.skip_annotations && !self.eager_function_annotations {
            for annotation in function_annotation_expressions(definition) {
                let required =
                    self.expression_requirements(annotation, annotation_nested_required_names);
                self.facts
                    .nested_lambda_requirements
                    .extend(required.into_iter().filter(|name| {
                        !definition.type_params.as_deref().is_some_and(|parameters| {
                            parameters
                                .iter()
                                .any(|parameter| parameter.name().as_str() == name)
                        })
                    }));
            }
        }
        if !self.skip_annotations
            && (!self.eager_function_annotations || definition.type_params.is_some())
        {
            for annotation in function_annotation_expressions(definition) {
                self.collect_annotation_comprehensions(
                    annotation,
                    definition.type_params.as_deref(),
                );
            }
        }
        self.facts.has_function_definition = true;
        // Symbol analysis visits defaults before decorators, which can establish the
        // first inlined-comprehension binding of a name in the enclosing scope.
        for default in function_default_expressions(definition) {
            self.visit_expr(default);
        }
        for decorator in &definition.decorator_list {
            self.visit_expr(&decorator.expression);
        }
        if self.eager_function_annotations && definition.type_params.is_none() {
            for parameter in definition
                .parameters
                .posonlyargs
                .iter()
                .chain(&definition.parameters.args)
            {
                if let Some(annotation) = parameter.parameter.annotation.as_deref() {
                    self.visit_expr(annotation);
                }
            }
            for parameter in definition
                .parameters
                .vararg
                .iter()
                .chain(&definition.parameters.kwarg)
            {
                if let Some(annotation) = parameter.annotation.as_deref() {
                    self.visit_expr(annotation);
                }
            }
            for parameter in &definition.parameters.kwonlyargs {
                if let Some(annotation) = parameter.parameter.annotation.as_deref() {
                    self.visit_expr(annotation);
                }
            }
            if let Some(annotation) = definition.returns.as_deref() {
                self.visit_expr(annotation);
            }
        }
        if self.class_scope
            && !self.skip_annotations
            && (!self.eager_function_annotations || definition.type_params.is_some())
            && !definition.type_params.iter().any(|parameters| {
                parameters
                    .iter()
                    .any(|parameter| parameter.name().as_str() == "__class__")
            })
        {
            for annotation in function_annotation_expressions(definition) {
                self.collect_annotation_class_reference(annotation);
            }
        }
        let Some(type_params) = definition.type_params.as_deref() else {
            return;
        };
        self.facts.has_generic_definition = true;
        self.collect_type_parameter_class_closures(type_params);
        self.collect_type_parameter_comprehensions(type_params);
        let type_names: BTreeSet<_> = type_params
            .iter()
            .map(|parameter| parameter.name().as_str().to_string())
            .collect();
        self.facts.nested_annotation_scope_requirements.extend(
            type_parameter_required_names(type_params)
                .difference(&type_names)
                .cloned(),
        );
    }

    fn collect_local_annotation(&mut self, annotation: &Expr) {
        // Before PEP 649, local annotations are omitted from bytecode but still participate
        // in symbol analysis. Their closures survive, while their fast-local positions do not.
        let parameters = ruff_python_ast::Parameters::default();
        let analysis = self.private_name.as_deref().map_or_else(
            || analyze_expression_scope(&parameters, annotation),
            |private_name| {
                analyze_expression_scope_with_mangler(&parameters, annotation, &|name| {
                    mangle_name(name, Some(private_name)).into_owned()
                })
                .analysis
            },
        );
        let mut bindings = LocalAnnotationBindings::default();
        bindings.visit_expr(annotation);
        let nested_required =
            self.expression_requirements(annotation, nested_expression_required_names);
        self.facts.nested_lambda_requirements.extend(
            nested_required
                .into_iter()
                .filter(|name| analysis.required.contains(name) || bindings.0.contains(name)),
        );
        self.facts
            .local_annotation_references
            .extend(analysis.required);
        self.facts.local_annotation_bindings.extend(bindings.0);
        self.facts
            .local_annotation_cellvars
            .extend(analysis.cellvars);
    }

    fn collect_class_header(&mut self, definition: &'ast StmtClassDef) {
        for decorator in &definition.decorator_list {
            self.visit_expr(&decorator.expression);
        }
        let Some(type_params) = definition.type_params.as_deref() else {
            // Plain class arguments execute directly in the current scope. Generic class
            // arguments instead execute in the synthetic type-parameter scope handled below.
            if let Some(arguments) = definition.arguments.as_deref() {
                for argument in &arguments.args {
                    self.visit_expr(argument);
                }
                for keyword in &arguments.keywords {
                    self.visit_expr(&keyword.value);
                }
            }
            return;
        };
        // Restricted generic headers retain their existing analysis. Their private
        // binding context depends on which type parameters have been declared so far.
        let enclosing_private_name = self.private_name.take();
        self.facts.has_generic_definition = true;
        // Keep this restricted header's captures separate until their lexical origin
        // has been recorded; an earlier body use can have the same source spelling.
        let body_lambda_requirements = std::mem::take(&mut self.facts.nested_lambda_requirements);
        let body_comprehension_captures =
            std::mem::take(&mut self.facts.annotation_comprehension_requirements.captures);
        self.collect_type_parameter_class_closures(type_params);
        let type_names = type_params
            .iter()
            .map(|parameter| {
                mangle_name(parameter.name().as_str(), Some(definition.name.as_str())).into_owned()
            })
            .collect::<BTreeSet<_>>();
        let mut declared = FxHashSet::default();
        let mut required = BTreeSet::new();
        let mut nested = BTreeSet::new();
        let mut collect = |expression: &Expr, declared: &FxHashSet<&str>| {
            let mangle = |name: &str| {
                if declared.contains(name) {
                    mangle_name(name, Some(definition.name.as_str())).into_owned()
                } else {
                    name.to_owned()
                }
            };
            required.extend(
                expression_required_names_with_mangler(expression, &mangle)
                    .into_iter()
                    .map(|name| mangle(&name)),
            );
            nested.extend(
                annotation_nested_required_names_with_mangler(expression, &mangle)
                    .into_iter()
                    .map(|name| mangle(&name)),
            );
        };
        for parameter in type_params {
            declared.insert(parameter.name().as_str());
            if let TypeParam::TypeVar(parameter) = parameter
                && let Some(bound) = parameter.bound.as_deref()
            {
                collect(bound, &declared);
            }
            if let Some(default) = parameter.default() {
                collect(default, &declared);
            }
        }
        if let Some(arguments) = definition.arguments.as_deref() {
            for argument in &arguments.args {
                collect(argument, &declared);
            }
            for keyword in &arguments.keywords {
                collect(&keyword.value, &declared);
            }
        }
        self.facts
            .nested_lambda_requirements
            .extend(nested.difference(&type_names).cloned());
        if !type_names.contains("__class__") {
            if let Some(arguments) = definition.arguments.as_deref() {
                for argument in &arguments.args {
                    self.collect_annotation_class_reference(argument);
                }
                for keyword in &arguments.keywords {
                    self.collect_annotation_class_reference(&keyword.value);
                }
            }
        }
        let is_unmangled_private = |name: &str| {
            self.class_scope
                && name.starts_with("__")
                && !name.ends_with("__")
                && !name.contains('.')
        };
        for name in required.difference(&type_names) {
            if is_unmangled_private(name) {
                self.facts
                    .unmangled_class_header_requirements
                    .insert(name.clone());
            } else {
                self.facts
                    .nested_annotation_scope_requirements
                    .insert(name.clone());
            }
        }
        self.facts.nested_lambda_requirements.retain(|name| {
            if is_unmangled_private(name) {
                self.facts
                    .unmangled_class_header_captures
                    .insert(name.clone());
                false
            } else {
                true
            }
        });
        self.facts
            .annotation_comprehension_requirements
            .captures
            .retain(|name| {
                if is_unmangled_private(name) {
                    self.facts
                        .unmangled_class_header_captures
                        .insert(name.clone());
                    false
                } else {
                    true
                }
            });
        self.facts
            .nested_lambda_requirements
            .extend(body_lambda_requirements);
        self.facts
            .annotation_comprehension_requirements
            .captures
            .extend(body_comprehension_captures);
        self.private_name = enclosing_private_name;
    }

    /// Annotation scopes request the current class cell, independently of class-body captures.
    fn collect_annotation_class_reference(&mut self, expression: &Expr) {
        if !self.class_scope || !expression_required_names(expression).contains("__class__") {
            return;
        }
        if !analyze_expression_scope(&ruff_python_ast::Parameters::default(), expression)
            .required
            .contains("__class__")
        {
            return;
        }
        self.facts.annotation_class_reference = true;
        self.facts.nested_annotation_class_closure |=
            nested_expression_required_names(expression).contains("__class__");
    }

    fn collect_type_parameter_class_closures(&mut self, type_params: &ruff_python_ast::TypeParams) {
        if !self.class_scope
            || type_params
                .iter()
                .any(|parameter| parameter.name().as_str() == "__class__")
        {
            return;
        }
        for parameter in type_params {
            let bound = match parameter {
                TypeParam::TypeVar(parameter) => parameter.bound.as_deref(),
                TypeParam::TypeVarTuple(_) | TypeParam::ParamSpec(_) => None,
            };
            for expression in bound.into_iter().chain(parameter.default()) {
                self.collect_annotation_class_reference(expression);
            }
        }
    }

    fn collect_type_alias(&mut self, statement: &'ast ruff_python_ast::StmtTypeAlias) {
        self.facts.has_type_alias = true;
        if self.class_scope
            && !statement.type_params.iter().any(|parameters| {
                parameters
                    .iter()
                    .any(|parameter| parameter.name().as_str() == "__class__")
            })
        {
            self.collect_annotation_class_reference(&statement.value);
            if let Some(parameters) = statement.type_params.as_deref() {
                self.collect_type_parameter_class_closures(parameters);
            }
        }
        self.collect_annotation_comprehensions(&statement.value, statement.type_params.as_deref());
        if let Some(parameters) = statement.type_params.as_deref() {
            self.collect_type_parameter_comprehensions(parameters);
        }
        let mut required = expression_required_names(&statement.value);
        let mut nested =
            self.expression_requirements(&statement.value, annotation_nested_required_names);
        if let Some(type_params) = statement.type_params.as_deref() {
            let type_names: BTreeSet<_> = type_params
                .iter()
                .map(|parameter| parameter.name().as_str().to_string())
                .collect();
            required.extend(type_parameter_required_names(type_params));
            for parameter in type_params {
                if let TypeParam::TypeVar(parameter) = parameter
                    && let Some(bound) = parameter.bound.as_deref()
                {
                    nested.extend(
                        self.expression_requirements(bound, annotation_nested_required_names),
                    );
                }
                if let Some(default) = parameter.default() {
                    nested.extend(
                        self.expression_requirements(default, annotation_nested_required_names),
                    );
                }
            }
            self.facts
                .nested_annotation_scope_requirements
                .extend(required.difference(&type_names).cloned());
            nested.retain(|name| !type_names.contains(name));
        } else {
            self.facts
                .nested_annotation_scope_requirements
                .extend(required);
        }
        // A nested function skips class bindings even when the alias itself can see them.
        self.facts.nested_lambda_requirements.extend(nested);
    }

    fn insert_reference(&mut self, name: &'ast str) {
        if self.class_scope && self.inlined_comprehension_depth > 0 {
            let canonical = mangle_name(name, self.private_name.as_deref());
            // An inlined body cannot itself request an enclosing `__class__` cell. It
            // can still use one requested by an independent direct class-body reference.
            if name != "__class__"
                && !self
                    .class_comprehension_targets
                    .iter()
                    .any(|target| mangle_name(target, self.private_name.as_deref()) == canonical)
            {
                self.facts
                    .class_inlined_comprehension_references
                    .insert(name.to_string());
            }
            return;
        }
        self.references.insert(name);
        if self.inlined_comprehension_depth == 0
            && let Some(references) = &mut self.outside_inlined_comprehension_references
        {
            references.insert(Cow::Borrowed(name));
        }
        if name == "super" {
            self.references.insert("__class__");
        } else if name == "__class__" {
            self.facts.explicit_dunder_class_reference = true;
        }
    }
}

impl<'ast> Visitor<'ast> for ScopeBodyFactsCollector<'ast> {
    fn visit_stmt(&mut self, statement: &'ast Stmt) {
        match statement {
            Stmt::Assert(_) => self.facts.has_assertions = true,
            Stmt::FunctionDef(definition) => {
                // The child body is represented by a separate `ScopeArena` node and plan.
                self.collect_function_header(definition);
                return;
            }
            Stmt::ClassDef(definition) => {
                // As above, only the class header is evaluated in the current scope.
                self.collect_class_header(definition);
                return;
            }
            Stmt::TypeAlias(statement) => {
                // The alias value and type parameters own annotation scopes. Their
                // free requirements were collected after filtering bound parameters.
                self.collect_type_alias(statement);
                return;
            }
            Stmt::Assign(assignment) if self.collect_function_scope_facts => {
                for target in &assignment.targets {
                    self.visit_expr(target);
                }
                self.visit_expr(&assignment.value);
                return;
            }
            Stmt::AugAssign(assignment) if self.collect_function_scope_facts => {
                self.visit_expr(&assignment.target);
                self.visit_expr(&assignment.value);
                return;
            }
            Stmt::For(statement) if self.collect_function_scope_facts => {
                self.visit_expr(&statement.target);
                self.visit_expr(&statement.iter);
                self.visit_body(&statement.body);
                self.visit_body(&statement.orelse);
                return;
            }
            Stmt::AnnAssign(annotation) => {
                self.facts.has_annotations = true;
                if !self.skip_annotations && !self.eager_function_annotations {
                    self.collect_annotation_comprehensions(&annotation.annotation, None);
                }
                if self.class_scope && !self.skip_annotations && !self.eager_function_annotations {
                    self.visit_expr(&annotation.target);
                    if let Some(value) = &annotation.value {
                        self.visit_expr(value);
                    }
                    let body_reference = self.facts.explicit_dunder_class_reference;
                    self.visit_expr(&annotation.annotation);
                    self.collect_annotation_class_reference(&annotation.annotation);
                    self.facts.explicit_dunder_class_reference = body_reference;
                    return;
                }
                if self.skip_annotations {
                    self.visit_expr(&annotation.target);
                    if let Some(value) = &annotation.value {
                        self.visit_expr(value);
                    }
                    if self.collect_function_scope_facts {
                        if self.eager_function_annotations {
                            self.collect_local_annotation(&annotation.annotation);
                        } else if self.deferred_local_annotations {
                            // The annotation never executes, but its nested functions and
                            // comprehensions still capture names from the real function scope.
                            let required = self.expression_requirements(
                                &annotation.annotation,
                                annotation_nested_required_names,
                            );
                            self.facts.nested_lambda_requirements.extend(required);
                        }
                    }
                    return;
                }
            }
            Stmt::Global(statement) => self
                .facts
                .globals
                .extend(statement.names.iter().map(|name| name.as_str().to_string())),
            Stmt::Nonlocal(statement) => self
                .facts
                .nonlocals
                .extend(statement.names.iter().map(|name| name.as_str().to_string())),
            _ => {}
        }
        walk_stmt(self, statement);
    }

    fn visit_expr(&mut self, expression: &'ast Expr) {
        if crate::stack_growth_required() {
            return crate::grow_stack(|| self.visit_expr(expression));
        }

        match expression {
            Expr::Name(name) => {
                if name.ctx == ExprContext::Load {
                    self.insert_reference(name.id.as_str());
                }
                return;
            }
            Expr::Attribute(attribute) => {
                self.visit_expr(attribute_base(attribute));
                return;
            }
            Expr::StringLiteral(_)
            | Expr::BytesLiteral(_)
            | Expr::NumberLiteral(_)
            | Expr::BooleanLiteral(_)
            | Expr::NoneLiteral(_)
            | Expr::EllipsisLiteral(_)
            | Expr::IpyEscapeCommand(_) => return,
            _ => {}
        }
        if self.collect_function_scope_facts
            && let Expr::Dict(dictionary) = expression
        {
            for item in &dictionary.items {
                if let Some(key) = &item.key {
                    self.visit_expr(key);
                }
            }
            for item in &dictionary.items {
                self.visit_expr(&item.value);
            }
            return;
        }
        if let Expr::Lambda(lambda) = expression {
            visit_lambda_defaults(self, lambda);
            let required = self.private_name.as_deref().map_or_else(
                || analyze_lambda_scope(lambda).required,
                |private_name| {
                    analyze_lambda_scope_with_mangler(lambda, &|name| {
                        mangle_name(name, Some(private_name)).into_owned()
                    })
                    .analysis
                    .required
                },
            );
            if self.inlined_comprehension_depth == 0 {
                self.facts
                    .outside_inlined_comprehension_requirements
                    .extend(required.iter().cloned());
            }
            self.facts.nested_lambda_requirements.extend(
                required
                    .into_iter()
                    .filter(|name| !self.class_comprehension_targets.contains(name)),
            );
            return;
        }
        if self.class_scope
            && let Expr::Generator(generator) = expression
        {
            // A generator owns its iteration targets. Only its free references escape
            // into the class, and enclosing comprehension targets provide their own cells.
            let required = self.expression_requirements(expression, |expression| {
                let Expr::Generator(generator) = expression else {
                    unreachable!()
                };
                generator_parent_requirements(generator)
            });
            self.facts.nested_generator_requirements.extend(
                required
                    .into_iter()
                    .filter(|name| !self.class_comprehension_targets.contains(name)),
            );
            if let Some(first) = generator.generators.first() {
                self.visit_expr(&first.iter);
            }
            return;
        }
        if self.collect_function_scope_facts
            && self.generator_depth == 0
            && let Expr::Generator(generator) = expression
        {
            let required = self.expression_requirements(expression, |expression| {
                let Expr::Generator(generator) = expression else {
                    unreachable!()
                };
                generator_parent_requirements(generator)
            });
            if self.inlined_comprehension_depth == 0 {
                self.facts
                    .outside_inlined_comprehension_requirements
                    .extend(required.iter().cloned());
            }
            self.facts.nested_generator_requirements.extend(required);
            self.facts
                .generator_named_targets
                .extend(generator_named_targets(generator));
            if let Some(first) = generator.generators.first() {
                self.visit_expr(&first.iter);
            }
            return;
        }
        if self.generator_depth == 0 {
            if let Some((generators, key, value)) = comprehension_parts(expression) {
                let cells = comprehension_cell_names_in_private_context(
                    generators,
                    key,
                    value,
                    self.private_name.as_deref(),
                );
                self.facts.inlined_comprehension_cellvars.extend(cells);
                if self.collect_function_scope_facts {
                    if !self.facts.has_inlined_comprehension {
                        let mut references = self
                            .references
                            .iter()
                            .copied()
                            .map(Cow::Borrowed)
                            .collect::<FxHashSet<_>>();
                        if !self.facts.explicit_dunder_class_reference {
                            references.remove("__class__");
                        }
                        self.outside_inlined_comprehension_references = Some(references);
                    }
                    self.facts.has_inlined_comprehension = true;
                    // Only the first iterable is evaluated outside the inlined comprehension's
                    // temporary scope.
                    if let Some(first) = generators.first() {
                        self.visit_expr(&first.iter);
                    }
                    if self.inlined_comprehension_depth == 0 {
                        for (name, bound) in comprehension_bindings_in_private_context(
                            expression,
                            self.private_name.as_deref(),
                        ) {
                            let canonical = mangle_name(&name, self.private_name.as_deref());
                            if bound {
                                self.seen_inlined_comprehension_targets
                                    .insert(canonical.into_owned());
                            } else if self
                                .seen_inlined_comprehension_targets
                                .contains(canonical.as_ref())
                            {
                                self.facts.later_comprehension_references.insert(name);
                            } else {
                                self.outside_inlined_comprehension_references
                                    .as_mut()
                                    .expect("inlined comprehension references are initialized")
                                    .insert(Cow::Owned(name));
                            }
                        }
                    }
                    self.inlined_comprehension_depth += 1;
                    for (index, generator) in generators.iter().enumerate() {
                        self.visit_expr(&generator.target);
                        if index > 0 {
                            self.visit_expr(&generator.iter);
                        }
                        for condition in &generator.ifs {
                            self.visit_expr(condition);
                        }
                    }
                    self.visit_expr(value);
                    if let Some(key) = key {
                        self.visit_expr(key);
                    }
                    self.inlined_comprehension_depth -= 1;
                    return;
                }
                // A class comprehension provides its own captured targets. References from
                // nested lambdas to those targets do not become class free variables.
                if let Some(first) = generators.first() {
                    self.visit_expr(&first.iter);
                }
                let outer_targets = self.class_comprehension_targets.len();
                for generator in generators {
                    collect_target_names(&generator.target, &mut self.class_comprehension_targets);
                }
                self.inlined_comprehension_depth += 1;
                for (index, generator) in generators.iter().enumerate() {
                    if index > 0 {
                        self.visit_expr(&generator.iter);
                    }
                    self.visit_expr(&generator.target);
                    for condition in &generator.ifs {
                        self.visit_expr(condition);
                    }
                }
                if let Some(key) = key {
                    self.visit_expr(key);
                }
                self.visit_expr(value);
                self.inlined_comprehension_depth -= 1;
                self.class_comprehension_targets.truncate(outer_targets);
                return;
            }
        }

        let is_generator = matches!(expression, Expr::Generator(_));
        if is_generator {
            self.generator_depth += 1;
            walk_expr(self, expression);
            self.generator_depth -= 1;
        } else {
            walk_expr(self, expression);
        }
    }
}

#[derive(Default)]
pub(super) struct ReferenceCollector {
    pub(super) references: FxHashSet<String>,
    skip_generator_bodies: bool,
    skip_inlined_comprehension_bodies: bool,
}

impl<'ast> Visitor<'ast> for ReferenceCollector {
    fn visit_expr(&mut self, expression: &'ast Expr) {
        if crate::stack_growth_required() {
            return crate::grow_stack(|| self.visit_expr(expression));
        }

        match expression {
            Expr::Name(name) => {
                if name.ctx == ExprContext::Load {
                    let spelling = name.id.as_str();
                    if !self.references.contains(spelling) {
                        self.references.insert(spelling.to_string());
                    }
                    if spelling == "super" && !self.references.contains("__class__") {
                        self.references.insert("__class__".to_string());
                    }
                }
                return;
            }
            Expr::Attribute(attribute) => {
                self.visit_expr(attribute_base(attribute));
                return;
            }
            Expr::StringLiteral(_)
            | Expr::BytesLiteral(_)
            | Expr::NumberLiteral(_)
            | Expr::BooleanLiteral(_)
            | Expr::NoneLiteral(_)
            | Expr::EllipsisLiteral(_)
            | Expr::IpyEscapeCommand(_) => return,
            _ => {}
        }
        if let Expr::Lambda(lambda) = expression {
            visit_lambda_defaults(self, lambda);
            return;
        }
        let generators = match expression {
            Expr::Generator(generator) if self.skip_generator_bodies => {
                Some(generator.generators.as_slice())
            }
            Expr::ListComp(comprehension) if self.skip_inlined_comprehension_bodies => {
                Some(&comprehension.generators[..])
            }
            Expr::SetComp(comprehension) if self.skip_inlined_comprehension_bodies => {
                Some(&comprehension.generators[..])
            }
            Expr::DictComp(comprehension) if self.skip_inlined_comprehension_bodies => {
                Some(&comprehension.generators[..])
            }
            _ => None,
        };
        if let Some(generators) = generators {
            // Only the first iterable is evaluated in the enclosing scope.
            if let Some(first) = generators.first() {
                self.visit_expr(&first.iter);
            }
            return;
        }
        walk_expr(self, expression);
    }
}

/// Returns the names loaded by an expression only if it has no conditional evaluation.
pub(super) fn definitely_evaluated_references(expression: &Expr) -> Option<SmallVec<[&str; 4]>> {
    #[derive(Default)]
    struct Collector<'ast> {
        conditional: bool,
        references: SmallVec<[&'ast str; 4]>,
    }

    impl<'ast> Visitor<'ast> for Collector<'ast> {
        fn visit_expr(&mut self, expression: &'ast Expr) {
            if crate::stack_growth_required() {
                return crate::grow_stack(|| self.visit_expr(expression));
            }

            if self.conditional {
                return;
            }
            match expression {
                Expr::BoolOp(_)
                | Expr::If(_)
                | Expr::Lambda(_)
                | Expr::Generator(_)
                | Expr::ListComp(_)
                | Expr::SetComp(_)
                | Expr::DictComp(_) => self.conditional = true,
                Expr::Compare(comparison) if comparison.ops.len() > 1 => self.conditional = true,
                Expr::Name(name) => {
                    if name.ctx == ExprContext::Load {
                        let name = name.id.as_str();
                        self.references.push(name);
                        if name == "super" {
                            self.references.push("__class__");
                        }
                    }
                }
                _ => walk_expr(self, expression),
            }
        }
    }

    let mut collector = Collector::default();
    collector.visit_expr(expression);
    if collector.conditional {
        return None;
    }
    collector.references.sort_unstable();
    collector.references.dedup();
    Some(collector.references)
}

pub(super) struct LambdaScopeAnalysis {
    pub(super) locals: Vec<String>,
    pub(super) cellvars: FxHashSet<String>,
    pub(super) inlined_comprehension_cellvars: FxHashSet<String>,
    pub(super) required: BTreeSet<String>,
}

/// Reuse raw lexical requirements within one borrowed expression tree.
///
/// Keys identify nodes in that tree; a fresh cache is used for normalized clones
/// and for each independent analysis, so neither pointer reuse nor private-name
/// contexts can mix results.
#[derive(Default)]
struct ExpressionScopeCache<'ast> {
    lambda_requirements: FxHashMap<*const ruff_python_ast::ExprLambda, BTreeSet<String>>,
    generator_requirements: FxHashMap<*const ruff_python_ast::ExprGenerator, BTreeSet<String>>,
    generator_parent_requirements:
        FxHashMap<*const ruff_python_ast::ExprGenerator, BTreeSet<String>>,
    nodes: PhantomData<&'ast Expr>,
}

fn lambda_required_names_with_cache<'ast>(
    lambda: &'ast ruff_python_ast::ExprLambda,
    cache: &mut ExpressionScopeCache<'ast>,
) -> BTreeSet<String> {
    let key = std::ptr::from_ref(lambda);
    if let Some(required) = cache.lambda_requirements.get(&key) {
        return required.clone();
    }
    let empty_parameters = ruff_python_ast::Parameters::default();
    let parameters = lambda.parameters.as_deref().unwrap_or(&empty_parameters);
    let required = expression_scope_facts(parameters, &lambda.body, cache).required;
    cache.lambda_requirements.insert(key, required.clone());
    required
}

pub(super) fn analyze_lambda_scope(lambda: &ruff_python_ast::ExprLambda) -> LambdaScopeAnalysis {
    let empty_parameters = ruff_python_ast::Parameters::default();
    let parameters = lambda.parameters.as_deref().unwrap_or(&empty_parameters);
    analyze_expression_scope(parameters, &lambda.body)
}

pub(super) struct ContextualLambdaScopeAnalysis {
    pub(super) analysis: LambdaScopeAnalysis,
    pub(super) local_aliases: Vec<(String, String)>,
}

/// Analyze symbol identity on a private clone, then retain raw escaping names.
///
/// `mangle` describes symbol analysis at this lambda's lexical location. It must
/// include a generic class header's declaration-time restriction when present.
pub(super) fn analyze_lambda_scope_with_mangler(
    lambda: &ruff_python_ast::ExprLambda,
    mangle: &impl Fn(&str) -> String,
) -> ContextualLambdaScopeAnalysis {
    let empty_parameters = ruff_python_ast::Parameters::default();
    analyze_expression_scope_with_mangler(
        lambda.parameters.as_deref().unwrap_or(&empty_parameters),
        &lambda.body,
        mangle,
    )
}

fn analyze_expression_scope_with_mangler(
    parameters: &ruff_python_ast::Parameters,
    body: &Expr,
    mangle: &impl Fn(&str) -> String,
) -> ContextualLambdaScopeAnalysis {
    let raw = analyze_expression_scope(parameters, body);
    let mut spellings = VariableSpellings::default();
    spellings.visit_parameters(parameters);
    spellings.visit_expr(body);
    let aliases = colliding_private_spellings(&spellings.names, mangle);
    if aliases.is_empty() {
        return ContextualLambdaScopeAnalysis {
            analysis: raw,
            local_aliases: Vec::new(),
        };
    }
    let normalize = |name: &str| {
        aliases
            .get(name)
            .cloned()
            .unwrap_or_else(|| name.to_owned())
    };
    let mut depth = crate::stack::ExpressionDepth::default();
    depth.visit_parameters(parameters);
    depth.visit_expr(body);
    crate::stack::with_depth(depth.maximum(), || {
        let mut parameters = parameters.clone();
        let mut body = body.clone();
        let transformer = PrivateVariableNormalizer { mangle: &normalize };
        ruff_python_ast::visitor::transformer::Transformer::visit_parameters(
            &transformer,
            &mut parameters,
        );
        ruff_python_ast::visitor::transformer::Transformer::visit_expr(&transformer, &mut body);

        let mut analysis = analyze_expression_scope(&parameters, &body);
        // Preserve the spellings used by the surrounding scope and original AST.
        // The normalized result removes false escapes such as lambda __x: _C__x.
        // Preserve the existing free-variable spelling selection.
        analysis.required = raw
            .required
            .into_iter()
            .filter(|name| analysis.required.contains(&normalize(name)))
            .collect();

        let local_names: FxHashSet<_> = analysis.locals.iter().map(String::as_str).collect();
        let local_aliases = spellings
            .names
            .into_iter()
            .filter_map(|raw| {
                let canonical = normalize(&raw);
                (raw != canonical && local_names.contains(canonical.as_str()))
                    .then_some((raw, canonical))
            })
            .collect();

        ContextualLambdaScopeAnalysis {
            analysis,
            local_aliases,
        }
    })
}

/// Adapt existing pure requirement collectors without changing recursive APIs.
///
/// Use at parent fact-collection boundaries for generator or annotation trees
/// whose nested lambdas must honor the current private-name context.
fn contextual_expression_requirements(
    expression: &Expr,
    mangle: &impl Fn(&str) -> String,
    collect: impl Fn(&Expr) -> BTreeSet<String>,
) -> BTreeSet<String> {
    let raw = collect(expression);
    // Normalization only filters raw requirements; an empty set cannot gain names.
    if raw.is_empty() {
        return raw;
    }
    let mut spellings = VariableSpellings::default();
    spellings.visit_expr(expression);
    let aliases = colliding_private_spellings(&spellings.names, mangle);
    if aliases.is_empty() {
        return raw;
    }
    let normalize = |name: &str| {
        aliases
            .get(name)
            .cloned()
            .unwrap_or_else(|| name.to_owned())
    };
    let mut depth = crate::stack::ExpressionDepth::default();
    depth.visit_expr(expression);
    crate::stack::with_depth(depth.maximum(), || {
        let mut normalized = expression.clone();
        ruff_python_ast::visitor::transformer::Transformer::visit_expr(
            &PrivateVariableNormalizer { mangle: &normalize },
            &mut normalized,
        );
        let required = collect(&normalized);
        raw.into_iter()
            .filter(|name| required.contains(&normalize(name)))
            .collect()
    })
}

/// Collect expression requirements using the private-name identity in force at this point.
pub(super) fn expression_required_names_with_mangler(
    expression: &Expr,
    mangle: &impl Fn(&str) -> String,
) -> BTreeSet<String> {
    analyze_expression_scope_with_mangler(
        &ruff_python_ast::Parameters::default(),
        expression,
        mangle,
    )
    .analysis
    .required
}

/// Collect nested annotation requirements using the enclosing symbol identity.
pub(super) fn annotation_nested_required_names_with_mangler(
    expression: &Expr,
    mangle: &impl Fn(&str) -> String,
) -> BTreeSet<String> {
    contextual_expression_requirements(expression, mangle, annotation_nested_required_names)
}

/// Plan fast storage independently of a generic header's frozen symbol table.
///
/// CPython freezes parameter symbols during analysis, then uses the completed
/// private-name restriction when allocating comprehension save slots.
pub(super) fn header_expression_storage(
    parameters: &ruff_python_ast::Parameters,
    expression: &Expr,
    symbol_name: &impl Fn(&str) -> String,
    instruction_name: &impl Fn(&str) -> String,
    names: &NameInterner,
    prefix: &[NameId],
) -> HeaderLocalStoragePlan {
    let mut depth = crate::stack::ExpressionDepth::default();
    depth.visit_parameters(parameters);
    depth.visit_expr(expression);
    crate::stack::with_depth(depth.maximum(), || {
        let mut seen = FxHashSet::default();
        let slots = inlined_comprehension_local_names_in_expression(expression)
            .into_iter()
            .map(|name| (symbol_name(&name), instruction_name(&name)))
            .filter(|(symbol, _)| seen.insert(symbol.clone()))
            .collect::<Vec<_>>();
        let mut symbol_expression = expression.clone();
        ruff_python_ast::visitor::transformer::Transformer::visit_expr(
            &PrivateVariableNormalizer {
                mangle: symbol_name,
            },
            &mut symbol_expression,
        );
        let mut symbol_parameters = parameters.clone();
        ruff_python_ast::visitor::transformer::Transformer::visit_parameters(
            &PrivateVariableNormalizer {
                mangle: symbol_name,
            },
            &mut symbol_parameters,
        );
        let facts = expression_scope_facts(
            &symbol_parameters,
            &symbol_expression,
            &mut ExpressionScopeCache::default(),
        );
        let ordinary_locals = facts
            .locals
            .non_comprehension_bindings
            .into_iter()
            .map(String::from)
            .collect();
        let mut storage_names = parameters_in_locals_order(parameters)
            .map(|parameter| symbol_name(parameter.name.as_str()))
            .collect::<Vec<_>>();
        collect_header_slot_names(
            &symbol_expression,
            &ordinary_locals,
            &facts.cellvars,
            instruction_name,
            &mut storage_names,
        );
        let id = |name: &str| {
            names
                .get(name)
                .expect("generic-header storage name is interned")
        };
        let mut fast_locals = prefix.to_vec();
        let mut seen_storage = FxHashSet::default();
        fast_locals.extend(
            storage_names
                .iter()
                .filter(|name| seen_storage.insert(name.as_str()))
                .map(|name| id(name)),
        );
        let cellvars = inlined_comprehension_cell_names_in_expression(&symbol_expression)
            .iter()
            .map(|name| id(&instruction_name(name)))
            .collect();
        HeaderLocalStoragePlan {
            fast_locals,
            comprehension_slots: slots
                .iter()
                .map(|(symbol, storage)| (id(symbol), id(storage)))
                .collect(),
            cellvars,
        }
    })
}

/// Collect generic-header storage in code generation order without merging symbols.
fn collect_header_slot_names(
    expression: &Expr,
    ordinary_locals: &FxHashSet<String>,
    cellvars: &FxHashSet<String>,
    instruction_name: &impl Fn(&str) -> String,
    names: &mut Vec<String>,
) {
    struct Collector<'a, M> {
        ordinary_locals: &'a FxHashSet<String>,
        cellvars: &'a FxHashSet<String>,
        instruction_name: &'a M,
        names: &'a mut Vec<String>,
    }

    impl<'ast, M: Fn(&str) -> String> Visitor<'ast> for Collector<'_, M> {
        fn visit_expr(&mut self, expression: &'ast Expr) {
            if crate::stack_growth_required() {
                return crate::grow_stack(|| self.visit_expr(expression));
            }

            let Some((generators, key, value)) = comprehension_parts(expression) else {
                match expression {
                    Expr::Generator(generator) => {
                        if let Some(first) = generator.generators.first() {
                            self.visit_expr(&first.iter);
                        }
                        return;
                    }
                    Expr::Lambda(lambda) => {
                        visit_lambda_defaults(self, lambda);
                        return;
                    }
                    Expr::Name(name) => {
                        let emitted = (self.instruction_name)(name.id.as_str());
                        if self.ordinary_locals.contains(&emitted)
                            && !self.cellvars.contains(&emitted)
                        {
                            self.names.push(emitted);
                        }
                        return;
                    }
                    _ => {
                        walk_expr(self, expression);
                        return;
                    }
                }
            };
            if let Some(first) = generators.first() {
                self.visit_expr(&first.iter);
            }
            let temporary_names = comprehension_temporary_names(generators, key, value);
            let mut direct_targets = Vec::new();
            for generator in generators {
                collect_target_names(&generator.target, &mut direct_targets);
            }
            let deferred_outer_names = comprehension_name_bindings(generators, key, value)
                .into_iter()
                .filter(|(name, bound)| !bound && !direct_targets.contains(name))
                .map(|(name, _)| name)
                .collect::<FxHashSet<_>>();
            // Decide which scope owns each save before mapping symbols to
            // storage names: two pending spellings can share storage while
            // remaining distinct in the declaration-time symbol tables.
            self.names.extend(
                temporary_names
                    .into_iter()
                    .filter(|name| !deferred_outer_names.contains(name))
                    .map(|name| (self.instruction_name)(&name)),
            );
            for (index, generator) in generators.iter().enumerate() {
                if index > 0 {
                    self.visit_expr(&generator.iter);
                }
                self.visit_expr(&generator.target);
                for condition in &generator.ifs {
                    self.visit_expr(condition);
                }
            }
            if let Some(key) = key {
                self.visit_expr(key);
            }
            self.visit_expr(value);
        }
    }

    Collector {
        ordinary_locals,
        cellvars,
        instruction_name,
        names,
    }
    .visit_expr(expression);
}

/// Plan a header generator's fast slots from the operations that actually allocate them.
///
/// Ordinary accesses are eligible only under their declaration-time symbols.
/// Inlined saves use completed instruction names and can allocate separate slots
/// even when the corresponding declaration symbol is a cell or a pending name.
pub(super) fn header_generator_storage(
    generator: &ruff_python_ast::ExprGenerator,
    generator_locals: &FxHashSet<String>,
    generator_cellvars: &FxHashSet<String>,
    symbol_name: &impl Fn(&str) -> String,
    instruction_name: &impl Fn(&str) -> String,
    names: &NameInterner,
) -> HeaderLocalStoragePlan {
    let id = |name: &str| {
        names
            .get(name)
            .expect("generic-header storage name is interned")
    };
    let mut fast_locals = vec![".0".to_string()];
    let mut comprehension_slots = Vec::new();
    let mut seen_symbols = FxHashSet::default();
    let mut cellvars = FxHashSet::default();
    let mut collect = |expression: &Expr| {
        let mut depth = crate::stack::ExpressionDepth::default();
        depth.visit_expr(expression);
        crate::stack::with_depth(depth.maximum(), || {
            for name in inlined_comprehension_local_names_in_expression(expression) {
                let symbol = symbol_name(&name);
                if seen_symbols.insert(symbol.clone()) {
                    comprehension_slots.push((id(&symbol), id(&instruction_name(&name))));
                }
            }

            let mut symbol_expression = expression.clone();
            ruff_python_ast::visitor::transformer::Transformer::visit_expr(
                &PrivateVariableNormalizer {
                    mangle: symbol_name,
                },
                &mut symbol_expression,
            );
            collect_header_slot_names(
                &symbol_expression,
                generator_locals,
                generator_cellvars,
                instruction_name,
                &mut fast_locals,
            );
            cellvars.extend(
                inlined_comprehension_cell_names_in_expression(&symbol_expression)
                    .iter()
                    .map(|name| id(&instruction_name(name))),
            );
        });
    };
    for (index, comprehension) in generator.generators.iter().enumerate() {
        // The outermost iterable runs in the enclosing scope before this
        // generator starts, so its temporary slots belong to that scope.
        if index > 0 {
            collect(&comprehension.iter);
        }
        collect(&comprehension.target);
        for condition in &comprehension.ifs {
            collect(condition);
        }
    }
    collect(&generator.elt);
    let mut seen_storage = FxHashSet::default();
    fast_locals.retain(|name| seen_storage.insert(name.clone()));
    HeaderLocalStoragePlan {
        fast_locals: fast_locals.iter().map(|name| id(name)).collect(),
        comprehension_slots,
        cellvars,
    }
}

/// Only normalize identities with multiple observed source spellings.
fn colliding_private_spellings(
    spellings: &BTreeSet<String>,
    mangle: &impl Fn(&str) -> String,
) -> FxHashMap<String, String> {
    if spellings.len() < 2 {
        return FxHashMap::default();
    }
    let mut counts: FxHashMap<String, usize> = FxHashMap::default();
    for spelling in spellings {
        *counts.entry(mangle(spelling)).or_default() += 1;
    }
    spellings
        .iter()
        .filter_map(|spelling| {
            let canonical = mangle(spelling);
            (counts[&canonical] > 1 && spelling != &canonical)
                .then(|| (spelling.clone(), canonical))
        })
        .collect()
}

struct PrivateVariableNormalizer<'a, M> {
    mangle: &'a M,
}

impl<M: Fn(&str) -> String> ruff_python_ast::visitor::transformer::Transformer
    for PrivateVariableNormalizer<'_, M>
{
    fn visit_expr(&self, expression: &mut Expr) {
        if crate::stack_growth_required() {
            return crate::grow_stack(|| self.visit_expr(expression));
        }

        if let Expr::Name(name) = expression {
            name.id = Name::new((self.mangle)(name.id.as_str()));
        }
        // Attribute labels and call keyword labels are deliberately unchanged.
        // Recursing visits nested lambda parameters, walrus targets, generator
        // targets, comprehension targets, and their variable references.
        ruff_python_ast::visitor::transformer::walk_expr(self, expression);
    }

    fn visit_parameter(&self, parameter: &mut ruff_python_ast::Parameter) {
        parameter.name.id = Name::new((self.mangle)(parameter.name.as_str()));
        ruff_python_ast::visitor::transformer::walk_parameter(self, parameter);
    }
}

#[derive(Default)]
struct VariableSpellings {
    names: BTreeSet<String>,
}

pub(super) fn generator_has_private_spelling_collisions(
    generator: &ruff_python_ast::ExprGenerator,
    mangle: &impl Fn(&str) -> String,
) -> bool {
    let mut spellings = VariableSpellings::default();
    spellings.visit_expr(&generator.elt);
    for comprehension in &generator.generators {
        spellings.visit_expr(&comprehension.target);
        spellings.visit_expr(&comprehension.iter);
        for condition in &comprehension.ifs {
            spellings.visit_expr(condition);
        }
    }
    !colliding_private_spellings(&spellings.names, mangle).is_empty()
}

impl<'ast> Visitor<'ast> for VariableSpellings {
    fn visit_expr(&mut self, expression: &'ast Expr) {
        if crate::stack_growth_required() {
            return crate::grow_stack(|| self.visit_expr(expression));
        }

        if let Expr::Name(name) = expression {
            self.names.insert(name.id.to_string());
        }
        ruff_python_ast::visitor::walk_expr(self, expression);
    }

    fn visit_parameter(&mut self, parameter: &'ast ruff_python_ast::Parameter) {
        self.names.insert(parameter.name.to_string());
        ruff_python_ast::visitor::walk_parameter(self, parameter);
    }
}

fn analyze_expression_scope(
    parameters: &ruff_python_ast::Parameters,
    body: &Expr,
) -> LambdaScopeAnalysis {
    analyze_expression_scope_with_cache(parameters, body, &mut ExpressionScopeCache::default())
}

fn analyze_expression_scope_with_cache<'ast>(
    parameters: &ruff_python_ast::Parameters,
    body: &'ast Expr,
    cache: &mut ExpressionScopeCache<'ast>,
) -> LambdaScopeAnalysis {
    let ExpressionScopeFacts {
        mut locals,
        parameter_names,
        cellvars,
        required,
    } = expression_scope_facts(parameters, body, cache);
    let mut inlined_comprehension_cellvars = inlined_comprehension_cell_names_in_expression(body);
    let comprehension_fast_cellvars = locals
        .comprehension_iteration_targets
        .iter()
        .filter(|name| cellvars.contains(name.as_str()))
        .cloned()
        .collect::<Vec<_>>();
    let comprehension_target_predecessors = locals.comprehension_target_predecessors.clone();
    let comprehension_reordered_fast_cellvars = locals
        .comprehension_iteration_targets
        .iter()
        .filter(|name| !parameter_names.contains(*name))
        .filter(|name| locals.comprehension_late_bindings.contains(*name))
        .filter(|name| cellvars.contains(name.as_str()))
        .cloned()
        .collect::<Vec<_>>();
    reorder_comprehension_fast_cells(
        &mut locals.names,
        &comprehension_reordered_fast_cellvars,
        &comprehension_target_predecessors,
    );
    inlined_comprehension_cellvars.extend(
        comprehension_fast_cellvars
            .iter()
            .map(|name| name.as_str().to_string()),
    );
    LambdaScopeAnalysis {
        locals: locals.names.into_iter().map(String::from).collect(),
        cellvars,
        inlined_comprehension_cellvars,
        required,
    }
}

struct ExpressionScopeFacts {
    locals: LocalCollector,
    parameter_names: FxHashSet<Name>,
    cellvars: FxHashSet<String>,
    required: BTreeSet<String>,
}

/// Collect requirements without planning inlined-comprehension cell slots.
fn expression_scope_facts<'ast>(
    parameters: &ruff_python_ast::Parameters,
    body: &'ast Expr,
    cache: &mut ExpressionScopeCache<'ast>,
) -> ExpressionScopeFacts {
    let mut locals = LocalCollector::default();
    for parameter in parameters_in_locals_order(parameters) {
        locals.insert(parameter.name.as_str());
    }
    let parameter_names = locals.names.iter().cloned().collect::<FxHashSet<_>>();
    locals.collect_expression(body);

    let mut references = ReferenceCollector {
        skip_generator_bodies: true,
        ..ReferenceCollector::default()
    };
    references.visit_expr(body);
    let nested_requirements = nested_expression_required_names_with_cache(body, cache);
    let local_names = locals.names.iter().cloned().collect::<FxHashSet<_>>();
    let mut outside_references = ReferenceCollector {
        skip_generator_bodies: true,
        skip_inlined_comprehension_bodies: true,
        ..ReferenceCollector::default()
    };
    // A comprehension's first iterable can read an outer binding with its target's spelling.
    // Lambda defaults are evaluated here too; nested lambda bodies retain their own captures.
    if !locals.comprehension_targets.is_empty() {
        outside_references.visit_expr(body);
        // An outer comprehension may read a name that only a nested
        // comprehension binds. The nested save does not make that read local.
        outside_references
            .references
            .extend(annotation_comprehension_requirements(body).captures);
    }
    let cellvars: FxHashSet<_> = nested_requirements
        .iter()
        .filter(|name| local_names.contains(name.as_str()))
        .cloned()
        .collect();
    let required = references
        .references
        .iter()
        .chain(&nested_requirements)
        .filter(|name| {
            !local_names.contains(name.as_str())
                || (outside_references.references.contains(name.as_str())
                    && !locals.non_comprehension_bindings.contains(name.as_str()))
        })
        .cloned()
        .collect();
    ExpressionScopeFacts {
        locals,
        parameter_names,
        cellvars,
        required,
    }
}

pub(super) fn expression_required_names(expression: &Expr) -> BTreeSet<String> {
    let mut references = ReferenceCollector::default();
    references.visit_expr(expression);
    let mut required = references.references.into_iter().collect::<BTreeSet<_>>();
    required.extend(nested_expression_required_names(expression));
    required
}

#[derive(Debug, Default)]
pub(super) struct AnnotationComprehensionRequirements {
    pub(super) captures: BTreeSet<String>,
    first_iterable_needs_class: bool,
}

/// Separate child captures from the first iterable, which uses annotation lookup rules.
pub(super) fn annotation_comprehension_requirements(
    expression: &Expr,
) -> AnnotationComprehensionRequirements {
    #[derive(Default)]
    struct Collector(AnnotationComprehensionRequirements);

    impl<'ast> Visitor<'ast> for Collector {
        fn visit_expr(&mut self, expression: &'ast Expr) {
            if crate::stack_growth_required() {
                return crate::grow_stack(|| self.visit_expr(expression));
            }

            let Some((generators, key, value)) = comprehension_parts(expression) else {
                match expression {
                    Expr::Lambda(lambda) => {
                        visit_lambda_defaults(self, lambda);
                        return;
                    }
                    Expr::Generator(generator) => {
                        if let Some(first) = generator.generators.first() {
                            self.visit_expr(&first.iter);
                        }
                        return;
                    }
                    _ => {
                        walk_expr(self, expression);
                        return;
                    }
                }
            };
            self.0.captures.extend(
                comprehension_name_bindings(generators, key, value)
                    .into_iter()
                    .filter_map(|(name, bound)| (!bound).then_some(name)),
            );
            if let Some(first) = generators.first() {
                self.visit_expr(&first.iter);
                self.0.first_iterable_needs_class |=
                    expression_required_names(&first.iter).contains("__class__");
            }
        }
    }

    let mut collector = Collector::default();
    collector.visit_expr(expression);
    collector.0
}

pub(super) fn expression_requirements_outside_comprehensions(
    expression: &Expr,
) -> BTreeSet<String> {
    #[derive(Default)]
    struct Collector {
        required: BTreeSet<String>,
    }

    impl<'ast> Visitor<'ast> for Collector {
        fn visit_expr(&mut self, expression: &'ast Expr) {
            if crate::stack_growth_required() {
                return crate::grow_stack(|| self.visit_expr(expression));
            }

            let generators = match expression {
                Expr::ListComp(comprehension) => Some(&comprehension.generators[..]),
                Expr::SetComp(comprehension) => Some(&comprehension.generators[..]),
                Expr::DictComp(comprehension) => Some(&comprehension.generators[..]),
                Expr::Lambda(lambda) => {
                    visit_lambda_defaults(self, lambda);
                    self.required.extend(analyze_lambda_scope(lambda).required);
                    return;
                }
                Expr::Generator(generator) => {
                    self.required.extend(generator_required_names(generator));
                    Some(generator.generators.as_slice())
                }
                Expr::Name(name) if name.ctx == ExprContext::Load => {
                    self.required.insert(name.id.to_string());
                    return;
                }
                _ => None,
            };
            if let Some(generators) = generators {
                if let Some(first) = generators.first() {
                    self.visit_expr(&first.iter);
                }
                return;
            }
            walk_expr(self, expression);
        }
    }

    let mut collector = Collector::default();
    collector.visit_expr(expression);
    collector.required
}

pub(super) fn inlined_comprehension_local_names_in_expression(expression: &Expr) -> Vec<String> {
    let mut collector = LocalCollector {
        ignore_generator_body_comprehension_targets: true,
        ..LocalCollector::default()
    };
    collector.collect_expression(expression);
    collector
        .names
        .into_iter()
        .filter(|name| {
            collector
                .seen_comprehension_iteration_targets
                .contains(name)
        })
        .map(String::from)
        .collect()
}

/// Enclosing bindings passed through an annotation to its nested functions and comprehensions.
pub(super) fn annotation_nested_required_names(expression: &Expr) -> BTreeSet<String> {
    let mut nested = nested_expression_required_names(expression);
    if !nested.is_empty() {
        let required =
            analyze_expression_scope(&ruff_python_ast::Parameters::default(), expression).required;
        nested.retain(|name| required.contains(name));
    }
    nested.extend(annotation_comprehension_requirements(expression).captures);
    nested
}

pub(super) fn nested_expression_required_names(expression: &Expr) -> BTreeSet<String> {
    nested_expression_required_names_with_cache(expression, &mut ExpressionScopeCache::default())
}

fn nested_expression_required_names_with_cache<'ast>(
    expression: &'ast Expr,
    cache: &mut ExpressionScopeCache<'ast>,
) -> BTreeSet<String> {
    struct Collector<'cache, 'ast> {
        required: BTreeSet<String>,
        cache: &'cache mut ExpressionScopeCache<'ast>,
    }

    impl<'ast> Visitor<'ast> for Collector<'_, 'ast> {
        fn visit_expr(&mut self, expression: &'ast Expr) {
            if crate::stack_growth_required() {
                return crate::grow_stack(|| self.visit_expr(expression));
            }

            if let Expr::Generator(generator) = expression {
                // The first iterable executes in the enclosing scope and can create its
                // own closures, independently of the generator body's requirements.
                if let Some(first) = generator.generators.first() {
                    self.visit_expr(&first.iter);
                }
                self.required
                    .extend(generator_parent_requirements_with_cache(
                        generator, self.cache,
                    ));
                return;
            }
            if let Expr::Lambda(lambda) = expression {
                visit_lambda_defaults(self, lambda);
                self.required
                    .extend(lambda_required_names_with_cache(lambda, self.cache));
                return;
            }
            walk_expr(self, expression);
        }
    }

    let mut collector = Collector {
        required: BTreeSet::new(),
        cache,
    };
    collector.visit_expr(expression);
    collector.required
}

pub(super) fn type_parameter_required_names(
    type_params: &ruff_python_ast::TypeParams,
) -> BTreeSet<String> {
    let mut required = BTreeSet::new();
    for parameter in type_params {
        if let TypeParam::TypeVar(parameter) = parameter
            && let Some(bound) = &parameter.bound
        {
            required.extend(expression_required_names(bound));
        }
        if let Some(default) = parameter.default() {
            required.extend(expression_required_names(default));
        }
    }
    required
}

pub(super) fn collect_target_names(target: &Expr, names: &mut Vec<String>) {
    match target {
        Expr::Name(name) => names.push(name.id.as_str().to_string()),
        Expr::List(list) => {
            for element in &list.elts {
                collect_target_names(element, names);
            }
        }
        Expr::Tuple(tuple) => {
            for element in &tuple.elts {
                collect_target_names(element, names);
            }
        }
        Expr::Starred(starred) => collect_target_names(&starred.value, names),
        _ => {}
    }
}

#[derive(Default)]
pub(super) struct ComprehensionScopeFacts {
    pub(super) names: BTreeSet<String>,
    pub(super) walrus_targets: BTreeSet<String>,
}

impl ComprehensionScopeFacts {
    fn visit_nested_comprehension(&mut self, generators: &[ruff_python_ast::Comprehension]) {
        // The first iterable is evaluated in the containing scope; the remaining
        // expressions enter the nested comprehension's own inlined scope.
        if let Some(generator) = generators.first() {
            self.visit_expr(&generator.iter);
        }
    }
}

impl<'ast> Visitor<'ast> for ComprehensionScopeFacts {
    fn visit_expr(&mut self, expression: &'ast Expr) {
        if crate::stack_growth_required() {
            return crate::grow_stack(|| self.visit_expr(expression));
        }

        match expression {
            Expr::Name(name) => {
                self.names.insert(name.id.as_str().to_string());
            }
            Expr::Named(named) => {
                if let Expr::Name(name) = named.target.as_ref() {
                    self.walrus_targets.insert(name.id.as_str().to_string());
                }
            }
            Expr::Generator(generator) => {
                self.visit_nested_comprehension(&generator.generators);
                return;
            }
            Expr::ListComp(comprehension) => {
                self.visit_nested_comprehension(&comprehension.generators);
                return;
            }
            Expr::SetComp(comprehension) => {
                self.visit_nested_comprehension(&comprehension.generators);
                return;
            }
            Expr::DictComp(comprehension) => {
                self.visit_nested_comprehension(&comprehension.generators);
                return;
            }
            Expr::Lambda(lambda) => {
                if let Some(parameters) = lambda.parameters.as_deref() {
                    for default in parameter_default_expressions(parameters) {
                        self.visit_expr(default);
                    }
                }
                return;
            }
            _ => {}
        }
        walk_expr(self, expression);
    }
}

pub(super) fn comprehension_scope_facts(
    generators: &[ruff_python_ast::Comprehension],
    key: Option<&Expr>,
    value: &Expr,
) -> ComprehensionScopeFacts {
    let mut facts = ComprehensionScopeFacts::default();
    for generator in generators {
        facts.visit_expr(&generator.target);
        for condition in &generator.ifs {
            facts.visit_expr(condition);
        }
    }
    for generator in generators.iter().skip(1) {
        facts.visit_expr(&generator.iter);
    }
    if let Some(key) = key {
        facts.visit_expr(key);
    }
    facts.visit_expr(value);
    facts
}

/// Return saved comprehension locals in CPython's symbol insertion order.
/// Nested inlined scopes merge after the containing scope's own symbols.
pub(super) fn comprehension_temporary_names(
    generators: &[ruff_python_ast::Comprehension],
    key: Option<&Expr>,
    value: &Expr,
) -> Vec<String> {
    comprehension_symbol_names(generators, key, value, false, None, None)
        .into_iter()
        .map(|(name, _)| name)
        .collect()
}

/// Return save order when eligible global walrus slots need to be merged.
pub(super) fn global_comprehension_temporary_names(
    generators: &[ruff_python_ast::Comprehension],
    key: Option<&Expr>,
    value: &Expr,
    is_global: impl Fn(&str) -> bool,
    private_name: Option<&str>,
) -> Option<Vec<String>> {
    let walrus_targets =
        global_comprehension_walrus_names(generators, key, value, is_global, private_name);
    if walrus_targets.is_empty() {
        return None;
    }
    Some(
        comprehension_symbol_names(
            generators,
            key,
            value,
            false,
            Some(&walrus_targets),
            private_name,
        )
        .into_iter()
        .map(|(name, _)| name)
        .collect(),
    )
}

/// Identify global assignment-expression names whose symbols are saved by this comprehension.
pub(super) fn global_comprehension_walrus_names(
    generators: &[ruff_python_ast::Comprehension],
    key: Option<&Expr>,
    value: &Expr,
    is_global: impl Fn(&str) -> bool,
    private_name: Option<&str>,
) -> FxHashSet<String> {
    let mut walrus_targets = Vec::new();
    if let Some(key) = key {
        collect_named_expression_target_names(key, &mut walrus_targets);
    }
    collect_named_expression_target_names(value, &mut walrus_targets);
    for generator in generators {
        for condition in &generator.ifs {
            collect_named_expression_target_names(condition, &mut walrus_targets);
        }
    }
    if walrus_targets.is_empty() {
        return FxHashSet::default();
    }
    let facts = comprehension_scope_facts(generators, key, value);
    // A child copies its flags only for an absent outer symbol. Preserve an
    // existing outer read unless this comprehension itself also binds the name.
    walrus_targets
        .into_iter()
        .filter(|name| is_global(name))
        .filter(|name| {
            if private_name.is_none() {
                return !facts.names.contains(name) || facts.walrus_targets.contains(name);
            }
            let canonical = mangle_name(name, private_name);
            !facts
                .names
                .iter()
                .any(|other| mangle_name(other, private_name) == canonical)
                || facts
                    .walrus_targets
                    .iter()
                    .any(|other| mangle_name(other, private_name) == canonical)
        })
        .map(|name| match private_name {
            Some(private_name) => mangle_name(&name, Some(private_name)).into_owned(),
            None => name,
        })
        .collect()
}

/// Return legacy class save candidates; `true` entries require an enclosing free binding.
pub(super) fn legacy_class_comprehension_names(
    generators: &[ruff_python_ast::Comprehension],
    key: Option<&Expr>,
    value: &Expr,
) -> Vec<(String, bool)> {
    let mut names = vec![(".0".to_string(), false)];
    names.extend(comprehension_symbol_names(
        generators, key, value, true, None, None,
    ));
    names
}

/// Match names that may propagate through a legacy class comprehension as free variables.
pub(super) fn legacy_class_comprehension_keeps_free_name(
    name: &str,
    version: PythonVersion,
) -> bool {
    name != "__class__"
        && !(version == PythonVersion::Py313
            && matches!(name, "__classdict__" | "__conditional_annotations__"))
}

fn comprehension_symbol_names(
    generators: &[ruff_python_ast::Comprehension],
    key: Option<&Expr>,
    value: &Expr,
    all_symbols: bool,
    module_walrus_targets: Option<&FxHashSet<String>>,
    private_name: Option<&str>,
) -> Vec<(String, bool)> {
    #[derive(Default)]
    struct Collector<'a> {
        names: Vec<(String, bool)>,
        nested_names: Vec<(String, bool)>,
        closure_references: BTreeSet<String>,
        targets: FxHashSet<String>,
        all_symbols: bool,
        module_walrus_targets: Option<&'a FxHashSet<String>>,
        private_name: Option<&'a str>,
    }

    impl<'a> Collector<'a> {
        fn comprehension(
            generators: &[ruff_python_ast::Comprehension],
            key: Option<&Expr>,
            value: &Expr,
            all_symbols: bool,
            module_walrus_targets: Option<&'a FxHashSet<String>>,
            private_name: Option<&'a str>,
        ) -> Self {
            let mut collector = Self {
                all_symbols,
                module_walrus_targets,
                private_name,
                ..Self::default()
            };
            for (index, generator) in generators.iter().enumerate() {
                let mut targets = Vec::new();
                collect_target_names(&generator.target, &mut targets);
                collector
                    .targets
                    .extend(targets.into_iter().map(|name| match private_name {
                        Some(private_name) => mangle_name(&name, Some(private_name)).into_owned(),
                        None => name,
                    }));
                collector.visit_expr(&generator.target);
                if index > 0 {
                    collector.visit_expr(&generator.iter);
                }
                for condition in &generator.ifs {
                    collector.visit_expr(condition);
                }
            }
            // The symbol-table traversal visits a dict comprehension's value before its key.
            collector.visit_expr(value);
            if let Some(key) = key {
                collector.visit_expr(key);
            }
            collector.names.append(&mut collector.nested_names);
            if all_symbols {
                // Native update_symbols adds propagated child free names after direct and
                // inlined symbols. More than one new name follows CPython's hash-set order.
                // Keep a stable candidate order; eligibility is resolved by the class parent.
                collector.names.extend(
                    collector
                        .closure_references
                        .iter()
                        .cloned()
                        .map(|name| (name, true)),
                );
            }
            collector
        }
    }

    impl<'ast> Visitor<'ast> for Collector<'_> {
        fn visit_expr(&mut self, expression: &'ast Expr) {
            if crate::stack_growth_required() {
                return crate::grow_stack(|| self.visit_expr(expression));
            }

            let Some((generators, key, value)) = comprehension_parts(expression) else {
                match expression {
                    Expr::Generator(generator) => {
                        if let Some(first) = generator.generators.first() {
                            self.visit_expr(&first.iter);
                        }
                        if self.all_symbols {
                            self.closure_references
                                .extend(generator_required_names(generator));
                        }
                        return;
                    }
                    Expr::Lambda(lambda) => {
                        visit_lambda_defaults(self, lambda);
                        if self.all_symbols {
                            self.closure_references
                                .extend(analyze_lambda_scope(lambda).required);
                        }
                        return;
                    }
                    Expr::Named(named) if self.module_walrus_targets.is_some() => {
                        if let Expr::Name(name) = named.target.as_ref()
                            && self.module_walrus_targets.is_some_and(|targets| {
                                targets.contains(
                                    mangle_name(name.id.as_str(), self.private_name).as_ref(),
                                )
                            })
                        {
                            // Native extends the containing scope before visiting the value.
                            // Its DEF_GLOBAL admission reserves this symbol's first position.
                            self.targets.insert(
                                mangle_name(name.id.as_str(), self.private_name).into_owned(),
                            );
                            self.names.push((name.id.to_string(), false));
                        }
                        self.visit_expr(&named.value);
                        self.visit_expr(&named.target);
                        return;
                    }
                    Expr::Name(name) => {
                        self.names.push((name.id.as_str().to_string(), false));
                        if self.all_symbols && name.id.as_str() == "super" {
                            self.names.push(("__class__".to_string(), false));
                        }
                        return;
                    }
                    Expr::Dict(dictionary)
                        if self.all_symbols || self.module_walrus_targets.is_some() =>
                    {
                        for item in &dictionary.items {
                            if let Some(key) = &item.key {
                                self.visit_expr(key);
                            }
                        }
                        for item in &dictionary.items {
                            self.visit_expr(&item.value);
                        }
                        return;
                    }
                    _ => {
                        walk_expr(self, expression);
                        return;
                    }
                }
            };
            if let Some(first) = generators.first() {
                self.visit_expr(&first.iter);
            }
            let child = Self::comprehension(
                generators,
                key,
                value,
                self.all_symbols,
                self.module_walrus_targets,
                self.private_name,
            );
            self.targets.extend(child.targets);
            self.nested_names.extend(child.names);
        }
    }

    let mut collector = Collector::comprehension(
        generators,
        key,
        value,
        all_symbols,
        module_walrus_targets,
        private_name,
    );
    if all_symbols {
        let mut seen = FxHashSet::default();
        collector.names.retain(|name| seen.insert(name.clone()));
    } else {
        collector.names.retain(|(name, _)| {
            collector
                .targets
                .remove(mangle_name(name, private_name).as_ref())
        });
    }
    collector.names
}

/// Return each inlined symbol's binding role: true for bound, false for external.
/// Own symbols precede inlined children; otherwise the first child admission wins.
pub(super) fn comprehension_name_bindings(
    generators: &[ruff_python_ast::Comprehension],
    key: Option<&Expr>,
    value: &Expr,
) -> BTreeMap<String, bool> {
    comprehension_name_bindings_with_parent_requirements(
        generators,
        key,
        value,
        false,
        &mut ExpressionScopeCache::default(),
    )
}

fn comprehension_name_bindings_with_parent_requirements<'ast>(
    generators: &'ast [ruff_python_ast::Comprehension],
    key: Option<&'ast Expr>,
    value: &'ast Expr,
    include_generator_parent_requirements: bool,
    cache: &mut ExpressionScopeCache<'ast>,
) -> BTreeMap<String, bool> {
    struct Collector<'cache, 'ast> {
        symbols: BTreeMap<String, bool>,
        children: Vec<BTreeMap<String, bool>>,
        closure_references: BTreeSet<String>,
        include_generator_parent_requirements: bool,
        cache: &'cache mut ExpressionScopeCache<'ast>,
    }

    impl<'ast> Collector<'_, 'ast> {
        fn comprehension(
            generators: &'ast [ruff_python_ast::Comprehension],
            key: Option<&'ast Expr>,
            value: &'ast Expr,
            include_generator_parent_requirements: bool,
            cache: &mut ExpressionScopeCache<'ast>,
        ) -> BTreeMap<String, bool> {
            let mut collector = Collector {
                include_generator_parent_requirements,
                symbols: BTreeMap::new(),
                children: Vec::new(),
                closure_references: BTreeSet::new(),
                cache,
            };
            for generator in generators {
                let mut targets = Vec::new();
                collect_target_names(&generator.target, &mut targets);
                collector
                    .symbols
                    .extend(targets.into_iter().map(|name| (name, true)));
            }
            for (index, generator) in generators.iter().enumerate() {
                collector.visit_expr(&generator.target);
                if index > 0 {
                    collector.visit_expr(&generator.iter);
                }
                for condition in &generator.ifs {
                    collector.visit_expr(condition);
                }
            }
            collector.visit_expr(value);
            if let Some(key) = key {
                collector.visit_expr(key);
            }
            for child in collector.children {
                for (name, bound) in child {
                    collector.symbols.entry(name).or_insert(bound);
                }
            }
            for name in collector.closure_references {
                collector.symbols.entry(name).or_insert(false);
            }
            collector.symbols
        }
    }

    impl<'ast> Visitor<'ast> for Collector<'_, 'ast> {
        fn visit_expr(&mut self, expression: &'ast Expr) {
            if crate::stack_growth_required() {
                return crate::grow_stack(|| self.visit_expr(expression));
            }

            let Some((generators, key, value)) = comprehension_parts(expression) else {
                match expression {
                    Expr::Generator(generator) => {
                        if let Some(first) = generator.generators.first() {
                            self.visit_expr(&first.iter);
                        }
                        let required = if self.include_generator_parent_requirements {
                            generator_parent_requirements_with_cache(generator, self.cache)
                        } else {
                            generator_required_names_with_cache(generator, self.cache)
                        };
                        self.closure_references.extend(required);
                        return;
                    }
                    Expr::Lambda(lambda) => {
                        visit_lambda_defaults(self, lambda);
                        self.closure_references
                            .extend(lambda_required_names_with_cache(lambda, self.cache));
                        return;
                    }
                    Expr::Dict(dictionary) => {
                        for item in &dictionary.items {
                            if let Some(key) = &item.key {
                                self.visit_expr(key);
                            }
                        }
                        for item in &dictionary.items {
                            self.visit_expr(&item.value);
                        }
                        return;
                    }
                    Expr::Named(named) => {
                        if let Expr::Name(name) = named.target.as_ref() {
                            self.symbols.entry(name.id.to_string()).or_insert(false);
                        }
                        self.visit_expr(&named.value);
                        return;
                    }
                    Expr::Name(name) if name.ctx == ExprContext::Load => {
                        self.symbols.entry(name.id.to_string()).or_insert(false);
                        if name.id.as_str() == "super" {
                            self.symbols.entry("__class__".to_string()).or_insert(false);
                        }
                        return;
                    }
                    _ => {
                        walk_expr(self, expression);
                        return;
                    }
                }
            };
            if let Some(first) = generators.first() {
                self.visit_expr(&first.iter);
            }
            let child = Self::comprehension(
                generators,
                key,
                value,
                self.include_generator_parent_requirements,
                self.cache,
            );
            self.children.push(child);
        }
    }

    Collector::comprehension(
        generators,
        key,
        value,
        include_generator_parent_requirements,
        cache,
    )
}

/// Compare alias identities before child admission, retaining raw escaping names.
fn comprehension_bindings_in_private_context(
    expression: &Expr,
    private_name: Option<&str>,
) -> BTreeMap<String, bool> {
    let collect = |expression: &Expr| match expression {
        Expr::ListComp(comprehension) => {
            comprehension_name_bindings(&comprehension.generators[..], None, &comprehension.elt)
        }
        Expr::SetComp(comprehension) => {
            comprehension_name_bindings(&comprehension.generators[..], None, &comprehension.elt)
        }
        Expr::DictComp(comprehension) => comprehension_name_bindings(
            &comprehension.generators[..],
            comprehension.key.as_deref(),
            &comprehension.value,
        ),
        _ => unreachable!("inlined comprehension expression"),
    };
    let raw = collect(expression);
    let Some(private_name) = private_name else {
        return raw;
    };
    let mut spellings = VariableSpellings::default();
    spellings.visit_expr(expression);
    let aliases = colliding_private_spellings(&spellings.names, &|name| {
        mangle_name(name, Some(private_name)).into_owned()
    });
    if aliases.is_empty() {
        return raw;
    }
    let normalize = |name: &str| {
        aliases
            .get(name)
            .cloned()
            .unwrap_or_else(|| name.to_owned())
    };
    let mut depth = crate::stack::ExpressionDepth::default();
    depth.visit_expr(expression);
    crate::stack::with_depth(depth.maximum(), || {
        let mut normalized = expression.clone();
        ruff_python_ast::visitor::transformer::Transformer::visit_expr(
            &PrivateVariableNormalizer { mangle: &normalize },
            &mut normalized,
        );
        let bindings = collect(&normalized);
        // Reuse the existing own/first-child precedence, including its exclusion of
        // the first iterable. Only symbol identity changes before that traversal.
        remap_comprehension_bindings(raw, &bindings, &aliases)
    })
}

/// Preserve comprehension binding precedence when private spellings share a name.
pub(super) fn comprehension_name_bindings_with_mangler(
    generators: &[ruff_python_ast::Comprehension],
    key: Option<&Expr>,
    value: &Expr,
    mangle: &impl Fn(&str) -> String,
) -> BTreeMap<String, bool> {
    let raw = comprehension_name_bindings(generators, key, value);
    let mut spellings = VariableSpellings::default();
    for generator in generators {
        spellings.visit_expr(&generator.target);
        spellings.visit_expr(&generator.iter);
        for condition in &generator.ifs {
            spellings.visit_expr(condition);
        }
    }
    if let Some(key) = key {
        spellings.visit_expr(key);
    }
    spellings.visit_expr(value);
    let aliases = colliding_private_spellings(&spellings.names, mangle);
    if aliases.is_empty() {
        return raw;
    }
    let normalize = |name: &str| {
        aliases
            .get(name)
            .cloned()
            .unwrap_or_else(|| name.to_owned())
    };
    let transformer = PrivateVariableNormalizer { mangle: &normalize };
    let mut depth = crate::stack::ExpressionDepth::default();
    for generator in generators {
        depth.visit_comprehension(generator);
    }
    if let Some(key) = key {
        depth.visit_expr(key);
    }
    depth.visit_expr(value);
    crate::stack::with_depth(depth.maximum(), || {
        let mut generators = generators.to_vec();
        let mut key = key.cloned();
        let mut value = value.clone();
        for generator in &mut generators {
            ruff_python_ast::visitor::transformer::Transformer::visit_comprehension(
                &transformer,
                generator,
            );
        }
        if let Some(key) = &mut key {
            ruff_python_ast::visitor::transformer::Transformer::visit_expr(&transformer, key);
        }
        ruff_python_ast::visitor::transformer::Transformer::visit_expr(&transformer, &mut value);
        let bindings = comprehension_name_bindings(&generators, key.as_ref(), &value);
        remap_comprehension_bindings(raw, &bindings, &aliases)
    })
}

/// Map normalized binding identities back to their original source spellings.
#[inline(never)]
fn remap_comprehension_bindings(
    raw: BTreeMap<String, bool>,
    bindings: &BTreeMap<String, bool>,
    aliases: &FxHashMap<String, String>,
) -> BTreeMap<String, bool> {
    raw.into_keys()
        .filter_map(|name| {
            let normalized = aliases.get(&name).map_or(name.as_str(), String::as_str);
            bindings.get(normalized).map(|bound| (name, *bound))
        })
        .collect()
}

pub(super) fn collect_nested_comprehension_target_names(
    expression: &Expr,
    names: &mut Vec<String>,
) {
    struct Collector<'a> {
        names: &'a mut Vec<String>,
    }

    impl<'ast> Visitor<'ast> for Collector<'_> {
        fn visit_expr(&mut self, expression: &'ast Expr) {
            if crate::stack_growth_required() {
                return crate::grow_stack(|| self.visit_expr(expression));
            }

            let generators = match expression {
                Expr::ListComp(comprehension) => Some(&comprehension.generators[..]),
                Expr::SetComp(comprehension) => Some(&comprehension.generators[..]),
                Expr::DictComp(comprehension) => Some(&comprehension.generators[..]),
                Expr::Generator(generator) => {
                    if let Some(first) = generator.generators.first() {
                        self.visit_expr(&first.iter);
                    }
                    return;
                }
                Expr::Lambda(lambda) => {
                    visit_lambda_defaults(self, lambda);
                    return;
                }
                _ => None,
            };
            if let Some(generators) = generators {
                for generator in generators {
                    collect_target_names(&generator.target, self.names);
                }
            }
            walk_expr(self, expression);
        }
    }

    Collector { names }.visit_expr(expression);
}

/// Collect generator fast-local uses and inlined comprehension saves in evaluation order.
pub(super) fn collect_generator_slot_names(
    expression: &Expr,
    generator_locals: &FxHashSet<String>,
    generator_cellvars: &FxHashSet<String>,
    names: &mut Vec<String>,
) {
    struct Collector<'a> {
        generator_locals: &'a FxHashSet<String>,
        generator_cellvars: &'a FxHashSet<String>,
        names: &'a mut Vec<String>,
    }

    impl<'ast> Visitor<'ast> for Collector<'_> {
        fn visit_expr(&mut self, expression: &'ast Expr) {
            if crate::stack_growth_required() {
                return crate::grow_stack(|| self.visit_expr(expression));
            }

            let Some((generators, key, value)) = comprehension_parts(expression) else {
                match expression {
                    Expr::Generator(generator) => {
                        if let Some(first) = generator.generators.first() {
                            self.visit_expr(&first.iter);
                        }
                        return;
                    }
                    Expr::Lambda(lambda) => {
                        visit_lambda_defaults(self, lambda);
                        return;
                    }
                    Expr::Name(name) => {
                        let name = name.id.as_str();
                        if self.generator_locals.contains(name)
                            && !self.generator_cellvars.contains(name)
                        {
                            self.names.push(name.to_owned());
                        }
                        return;
                    }
                    _ => {
                        walk_expr(self, expression);
                        return;
                    }
                }
            };
            if let Some(first) = generators.first() {
                self.visit_expr(&first.iter);
            }
            let temporary_names = comprehension_temporary_names(generators, key, value);
            let mut direct_targets = Vec::new();
            for generator in generators {
                collect_target_names(&generator.target, &mut direct_targets);
            }
            let deferred_outer_names = comprehension_name_bindings(generators, key, value)
                .into_iter()
                .filter(|(name, bound)| !bound && !direct_targets.contains(name))
                .map(|(name, _)| name)
                .collect::<FxHashSet<_>>();
            // An inlined child can shadow a name that its parent reads from an
            // enclosing scope. The child owns that save, after the parent's saves.
            self.names.extend(
                temporary_names
                    .into_iter()
                    .filter(|name| !deferred_outer_names.contains(name)),
            );
            for (index, generator) in generators.iter().enumerate() {
                if index > 0 {
                    self.visit_expr(&generator.iter);
                }
                self.visit_expr(&generator.target);
                for condition in &generator.ifs {
                    self.visit_expr(condition);
                }
            }
            if let Some(key) = key {
                self.visit_expr(key);
            }
            self.visit_expr(value);
        }
    }

    Collector {
        generator_locals,
        generator_cellvars,
        names,
    }
    .visit_expr(expression);
}

pub(super) fn collect_self_iterated_nested_comprehension_targets(
    expression: &Expr,
    names: &mut Vec<String>,
) {
    struct Collector<'a> {
        names: &'a mut Vec<String>,
    }

    impl<'ast> Visitor<'ast> for Collector<'_> {
        fn visit_expr(&mut self, expression: &'ast Expr) {
            if crate::stack_growth_required() {
                return crate::grow_stack(|| self.visit_expr(expression));
            }

            let generators = match expression {
                Expr::ListComp(comprehension) => Some(&comprehension.generators[..]),
                Expr::SetComp(comprehension) => Some(&comprehension.generators[..]),
                Expr::DictComp(comprehension) => Some(&comprehension.generators[..]),
                Expr::Generator(_) | Expr::Lambda(_) => return,
                _ => None,
            };
            if let Some(generators) = generators {
                for generator in generators {
                    let Some(references) = definitely_evaluated_references(&generator.iter) else {
                        continue;
                    };
                    let mut targets = Vec::new();
                    collect_target_names(&generator.target, &mut targets);
                    self.names.extend(
                        targets
                            .into_iter()
                            .filter(|name| references.binary_search(&name.as_str()).is_ok()),
                    );
                }
            }
            walk_expr(self, expression);
        }
    }

    Collector { names }.visit_expr(expression);
}

pub(super) fn comprehension_cell_names(
    generators: &[ruff_python_ast::Comprehension],
    key: Option<&Expr>,
    value: &Expr,
) -> FxHashSet<String> {
    comprehension_cell_names_in_private_context(generators, key, value, None)
}

/// Return source target spellings captured under the current private-name context.
pub(super) fn comprehension_cell_names_in_private_context(
    generators: &[ruff_python_ast::Comprehension],
    key: Option<&Expr>,
    value: &Expr,
    private_name: Option<&str>,
) -> FxHashSet<String> {
    comprehension_cell_names_with_mangler(generators, key, value, &|name| {
        mangle_name(name, private_name).into_owned()
    })
}

/// Return captured target spellings using declaration-time symbol identities.
pub(super) fn comprehension_cell_names_with_mangler(
    generators: &[ruff_python_ast::Comprehension],
    key: Option<&Expr>,
    value: &Expr,
    mangle: &impl Fn(&str) -> String,
) -> FxHashSet<String> {
    let nested_required = |expression: &Expr| {
        contextual_expression_requirements(expression, mangle, nested_expression_required_names)
    };
    let mut targets = Vec::new();
    let mut required = BTreeSet::new();
    for (index, generator) in generators.iter().enumerate() {
        collect_target_names(&generator.target, &mut targets);
        collect_nested_comprehension_target_names(&generator.target, &mut targets);
        required.extend(nested_required(&generator.target));
        if index > 0 {
            collect_nested_comprehension_target_names(&generator.iter, &mut targets);
            required.extend(nested_required(&generator.iter));
        }
        for condition in &generator.ifs {
            collect_nested_comprehension_target_names(condition, &mut targets);
            required.extend(nested_required(condition));
        }
    }
    if let Some(key) = key {
        collect_nested_comprehension_target_names(key, &mut targets);
        required.extend(nested_required(key));
    }
    collect_nested_comprehension_target_names(value, &mut targets);
    required.extend(nested_required(value));

    let required = required
        .iter()
        .map(|name| mangle(name))
        .collect::<FxHashSet<_>>();
    targets
        .into_iter()
        .filter(|name| required.contains(&mangle(name)))
        .collect()
}

pub(super) fn inlined_comprehension_cell_names_in_expression(
    expression: &Expr,
) -> FxHashSet<String> {
    #[derive(Default)]
    struct Collector {
        names: FxHashSet<String>,
    }

    impl<'ast> Visitor<'ast> for Collector {
        fn visit_expr(&mut self, expression: &'ast Expr) {
            if crate::stack_growth_required() {
                return crate::grow_stack(|| self.visit_expr(expression));
            }

            match expression {
                Expr::ListComp(comprehension) => self.names.extend(comprehension_cell_names(
                    &comprehension.generators[..],
                    None,
                    &comprehension.elt,
                )),
                Expr::SetComp(comprehension) => self.names.extend(comprehension_cell_names(
                    &comprehension.generators[..],
                    None,
                    &comprehension.elt,
                )),
                Expr::DictComp(comprehension) => self.names.extend(comprehension_cell_names(
                    &comprehension.generators[..],
                    comprehension.key.as_deref(),
                    &comprehension.value,
                )),
                Expr::Lambda(lambda) => {
                    visit_lambda_defaults(self, lambda);
                    return;
                }
                Expr::Generator(generator) => {
                    if let Some(first) = generator.generators.first() {
                        self.visit_expr(&first.iter);
                    }
                    return;
                }
                _ => {}
            }
            walk_expr(self, expression);
        }
    }

    let mut collector = Collector::default();
    collector.visit_expr(expression);
    collector.names
}

pub(super) fn collect_named_expression_target_names(expression: &Expr, names: &mut Vec<String>) {
    struct Collector<'a> {
        names: &'a mut Vec<String>,
    }

    impl<'ast> Visitor<'ast> for Collector<'_> {
        fn visit_expr(&mut self, expression: &'ast Expr) {
            if crate::stack_growth_required() {
                return crate::grow_stack(|| self.visit_expr(expression));
            }

            if let Expr::Named(named) = expression
                && let Expr::Name(name) = named.target.as_ref()
            {
                self.names.push(name.id.as_str().to_string());
            }
            if matches!(expression, Expr::Generator(_) | Expr::Lambda(_)) {
                return;
            }
            walk_expr(self, expression);
        }
    }

    Collector { names }.visit_expr(expression);
}

pub(super) fn generator_named_targets(
    generator: &ruff_python_ast::ExprGenerator,
) -> FxHashSet<String> {
    #[derive(Default)]
    struct Collector {
        names: FxHashSet<String>,
    }

    impl<'ast> Visitor<'ast> for Collector {
        fn visit_expr(&mut self, expression: &'ast Expr) {
            if crate::stack_growth_required() {
                return crate::grow_stack(|| self.visit_expr(expression));
            }

            if let Expr::Lambda(lambda) = expression {
                visit_lambda_defaults(self, lambda);
                return;
            }
            if let Expr::Named(named) = expression
                && let Expr::Name(name) = named.target.as_ref()
            {
                self.names.insert(name.id.as_str().to_string());
            }
            walk_expr(self, expression);
        }
    }

    let mut collector = Collector::default();
    collector.visit_expr(&generator.elt);
    for comprehension in &generator.generators {
        collector.visit_expr(&comprehension.iter);
        for condition in &comprehension.ifs {
            collector.visit_expr(condition);
        }
    }
    collector.names
}

/// Names used outside the inlined comprehension targets that shadow them.
pub(super) fn generator_external_names(
    generator: &ruff_python_ast::ExprGenerator,
    mangle: &impl Fn(&str) -> String,
) -> (FxHashSet<String>, FxHashSet<String>, FxHashSet<String>) {
    generator_external_names_with_cache(generator, mangle, &mut ExpressionScopeCache::default())
}

fn generator_external_names_with_cache<'ast>(
    generator: &'ast ruff_python_ast::ExprGenerator,
    mangle: &impl Fn(&str) -> String,
    cache: &mut ExpressionScopeCache<'ast>,
) -> (FxHashSet<String>, FxHashSet<String>, FxHashSet<String>) {
    struct Collector<'a, 'cache, 'ast, M> {
        names: FxHashSet<String>,
        closure_names: FxHashSet<String>,
        captured_targets: FxHashSet<String>,
        targets: Vec<FxHashSet<String>>,
        mangle: &'a M,
        cache: &'cache mut ExpressionScopeCache<'ast>,
    }

    impl<M: Fn(&str) -> String> Collector<'_, '_, '_, M> {
        fn insert(&mut self, name: &str) {
            let canonical = (self.mangle)(name);
            if !self
                .targets
                .iter()
                .any(|targets| targets.contains(&canonical))
            {
                self.names.insert(name.to_owned());
            }
        }

        fn insert_closure(&mut self, name: &str) {
            let canonical = (self.mangle)(name);
            if self
                .targets
                .iter()
                .any(|targets| targets.contains(&canonical))
            {
                self.captured_targets.insert(canonical);
            } else {
                self.names.insert(name.to_owned());
                self.closure_names.insert(name.to_owned());
            }
        }
    }

    impl<'ast, M: Fn(&str) -> String> Visitor<'ast> for Collector<'_, '_, 'ast, M> {
        fn visit_expr(&mut self, expression: &'ast Expr) {
            if crate::stack_growth_required() {
                return crate::grow_stack(|| self.visit_expr(expression));
            }

            let Some((generators, key, value)) = comprehension_parts(expression) else {
                match expression {
                    Expr::Lambda(lambda) => {
                        visit_lambda_defaults(self, lambda);
                        for name in lambda_required_names_with_cache(lambda, self.cache) {
                            self.insert_closure(&name);
                        }
                        return;
                    }
                    Expr::Generator(generator) => {
                        if let Some(first) = generator.generators.first() {
                            self.visit_expr(&first.iter);
                        }
                        let mut own_targets = Vec::new();
                        for comprehension in &generator.generators {
                            collect_target_names(&comprehension.target, &mut own_targets);
                        }
                        let own_targets = own_targets
                            .iter()
                            .map(|name| (self.mangle)(name))
                            .collect::<FxHashSet<_>>();
                        let (names, _, _) =
                            generator_external_names_with_cache(generator, self.mangle, self.cache);
                        for name in names.into_iter().collect::<BTreeSet<_>>() {
                            if !own_targets.contains(&(self.mangle)(&name)) {
                                self.insert_closure(&name);
                            }
                        }
                        return;
                    }
                    Expr::Named(named) => {
                        if let Expr::Name(name) = named.target.as_ref() {
                            self.insert(name.id.as_str());
                        }
                        self.visit_expr(&named.value);
                        return;
                    }
                    Expr::Name(name) if name.ctx == ExprContext::Load => {
                        self.insert(name.id.as_str());
                        if name.id.as_str() == "super" {
                            self.insert("__class__");
                        }
                        return;
                    }
                    _ => {
                        walk_expr(self, expression);
                        return;
                    }
                }
            };

            if let Some(first) = generators.first() {
                self.visit_expr(&first.iter);
            }
            let mut targets = Vec::new();
            for generator in generators {
                collect_target_names(&generator.target, &mut targets);
            }
            self.targets
                .push(targets.iter().map(|name| (self.mangle)(name)).collect());
            for (index, generator) in generators.iter().enumerate() {
                self.visit_expr(&generator.target);
                if index > 0 {
                    self.visit_expr(&generator.iter);
                }
                for condition in &generator.ifs {
                    self.visit_expr(condition);
                }
            }
            if let Some(key) = key {
                self.visit_expr(key);
            }
            self.visit_expr(value);
            self.targets.pop();
        }
    }

    let mut collector = Collector {
        names: FxHashSet::default(),
        closure_names: FxHashSet::default(),
        captured_targets: FxHashSet::default(),
        targets: Vec::new(),
        mangle,
        cache,
    };
    for (index, comprehension) in generator.generators.iter().enumerate() {
        collector.visit_expr(&comprehension.target);
        if index > 0 {
            collector.visit_expr(&comprehension.iter);
        }
        for condition in &comprehension.ifs {
            collector.visit_expr(condition);
        }
    }
    collector.visit_expr(&generator.elt);
    (
        collector.names,
        collector.closure_names,
        collector.captured_targets,
    )
}

/// Include lexical child captures when promoting cells in the enclosing scope.
fn generator_parent_requirements(generator: &ruff_python_ast::ExprGenerator) -> BTreeSet<String> {
    generator_parent_requirements_with_cache(generator, &mut ExpressionScopeCache::default())
}

fn generator_parent_requirements_with_cache<'ast>(
    generator: &'ast ruff_python_ast::ExprGenerator,
    cache: &mut ExpressionScopeCache<'ast>,
) -> BTreeSet<String> {
    let key = std::ptr::from_ref(generator);
    if let Some(required) = cache.generator_parent_requirements.get(&key) {
        return required.clone();
    }
    let mut required = generator_required_names_with_cache(generator, cache);
    let mut generator_targets = Vec::new();
    for comprehension in &generator.generators {
        collect_target_names(&comprehension.target, &mut generator_targets);
    }
    let (_, closure_names, captured_targets) =
        generator_external_names_with_cache(generator, &str::to_owned, cache);
    required.extend(
        closure_names
            .into_iter()
            .filter(|name| captured_targets.contains(name) && !generator_targets.contains(name)),
    );
    cache
        .generator_parent_requirements
        .insert(key, required.clone());
    required
}

/// Resolve colliding private spellings before deciding which generator names escape.
pub(super) fn generator_required_names_with_mangler(
    generator: &ruff_python_ast::ExprGenerator,
    mangle: &impl Fn(&str) -> String,
) -> BTreeSet<String> {
    let mut depth = crate::stack::ExpressionDepth::default();
    depth.visit_expr(&generator.elt);
    for comprehension in &generator.generators {
        depth.visit_comprehension(comprehension);
    }
    crate::stack::with_depth(depth.maximum(), || {
        let expression = Expr::Generator(generator.clone());
        contextual_expression_requirements(&expression, mangle, |expression| {
            let Expr::Generator(generator) = expression else {
                unreachable!();
            };
            generator_required_names(generator)
        })
    })
}

/// Give private spellings of a generator local the same physical slot.
pub(super) fn generator_private_local_aliases(
    generator: &ruff_python_ast::ExprGenerator,
    locals: &mut Vec<String>,
    mangle: &impl Fn(&str) -> String,
) -> Vec<(String, String)> {
    let mut representatives = FxHashMap::default();
    locals.retain(|name| {
        if let std::collections::hash_map::Entry::Vacant(entry) =
            representatives.entry(mangle(name))
        {
            entry.insert(name.clone());
            true
        } else {
            false
        }
    });
    let mut spellings = VariableSpellings::default();
    spellings.visit_expr(&generator.elt);
    for comprehension in &generator.generators {
        spellings.visit_comprehension(comprehension);
    }
    spellings
        .names
        .into_iter()
        .filter_map(|name| {
            let original = representatives.get(&mangle(&name))?;
            (name != *original).then_some((name, original.clone()))
        })
        .collect()
}

pub(super) fn generator_required_names(
    generator: &ruff_python_ast::ExprGenerator,
) -> BTreeSet<String> {
    generator_required_names_with_cache(generator, &mut ExpressionScopeCache::default())
}

fn generator_required_names_with_cache<'ast>(
    generator: &'ast ruff_python_ast::ExprGenerator,
    cache: &mut ExpressionScopeCache<'ast>,
) -> BTreeSet<String> {
    struct InlineExternalReferences<'cache, 'ast> {
        names: FxHashSet<String>,
        nested: BTreeSet<String>,
        cache: &'cache mut ExpressionScopeCache<'ast>,
    }

    impl<'ast> Visitor<'ast> for InlineExternalReferences<'_, 'ast> {
        fn visit_expr(&mut self, expression: &'ast Expr) {
            if crate::stack_growth_required() {
                return crate::grow_stack(|| self.visit_expr(expression));
            }

            let Some((generators, key, value)) = comprehension_parts(expression) else {
                match expression {
                    Expr::Lambda(lambda) => {
                        visit_lambda_defaults(self, lambda);
                        self.nested
                            .extend(lambda_required_names_with_cache(lambda, self.cache));
                        return;
                    }
                    Expr::Generator(generator) => {
                        if let Some(first) = generator.generators.first() {
                            self.visit_expr(&first.iter);
                        }
                        self.nested.extend(generator_parent_requirements_with_cache(
                            generator, self.cache,
                        ));
                        return;
                    }
                    _ => {
                        walk_expr(self, expression);
                        return;
                    }
                }
            };
            if let Some(first) = generators.first() {
                self.visit_expr(&first.iter);
            }
            let external = comprehension_name_bindings_with_parent_requirements(
                generators, key, value, true, self.cache,
            )
            .into_iter()
            .filter_map(|(name, bound)| (!bound).then_some(name));
            self.names.extend(external);
        }
    }

    fn collect_requirements<'ast>(
        expression: &'ast Expr,
        local_names: &mut FxHashSet<String>,
        references: &mut ReferenceCollector,
        outside_references: &mut ReferenceCollector,
        nested_requirements: &mut BTreeSet<String>,
        cache: &mut ExpressionScopeCache<'ast>,
    ) {
        let mut names = Vec::new();
        collect_nested_comprehension_target_names(expression, &mut names);
        local_names.extend(names);
        references.visit_expr(expression);
        outside_references.visit_expr(expression);
        let mut inlined = InlineExternalReferences {
            names: FxHashSet::default(),
            nested: BTreeSet::new(),
            cache,
        };
        inlined.visit_expr(expression);
        nested_requirements.extend(inlined.names.iter().cloned());
        nested_requirements.extend(inlined.nested);
        outside_references.references.extend(inlined.names);
    }

    let key = std::ptr::from_ref(generator);
    if let Some(required) = cache.generator_requirements.get(&key) {
        return required.clone();
    }
    let mut local_names = FxHashSet::default();
    for comprehension in &generator.generators {
        let mut names = Vec::new();
        collect_target_names(&comprehension.target, &mut names);
        local_names.extend(names);
    }

    let generator_targets = local_names.clone();
    let mut references = ReferenceCollector {
        skip_generator_bodies: true,
        ..ReferenceCollector::default()
    };
    let mut outside_references = ReferenceCollector {
        skip_generator_bodies: true,
        skip_inlined_comprehension_bodies: true,
        ..ReferenceCollector::default()
    };
    let mut nested_requirements = BTreeSet::new();
    collect_requirements(
        &generator.elt,
        &mut local_names,
        &mut references,
        &mut outside_references,
        &mut nested_requirements,
        cache,
    );
    for (index, comprehension) in generator.generators.iter().enumerate() {
        collect_requirements(
            &comprehension.target,
            &mut local_names,
            &mut references,
            &mut outside_references,
            &mut nested_requirements,
            cache,
        );
        // The outermost iterable is evaluated by the enclosing scope and passed
        // to the generator as its implicit `.0` argument.
        if index > 0 {
            collect_requirements(
                &comprehension.iter,
                &mut local_names,
                &mut references,
                &mut outside_references,
                &mut nested_requirements,
                cache,
            );
        }
        for condition in &comprehension.ifs {
            collect_requirements(
                condition,
                &mut local_names,
                &mut references,
                &mut outside_references,
                &mut nested_requirements,
                cache,
            );
        }
    }
    references
        .references
        .extend(generator_named_targets(generator));
    references.references.extend(nested_requirements);
    // Inlined targets need temporary local slots without hiding reads in the generator body
    // or in the comprehension's first iterable.
    let required: BTreeSet<_> = references
        .references
        .into_iter()
        .filter(|name| {
            !local_names.contains(name)
                || (outside_references.references.contains(name)
                    && !generator_targets.contains(name))
        })
        .collect();
    cache.generator_requirements.insert(key, required.clone());
    required
}

fn generator_cellvar_local_names(generator: &ruff_python_ast::ExprGenerator) -> FxHashSet<String> {
    let mut local_names = FxHashSet::default();
    for comprehension in &generator.generators {
        let mut names = Vec::new();
        collect_target_names(&comprehension.target, &mut names);
        local_names.extend(names);
    }
    let mut extend_local_names = |expression: &Expr| {
        let mut names = Vec::new();
        collect_nested_comprehension_target_names(expression, &mut names);
        local_names.extend(names);
    };
    extend_local_names(&generator.elt);
    for (index, comprehension) in generator.generators.iter().enumerate() {
        extend_local_names(&comprehension.target);
        if index > 0 {
            extend_local_names(&comprehension.iter);
        }
        for condition in &comprehension.ifs {
            extend_local_names(condition);
        }
    }
    local_names
}

/// Analyze captures after resolving colliding private spellings, preserving target names.
pub(super) fn generator_cellvars_with_mangler(
    generator: &ruff_python_ast::ExprGenerator,
    mangle: &impl Fn(&str) -> String,
) -> FxHashSet<String> {
    let mut depth = crate::stack::ExpressionDepth::default();
    depth.visit_expr(&generator.elt);
    for comprehension in &generator.generators {
        depth.visit_comprehension(comprehension);
    }
    crate::stack::with_depth(depth.maximum(), || {
        let expression = Expr::Generator(generator.clone());
        let mut spellings = VariableSpellings::default();
        spellings.visit_expr(&expression);
        let aliases = colliding_private_spellings(&spellings.names, mangle);
        if aliases.is_empty() {
            return generator_cellvars(generator);
        }
        let normalize = |name: &str| {
            aliases
                .get(name)
                .cloned()
                .unwrap_or_else(|| name.to_owned())
        };
        let mut normalized = expression;
        ruff_python_ast::visitor::transformer::Transformer::visit_expr(
            &PrivateVariableNormalizer { mangle: &normalize },
            &mut normalized,
        );
        let Expr::Generator(normalized) = normalized else {
            unreachable!()
        };
        let cells = generator_cellvars(&normalized);
        generator_cellvar_local_names(generator)
            .into_iter()
            .filter(|name| cells.contains(&normalize(name)))
            .collect()
    })
}

pub(super) fn generator_cellvars(generator: &ruff_python_ast::ExprGenerator) -> FxHashSet<String> {
    let local_names = generator_cellvar_local_names(generator);
    let mut nested_requirements = nested_expression_required_names(&generator.elt);
    for (index, comprehension) in generator.generators.iter().enumerate() {
        nested_requirements.extend(nested_expression_required_names(&comprehension.target));
        if index > 0 {
            nested_requirements.extend(nested_expression_required_names(&comprehension.iter));
        }
        for condition in &comprehension.ifs {
            nested_requirements.extend(nested_expression_required_names(condition));
        }
    }
    nested_requirements
        .into_iter()
        .filter(|name| local_names.contains(name))
        .collect()
}
pub(super) fn future_feature_flags(body: &[Stmt]) -> u32 {
    body.iter()
        .filter_map(|statement| {
            let Stmt::ImportFrom(import) = statement else {
                return None;
            };
            (import.level == 0 && import.module.as_deref() == Some("__future__")).then_some(import)
        })
        .flat_map(|import| &import.names)
        .fold(0, |flags, alias| {
            flags
                | match alias.name.as_str() {
                    "barry_as_FLUFL" => CO_FUTURE_BARRY_AS_BDFL,
                    "annotations" => CO_FUTURE_ANNOTATIONS,
                    _ => 0,
                }
        })
}

pub(super) fn has_annotations(body: &[Stmt]) -> bool {
    #[derive(Default)]
    struct AnnotationFinder(bool);

    impl<'ast> Visitor<'ast> for AnnotationFinder {
        fn visit_stmt(&mut self, statement: &'ast Stmt) {
            match statement {
                Stmt::AnnAssign(_) => self.0 = true,
                Stmt::FunctionDef(_) | Stmt::ClassDef(_) => {}
                _ if !self.0 => walk_stmt(self, statement),
                _ => {}
            }
        }

        fn visit_expr(&mut self, _expression: &'ast Expr) {}
    }

    let mut finder = AnnotationFinder::default();
    for statement in body {
        finder.visit_stmt(statement);
    }
    finder.0
}

pub(super) fn collect_conditional_simple_annotations<'a>(
    body: &'a [Stmt],
    annotations: &mut Vec<&'a ruff_python_ast::StmtAnnAssign>,
) {
    for statement in body {
        if !matches!(statement, Stmt::AnnAssign(_)) {
            collect_simple_annotations(std::slice::from_ref(statement), annotations);
        }
    }
}

pub(super) fn collect_simple_annotations<'a>(
    body: &'a [Stmt],
    annotations: &mut Vec<&'a ruff_python_ast::StmtAnnAssign>,
) {
    for statement in body {
        match statement {
            Stmt::AnnAssign(annotation) if annotation.simple => annotations.push(annotation),
            Stmt::If(statement) => {
                collect_simple_annotations(&statement.body, annotations);
                for clause in &statement.elif_else_clauses {
                    collect_simple_annotations(&clause.body, annotations);
                }
            }
            Stmt::For(statement) => {
                collect_simple_annotations(&statement.body, annotations);
                collect_simple_annotations(&statement.orelse, annotations);
            }
            Stmt::While(statement) => {
                collect_simple_annotations(&statement.body, annotations);
                collect_simple_annotations(&statement.orelse, annotations);
            }
            Stmt::Try(statement) => {
                collect_simple_annotations(&statement.body, annotations);
                collect_simple_annotations(&statement.orelse, annotations);
                for handler in &statement.handlers {
                    if let Some(handler) = handler.as_except_handler() {
                        collect_simple_annotations(&handler.body, annotations);
                    }
                }
                collect_simple_annotations(&statement.finalbody, annotations);
                // Try/finally lowers the final body once for the normal path and once for the
                // exceptional path. CPython records deferred annotations during both copies.
                collect_simple_annotations(&statement.finalbody, annotations);
            }
            Stmt::With(statement) => {
                collect_simple_annotations(&statement.body, annotations);
            }
            Stmt::Match(statement) => {
                for case in &statement.cases {
                    collect_simple_annotations(&case.body, annotations);
                }
            }
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {

    use ruff_python_ast::visitor::{Visitor, walk_expr, walk_stmt};
    use ruff_python_ast::{Expr, Stmt, StmtFunctionDef};
    use ruff_python_parser::parse_module;
    use ruff_text_size::{Ranged, TextSize};
    use rustc_hash::{FxHashMap, FxHashSet};

    use crate::PythonVersion;

    use super::super::statement::function_body_contains_yield;
    use super::{
        AssertionMode, FlatFunctionInputs, FunctionPlan, LocalCollector, ModuleNameCollector, Name,
        NameId, NameInterner, NameSet, SCOPE_SEED_NAMES, ScopeArena, ScopeDefinition, ScopeId,
        definitely_evaluated_references, has_annotations,
    };

    #[test]
    fn class_comprehension_detection_excludes_method_bodies_but_keeps_headers() {
        for (source, expected) in [
            ("result = [x for x in values]\n", false),
            (
                "class C:\n    def method(self):\n        return [x for x in values]\n",
                false,
            ),
            (
                "class C:\n    @decorate([x for x in values])\n    def method(self):\n        pass\n",
                true,
            ),
            (
                "class C:\n    def method(self, value=[x for x in values]):\n        pass\n",
                true,
            ),
            (
                "class C:\n    def method(self, value: [x for x in values]):\n        pass\n",
                true,
            ),
            ("class C:\n    values = {x: x for x in values}\n", true),
            ("class C:\n    values = (x for x in values)\n", true),
            ("class C(*(base for base in bases)):\n    pass\n", true),
            (
                "def outer():\n    class C:\n        values = {x for x in values}\n",
                true,
            ),
            (
                "class C:\n    def method(self):\n        class D:\n            pass\n        return [x for x in values]\n",
                false,
            ),
        ] {
            let parsed = parse_module(source).unwrap();
            let (facts, _, _) =
                ModuleNameCollector::collect(&mut NameInterner::seeded(), parsed.suite(), true);
            assert_eq!(facts.has_class_comprehensions, expected, "{source}");
            let scopes = ScopeArena::analyze_with_source(
                parsed.suite(),
                PythonVersion::Py312,
                &mut super::SourceAnalysis::new(PythonVersion::Py312, 0),
            );
            assert_eq!(
                scopes.module().has_class_comprehensions,
                expected,
                "{source}"
            );
        }
    }

    #[test]
    fn omitted_flat_records_preserve_name_interning_order() {
        let parsed = parse_module(
            "def f(parameter):\n    target += value\n    annotated: annotation = initializer\n    return target, annotated, parameter\n",
        )
        .unwrap();
        let collect = |keep| {
            super::ScopeInputs::collect(
                parsed.suite(),
                PythonVersion::Py314,
                &mut super::SourceAnalysis::new(PythonVersion::Py314, 0),
                AssertionMode::Keep,
                keep,
            )
        };
        let complete = collect(true);
        let partial = collect(false);
        assert!(
            complete
                .definitions
                .iter()
                .any(|input| matches!(input.definition, ScopeDefinition::Function(_, Some(_), _)))
        );
        assert!(
            partial
                .definitions
                .iter()
                .all(|input| matches!(input.definition, ScopeDefinition::Function(_, None, _)))
        );
        for name in [
            "f",
            "parameter",
            "target",
            "value",
            "initializer",
            "annotation",
            "annotated",
        ] {
            let expected = complete.arena.names.get(name).unwrap();
            assert_eq!(partial.arena.names.get(name), Some(expected), "{name}");
        }
    }

    #[test]
    fn lowered_scope_facts_match_full_analysis_for_all_targets() {
        struct ResetFull(bool);

        impl Drop for ResetFull {
            fn drop(&mut self) {
                super::FORCE_FULL_LOWERED_SCOPES.set(self.0);
            }
        }

        let sources = [
            "assert hidden\ndef f(value):\n    return value\n",
            "assert hidden\ndef f(parameter):\n    target += value\n    annotated: annotation = initializer\n    return target, annotated, parameter\n",
            "assert hidden\nclass C:\n    values = [x for x in iterable]\n    def method(self):\n        target += value\n        annotated: annotation = initializer\n        return target, annotated\n",
            "assert [lambda: item for item in values]\nresult = [x for x in values]\n",
            "class C:\n    'docstring'\n    __field = 1\n    def method(self):\n        assert hidden\n        return [self.__field for x in values]\n",
            "class C:\n    assert [lambda: item for item in values]\n    field = 1\n",
            "class C:\n    assert hidden\n    values = [lambda: item for item in values]\n",
            "class C:\n    assert hidden\n    @decorate([x for x in values])\n    def method(self, value={x for x in values}):\n        return value\n",
            "class C:\n    assert hidden\n    def method(self, value: [x for x in values]):\n        return value\n",
            "from __future__ import annotations\nclass C:\n    assert hidden\n    field: [x for x in values]\n",
            "def outer(value):\n    assert hidden\n    class C:\n        def method(self):\n            return value, __class__\n    return C\n",
            "class Outer[T]:\n    assert hidden\n    class Inner:\n        def method(self):\n            return super(), T\n",
            "assert caf\u{e9}\nclass C:\n    __field = ''\n    def method(self):\n        return '\u{e9}', self.__field\n",
            "def generator(value):\n    assert (yield value)\nasync def coroutine():\n    assert await work()\n",
            "assert hidden\nclass C:\n    def before(self):\n        self._C__first += (lambda *, __first=0: None)\n        assert hidden\n    def after(self):\n        assert hidden\n        self._C__second += (lambda *, __second=0: None)\n",
            "assert hidden\nglobal shared\ndef outer():\n    value = 1\n    def inner():\n        nonlocal value\n        global shared\n        value += shared\n    return inner\n",
            "assert hidden\ndef f():\n    try:\n        return '%%' % value\n    finally:\n        assert cleanup()\n        empty = b'value' * 0\n",
            "assert hidden\nresult = [__debug__ for () in [()]]\n",
        ];
        for python_version in [
            PythonVersion::Py312,
            PythonVersion::Py313,
            PythonVersion::Py314,
            PythonVersion::Py315,
        ] {
            for optimization_level in [
                crate::OptimizationLevel::Zero,
                crate::OptimizationLevel::One,
                crate::OptimizationLevel::Two,
            ] {
                let options = crate::CompileOptions {
                    python_version,
                    optimization_level,
                    ..crate::CompileOptions::default()
                };
                for source in sources {
                    let fast = crate::compile_with_options(source, "lowered_scopes.py", &options);
                    let full = {
                        let _reset = ResetFull(super::FORCE_FULL_LOWERED_SCOPES.replace(true));
                        crate::compile_with_options(source, "lowered_scopes.py", &options)
                    };
                    match (fast, full) {
                        (Ok(fast), Ok(full)) => assert_eq!(
                            fast.marshal(),
                            full.marshal(),
                            "{python_version:?} {optimization_level:?}: {source}"
                        ),
                        (fast, full) => assert_eq!(
                            format!("{fast:?}"),
                            format!("{full:?}"),
                            "{python_version:?} {optimization_level:?}: {source}"
                        ),
                    }
                }
            }
        }
    }

    #[test]
    fn module_suspension_certificate_matches_forced_scope_walk_for_all_targets() {
        struct ResetGeneric(bool);

        impl Drop for ResetGeneric {
            fn drop(&mut self) {
                super::FORCE_GENERIC_SUSPENSION_SEARCH.set(self.0);
            }
        }

        let sources = [
            (
                r"
def pure(values, manager):
    if check(values, manager.field):
        assert other(values)
    while check(values):
        if stop(values):
            break
    try:
        return [item.field for item in values if guard(item)]
    except Error:
        return None
    finally:
        cleanup(manager)
def generator(values):
    yield from values
",
                false,
            ),
            (
                r"
def lazy(values):
    return (item async for item in values)
",
                false,
            ),
            (
                r"
async def active(values, manager):
    if await check(values):
        assert await other(manager)
    while await check(values):
        if stop(values):
            break
    try:
        return await finish(values)
    except Error:
        return None
    finally:
        await cleanup(manager)
",
                true,
            ),
            (
                r"
async def only_async_comprehensions(values):
    first = [item async for item in values]
    second = {item async for item in values}
    third = {item: item async for item in values}
    return first, second, third
",
                true,
            ),
            (
                r"
def ordinary(values):
    if check(values):
        return values
    async def nested():
        return (item for item in await consume(values))
    return nested
",
                true,
            ),
        ];
        for python_version in [
            PythonVersion::Py312,
            PythonVersion::Py313,
            PythonVersion::Py314,
            PythonVersion::Py315,
        ] {
            let options = crate::CompileOptions {
                python_version,
                ..crate::CompileOptions::default()
            };
            for (source, expected) in sources {
                let parsed = parse_module(source).unwrap();
                let arena = ScopeArena::analyze_with_python_version(parsed.suite(), python_version);
                assert_eq!(arena.module().has_suspension_expressions, expected);
                let fast = crate::compile_with_options(source, "suspension.py", &options).unwrap();
                let generic = {
                    let _reset = ResetGeneric(super::FORCE_GENERIC_SUSPENSION_SEARCH.replace(true));
                    crate::compile_with_options(source, "suspension.py", &options).unwrap()
                };
                assert_eq!(
                    format!("{:?}", fast.code),
                    format!("{:?}", generic.code),
                    "{python_version:?}: {source}"
                );
                assert_eq!(fast.marshal(), generic.marshal(), "{python_version:?}");
                let source_size = u32::try_from(source.len()).unwrap();
                assert_eq!(
                    fast.to_timestamp_pyc(17, source_size),
                    generic.to_timestamp_pyc(17, source_size),
                    "{python_version:?}"
                );
            }
        }
    }

    #[test]
    fn sparse_name_sets_keep_ascending_order_and_recognize_cleared_words() {
        let ids = [0, 1, 63, 64, 127, 128, 1023, 2048].map(NameId::from_usize);
        let mut names = NameSet::default();
        assert!(names.is_empty());
        assert!(names.iter_unordered().next().is_none());

        for &id in ids.iter().rev() {
            assert!(names.insert(id));
            assert!(!names.insert(id));
        }
        assert!(!names.is_empty());
        assert_eq!(names.iter_unordered().collect::<Vec<_>>(), ids);

        for index in [0, 1, 3, 6] {
            assert!(names.remove(ids[index]));
        }
        assert_eq!(names.words.len(), 33);
        assert_eq!(
            names.iter_unordered().collect::<Vec<_>>(),
            [ids[2], ids[4], ids[5], ids[7]]
        );

        assert!(names.remove(ids[7]));
        assert_eq!(names.words.len(), 3);
        assert!(!names.remove(ids[7]));
        for index in [2, 4, 5] {
            assert!(names.remove(ids[index]));
        }
        assert!(names.is_empty());
        assert!(names.words.is_empty());
        assert!(names.iter_unordered().next().is_none());
        assert!(names.insert(ids[5]));
        assert_eq!(names.iter_unordered().collect::<Vec<_>>(), [ids[5]]);
    }

    #[test]
    fn aliased_name_sets_trim_the_canonical_last_word() {
        let low = NameId::from_usize(2);
        let high = NameId::from_usize(2048);
        let aliases: std::rc::Rc<[(NameId, NameId)]> = std::rc::Rc::from([(low, high)]);
        let mut names = NameSet::from_iter([low]).with_aliases(Some(&aliases));
        assert!(names.contains(low));
        assert!(names.contains(high));
        assert_eq!(names.words.len(), 33);
        assert!(names.remove(low));
        assert!(names.is_empty());
        assert!(!names.remove(high));
        assert!(names.insert(high));
        assert!(names.remove(low));
        assert!(names.is_empty());

        let aliases: std::rc::Rc<[(NameId, NameId)]> = std::rc::Rc::from([(high, low)]);
        let mut names = NameSet::from_iter([high]).with_aliases(Some(&aliases));
        assert_eq!(names.words.len(), 1);
        assert!(names.remove(high));
        assert!(names.is_empty());
    }

    #[test]
    fn indexed_yields_match_the_exact_scope_walk_for_all_target_versions() {
        #[derive(Default)]
        struct Nodes<'ast> {
            functions: Vec<&'ast StmtFunctionDef>,
            yield_offsets: Vec<TextSize>,
        }

        impl<'ast> Visitor<'ast> for Nodes<'ast> {
            fn visit_stmt(&mut self, statement: &'ast Stmt) {
                if let Stmt::FunctionDef(function) = statement {
                    self.functions.push(function);
                }
                walk_stmt(self, statement);
            }

            fn visit_expr(&mut self, expression: &'ast Expr) {
                if crate::stack_growth_required() {
                    return crate::grow_stack(|| self.visit_expr(expression));
                }

                if matches!(expression, Expr::Yield(_) | Expr::YieldFrom(_)) {
                    self.yield_offsets.push(expression.start());
                }
                walk_expr(self, expression);
            }
        }

        let source = r"
def plain(value):
    return value

def nested_only():
    def nested_generator():
        yield 1
    return nested_generator

async def async_plain():
    await call()

def header_only():
    @(yield decorator)
    def child_header(value=(yield default)):
        pass

def annotated_only():
    def child_annotation(value: (yield annotation)):
        pass

def lambda_only():
    return lambda: (yield nested)

def lambda_defaults():
    return lambda value=(yield default): value

def comprehension_nested():
    return [(lambda: (yield item))() for item in source]

def comprehension_input():
    return [item for item in (yield values)]

def class_only():
    class Body:
        def class_generator(self):
            yield from items

def class_header():
    @(yield decorator)
    class Header((yield base)):
        pass

def out_of_order():
    (yield items)[(yield key)] = (yield value)

async def async_generator():
    yield 1

def trailing():
    pass
";
        let parsed = parse_module(source).unwrap();
        let mut nodes = Nodes::default();
        nodes.visit_body(parsed.suite());
        assert!(
            nodes.yield_offsets.windows(2).any(|pair| pair[0] > pair[1]),
            "the independent walker should exercise evaluation-order offsets"
        );
        nodes.yield_offsets.sort_unstable();
        nodes.yield_offsets.dedup();

        let expected = FxHashMap::from_iter([
            ("plain", (false, false, false)),
            ("nested_only", (true, false, false)),
            ("nested_generator", (true, true, true)),
            ("async_plain", (false, false, false)),
            ("header_only", (true, true, true)),
            ("child_header", (false, false, false)),
            ("annotated_only", (true, false, true)),
            ("child_annotation", (false, false, false)),
            ("lambda_only", (true, false, false)),
            ("lambda_defaults", (true, true, true)),
            ("comprehension_nested", (true, false, false)),
            ("comprehension_input", (true, true, true)),
            ("class_only", (true, false, false)),
            ("class_generator", (true, true, true)),
            ("class_header", (true, true, true)),
            ("out_of_order", (true, true, true)),
            ("async_generator", (true, true, true)),
            ("trailing", (false, false, false)),
        ]);
        assert_eq!(nodes.functions.len(), expected.len());

        for version in [
            PythonVersion::Py312,
            PythonVersion::Py313,
            PythonVersion::Py314,
            PythonVersion::Py315,
        ] {
            let scopes = ScopeArena::analyze_with_python_version(parsed.suite(), version);
            let plan = scopes.module();
            assert_eq!(plan.yield_offsets, nodes.yield_offsets, "{version:?}");
            assert!(!plan.may_contain_yield(&[]), "{version:?}");
            for function in &nodes.functions {
                let name = function.name.as_str();
                let (indexed, deferred, eager) = expected[name];
                assert_eq!(plan.may_contain_yield(&function.body), indexed, "{name}");
                for eager_annotations in [false, true] {
                    let exact = function_body_contains_yield(&function.body, eager_annotations);
                    let guarded = plan.may_contain_yield(&function.body)
                        && function_body_contains_yield(&function.body, eager_annotations);
                    assert_eq!(exact, if eager_annotations { eager } else { deferred });
                    assert_eq!(guarded, exact, "{version:?}: {name}");
                }
            }

            let plain = parse_module("def only():\n    return 1\n").unwrap();
            let plain_scope = ScopeArena::analyze_with_python_version(plain.suite(), version);
            assert!(plain_scope.module().yield_offsets.is_empty());
            assert!(!plain_scope.module().may_contain_yield(plain.suite()));
        }
    }

    #[test]
    fn optimized_yield_index_matches_the_full_scope_walk() {
        struct ResetGeneric(bool);

        impl Drop for ResetGeneric {
            fn drop(&mut self) {
                super::FORCE_GENERIC_SUSPENSION_SEARCH.set(self.0);
            }
        }

        let sources = [
            "\"\"\"module docstring\"\"\"\ndef plain(value):\n    return value\n",
            "def plain(value):\n    assert value\n    return value\n",
            "def erased():\n    assert (yield 1)\n",
            "def erased_from(values):\n    assert (yield from values)\n",
            "def outer():\n    assert ready\n    def inner():\n        yield 1\n    return inner\n",
            "def header():\n    assert ready\n    @(yield decorator)\n    def child(value=(yield default)):\n        pass\n",
            "assert ready\ndef outer():\n    @(yield decorator)\n    def child():\n        pass\n",
            "assert ready\ndef outer():\n    @(yield decorator)\n    class Child:\n        pass\n",
            "def annotation():\n    assert ready\n    def child(value: (yield annotation)):\n        pass\n",
            "def lambda_body():\n    assert ready\n    return lambda: (yield 1)\n",
            "def lambda_default():\n    assert (lambda value=(yield 1): value)\n",
            "async def asynchronous():\n    assert (yield 1)\n",
            "def legacy_coroutine():\n    assert await task()\n",
            "def legacy_comprehension(values):\n    assert [value async for value in values]\n",
        ];
        for python_version in [
            PythonVersion::Py312,
            PythonVersion::Py313,
            PythonVersion::Py314,
            PythonVersion::Py315,
        ] {
            for optimization_level in [
                crate::OptimizationLevel::Zero,
                crate::OptimizationLevel::One,
                crate::OptimizationLevel::Two,
            ] {
                let options = crate::CompileOptions {
                    python_version,
                    optimization_level,
                    ..crate::CompileOptions::default()
                };
                for source in sources {
                    let fast = crate::compile_with_options(source, "yield_index.py", &options);
                    let generic = {
                        let _reset =
                            ResetGeneric(super::FORCE_GENERIC_SUSPENSION_SEARCH.replace(true));
                        crate::compile_with_options(source, "yield_index.py", &options)
                    };
                    match (fast, generic) {
                        (Ok(fast), Ok(generic)) => {
                            assert_eq!(
                                fast.marshal(),
                                generic.marshal(),
                                "{python_version:?} {optimization_level:?}: {source}"
                            );
                        }
                        (Err(fast), Err(generic)) => {
                            assert_eq!(
                                format!("{fast:?}"),
                                format!("{generic:?}"),
                                "{python_version:?} {optimization_level:?}: {source}"
                            );
                        }
                        _ => panic!(
                            "indexed and generic compilation disagree: {python_version:?} {optimization_level:?}: {source}"
                        ),
                    }
                }
            }
        }
    }

    #[test]
    fn resolved_requirements_reuse_globals_without_losing_captures_or_protected_locals() {
        let mut names = NameInterner::seeded();
        let [
            capture_z,
            capture_a,
            local,
            alias,
            shadow_local,
            shadow_alias,
            global,
            already_global,
            explicit_only,
            untouched,
        ] = [
            "z_capture",
            "a_capture",
            "local",
            "alias",
            "shadow_local",
            "shadow_alias",
            "global",
            "already_global",
            "explicit_only",
            "untouched",
        ]
        .map(|name| names.intern(name));

        for explicit in [false, true] {
            for capture_conflicts in [false, true] {
                let mut plan = FunctionPlan {
                    locals: vec![local, shadow_local],
                    local_aliases: vec![(alias, local), (shadow_alias, shadow_local)],
                    lexical_bindings: FxHashSet::from_iter([local, shadow_local]),
                    deferred_comprehension_globals: vec![(shadow_alias, shadow_local, false)],
                    type_parameter_names: FxHashSet::from_iter([untouched]),
                    comprehension_shadowed_targets: FxHashSet::from_iter([
                        shadow_local,
                        shadow_alias,
                    ]),
                    required: FxHashSet::from_iter([
                        capture_z,
                        capture_a,
                        local,
                        alias,
                        shadow_local,
                        shadow_alias,
                        global,
                        already_global,
                    ]),
                    globals: if explicit {
                        FxHashSet::from_iter([already_global, explicit_only])
                    } else {
                        FxHashSet::default()
                    },
                    ..FunctionPlan::default()
                };
                for name in [
                    capture_z,
                    local,
                    alias,
                    shadow_local,
                    shadow_alias,
                    global,
                    already_global,
                    explicit_only,
                    untouched,
                ] {
                    plan.insert_freevar(&names, name);
                    plan.insert_annotation_freevar(&names, name);
                }
                plan.insert_annotation_freevar(&names, capture_a);
                let mut captures = FxHashSet::from_iter([capture_a, capture_z]);
                if capture_conflicts {
                    captures.extend([local, shadow_alias, global]);
                }
                let mut reference = plan.clone();
                let mut plan = plan.clone_for_lowering();
                for name in reference.required.iter().copied().collect::<Vec<_>>() {
                    if captures.contains(&name) {
                        reference.insert_freevar(&names, name);
                    } else {
                        reference.mark_global(name);
                    }
                }
                plan.resolve_required(&names, |name| captures.contains(&name));

                assert_eq!(plan.required, reference.required);
                assert_eq!(plan.globals, reference.globals);
                assert_eq!(plan.freevars, reference.freevars);
                assert_eq!(plan.annotation_freevars, reference.annotation_freevars);

                if !capture_conflicts {
                    assert_eq!(
                        plan.required,
                        FxHashSet::from_iter([capture_a, capture_z, local, alias])
                    );
                    assert!(plan.globals.is_superset(&FxHashSet::from_iter([
                        shadow_local,
                        shadow_alias,
                        global,
                        already_global,
                    ])));
                    assert_eq!(plan.globals.contains(&explicit_only), explicit);
                    assert_eq!(
                        plan.annotation_freevars,
                        [capture_a, explicit_only, untouched, capture_z]
                    );
                    assert_eq!(
                        plan.freevars,
                        [capture_a, alias, explicit_only, local, untouched, capture_z]
                    );
                }
            }
        }
    }

    #[test]
    fn empty_child_requirements_preserve_plans_and_annotation_only_inputs_are_absorbed() {
        let mut names = NameInterner::seeded();
        let [local, alias, shadow, global, free, existing] =
            ["local", "alias", "shadow", "global", "free", "existing"]
                .map(|name| names.intern(name));
        let mut full = FunctionPlan {
            locals: vec![local, shadow],
            local_aliases: vec![(alias, local)],
            globals: FxHashSet::from_iter([global]),
            required: FxHashSet::from_iter([existing]),
            comprehension_shadowed_targets: FxHashSet::from_iter([shadow]),
            ..FunctionPlan::default()
        };
        let mut lowering = full.clone().into_lowering_plan();
        full.absorb_child_requirements([], []);
        lowering.absorb_child_requirements([], []);
        assert!(full.cellvars.is_empty());
        assert!(lowering.cellvars.is_empty());
        assert_eq!(full.required, FxHashSet::from_iter([existing]));
        assert_eq!(lowering.required, full.required);

        let annotations = [local, alias, shadow, global, free];
        full.absorb_child_requirements([], annotations);
        lowering.absorb_child_requirements([], annotations);
        assert_eq!(full.cellvars, FxHashSet::from_iter([local, alias]));
        assert_eq!(
            full.required,
            FxHashSet::from_iter([existing, free, shadow])
        );
        assert_eq!(
            lowering.cellvars,
            FxHashSet::from_iter([local, alias, shadow])
        );
        assert_eq!(lowering.required, FxHashSet::from_iter([existing, free]));
    }

    #[test]
    fn eager_annotations_use_parent_locals_except_in_generic_scopes() {
        for generic in [false, true] {
            let type_params = if generic { "[T]" } else { "" };
            let source = format!(
                "def outer(annotation):\n    def inner{type_params}(value: annotation):\n        pass\n    return inner\n"
            );
            let parsed = parse_module(&source).unwrap();
            for version in [
                PythonVersion::Py312,
                PythonVersion::Py313,
                PythonVersion::Py314,
                PythonVersion::Py315,
            ] {
                let arena = ScopeArena::analyze_with_python_version(parsed.suite(), version);
                let annotation = arena.names.get("annotation").unwrap();
                let outer = arena.function(ScopeId::from_usize(1)).unwrap();
                assert_eq!(
                    outer.cellvars.contains(&annotation),
                    generic || matches!(version, PythonVersion::Py314 | PythonVersion::Py315),
                    "{version:?}, generic={generic}"
                );
            }
        }
    }

    #[test]
    fn eager_class_annotations_do_not_request_deferred_cells() {
        let parsed = parse_module("class C:\n    if condition:\n        value: int\n    def method(self, argument: value):\n        pass\n").unwrap();
        for version in [
            PythonVersion::Py312,
            PythonVersion::Py313,
            PythonVersion::Py314,
            PythonVersion::Py315,
        ] {
            let arena = ScopeArena::analyze_with_python_version(parsed.suite(), version);
            let class = arena.class(ScopeId::from_usize(1)).unwrap();
            let deferred = matches!(version, PythonVersion::Py314 | PythonVersion::Py315);
            assert_eq!(class.needs_classdict, deferred, "{version:?}");
            assert_eq!(class.has_conditional_annotations, deferred, "{version:?}");
        }
    }

    #[test]
    fn nonsimple_class_annotations_keep_native_scope_cells() {
        for (body, conditional) in [
            ("    object.attribute: int = 0\n", false),
            ("    object[index]: int\n", false),
            ("    (name): int = 0\n", false),
            ("    if condition:\n        object.attribute: int\n", true),
            ("    if False:\n        object[index]: int = 0\n", true),
        ] {
            for future in [false, true] {
                let source = format!(
                    "{}class C:\n{body}",
                    if future {
                        "from __future__ import annotations\n"
                    } else {
                        ""
                    }
                );
                let parsed = parse_module(&source).unwrap();
                for version in [
                    PythonVersion::Py312,
                    PythonVersion::Py313,
                    PythonVersion::Py314,
                    PythonVersion::Py315,
                ] {
                    let arena = ScopeArena::analyze_with_python_version(parsed.suite(), version);
                    let class = arena.class(ScopeId::from_usize(1)).unwrap();
                    let deferred = matches!(version, PythonVersion::Py314 | PythonVersion::Py315);
                    assert_eq!(
                        class.needs_classdict,
                        deferred && !future,
                        "{source}, {version:?}"
                    );
                    assert_eq!(
                        class.has_conditional_annotations,
                        deferred && conditional,
                        "{source}, {version:?}"
                    );
                }
            }
        }
    }

    #[test]
    fn nested_nonsimple_annotations_do_not_mark_the_enclosing_class() {
        let parsed = parse_module(
            "class Outer:\n    if condition:\n        class Inner:\n            object.attribute: int = 0\n",
        )
        .unwrap();
        for version in [
            PythonVersion::Py312,
            PythonVersion::Py313,
            PythonVersion::Py314,
            PythonVersion::Py315,
        ] {
            let arena = ScopeArena::analyze_with_python_version(parsed.suite(), version);
            let class = arena.class(ScopeId::from_usize(1)).unwrap();
            assert!(!class.needs_classdict);
            assert!(!class.has_conditional_annotations);
        }
    }

    #[test]
    fn annotation_local_claims_match_ordered_private_alias_lookup() {
        use ruff_python_ast::name::Name;

        const SPELLINGS: &[&str] = &[
            "ordinary",
            "other",
            "__slot",
            "_C__slot",
            "_Ω__slot",
            "_C__Nested__slot",
            "__slot__",
            "_C__slot__",
            "__slot.member",
            "_C__slot.member",
            "___slot",
            "_C___slot",
            "_Other__slot",
            "_C__",
            "__",
        ];

        for private_name in [
            None,
            Some("C"),
            Some("_C"),
            Some("__"),
            Some("Ω"),
            Some("C__Nested"),
        ] {
            for annotations in
                std::iter::once(SPELLINGS).chain(SPELLINGS.iter().map(std::slice::from_ref))
            {
                for reverse in [false, true] {
                    let mut collector = LocalCollector {
                        names: SPELLINGS.iter().map(Name::new).collect(),
                        annotation_only: annotations.iter().map(Name::new).collect(),
                        private_name: private_name.map(str::to_owned),
                        ..LocalCollector::default()
                    };
                    let mut expected_names = collector.names.clone();
                    let mut expected_annotations = collector.annotation_only.clone();
                    let mut claimed = SPELLINGS.to_vec();
                    if reverse {
                        claimed.reverse();
                    }
                    for name in claimed {
                        let annotation = if expected_annotations.contains(name) {
                            Some(Name::new(name))
                        } else if let Some(private_name) = private_name {
                            let canonical = super::mangle_name(name, Some(private_name));
                            expected_names
                                .iter()
                                .find(|candidate| {
                                    expected_annotations.contains(*candidate)
                                        && super::mangle_name(candidate, Some(private_name))
                                            == canonical
                                })
                                .cloned()
                        } else {
                            None
                        };
                        if let Some(annotation) = annotation {
                            expected_annotations.remove(&annotation);
                            let index = expected_names
                                .iter()
                                .position(|name| *name == annotation)
                                .unwrap();
                            let annotation = expected_names.remove(index);
                            expected_names.push(annotation);
                        }

                        collector.claim_annotation_only_position(name);
                        assert_eq!(collector.names, expected_names, "{private_name:?}, {name}");
                        assert_eq!(
                            collector.annotation_only, expected_annotations,
                            "{private_name:?}, {name}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn private_local_retention_matches_complete_mangled_binding_set() {
        use ruff_python_ast::name::Name;

        const SPELLINGS: &[&str] = &[
            "ordinary",
            "__slot",
            "_C__slot",
            "_Ω__slot",
            "_C__Nested__slot",
            "__slot__",
            "_C__slot__",
            "__slot.member",
            "_C__slot.member",
        ];

        for private_name in [
            None,
            Some("C"),
            Some("_C"),
            Some("__"),
            Some("Ω"),
            Some("C__Nested"),
        ] {
            for bound_mask in 0..1_u32 << SPELLINGS.len() {
                let names: Vec<_> = SPELLINGS.iter().map(Name::new).collect();
                let candidate_bindings: FxHashMap<_, _> = names
                    .iter()
                    .enumerate()
                    .map(|(index, name)| (name.clone(), bound_mask & (1 << index) != 0))
                    .collect();
                let bound: FxHashSet<_> = names
                    .iter()
                    .filter(|name| candidate_bindings[*name])
                    .map(|name| super::mangle_name(name, private_name).into_owned())
                    .collect();
                let expected: Vec<_> = names
                    .iter()
                    .filter(|name| bound.contains(super::mangle_name(name, private_name).as_ref()))
                    .cloned()
                    .collect();
                let mut collector = LocalCollector {
                    names,
                    candidate_bindings: Some(candidate_bindings),
                    private_name: private_name.map(str::to_owned),
                    ..LocalCollector::default()
                };

                collector.retain_bindings();

                assert_eq!(collector.names, expected, "{private_name:?}, {bound_mask}");
            }
        }
    }

    #[test]
    fn legacy_local_annotations_preserve_symbol_captures_without_runtime_slots() {
        for version in [PythonVersion::Py312, PythonVersion::Py313] {
            for future in [false, true] {
                let source = format!(
                    "{}def outer(annotation):\n    def inner():\n        local: annotation\n    return inner\n",
                    if future {
                        "from __future__ import annotations\n"
                    } else {
                        ""
                    }
                );
                let parsed = parse_module(&source).unwrap();
                let arena = ScopeArena::analyze_with_python_version(parsed.suite(), version);
                let annotation = arena.names.get("annotation").unwrap();
                assert_eq!(
                    arena
                        .function(ScopeId::from_usize(1))
                        .unwrap()
                        .cellvars
                        .contains(&annotation),
                    !future
                );
                assert!(
                    arena
                        .function(ScopeId::from_usize(2))
                        .unwrap()
                        .locals
                        .is_empty()
                );
            }

            let parsed = parse_module(
                "def f():\n    local: (bound := int)\n    later = 1\n    return bound\n",
            )
            .unwrap();
            let arena = ScopeArena::analyze_with_python_version(parsed.suite(), version);
            let plan = arena.function(ScopeId::from_usize(1)).unwrap();
            assert_eq!(
                plan.locals
                    .iter()
                    .map(|name| arena.names.resolve(*name))
                    .collect::<Vec<_>>(),
                ["later", "bound"]
            );

            let parsed =
                parse_module("def f(values):\n    local: [(lambda: item) for item in values]\n")
                    .unwrap();
            let arena = ScopeArena::analyze_with_python_version(parsed.suite(), version);
            let plan = arena.function(ScopeId::from_usize(1)).unwrap();
            assert_eq!(
                plan.locals
                    .iter()
                    .map(|name| arena.names.resolve(*name))
                    .collect::<Vec<_>>(),
                ["values", "item"]
            );
            assert!(plan.cellvars.contains(&arena.names.get("item").unwrap()));
        }
    }

    #[test]
    fn deferred_local_annotations_propagate_only_nested_captures() {
        for version in [PythonVersion::Py314, PythonVersion::Py315] {
            for future in [false, true] {
                let source = format!(
                    "{}def outer(direct, first_iterable, captured):\n    def inner():\n        ignored: (direct, [item for item in first_iterable], [captured for item in ()], [(lambda: item) for item in ()])\n    return inner\n",
                    if future {
                        "from __future__ import annotations\n"
                    } else {
                        ""
                    },
                );
                let parsed = parse_module(&source).unwrap();
                let arena = ScopeArena::analyze_with_python_version(parsed.suite(), version);
                let outer = arena.function(ScopeId::from_usize(1)).unwrap();
                let inner = arena.function(ScopeId::from_usize(2)).unwrap();
                for name in ["direct", "first_iterable", "captured", "item"] {
                    let name_id = arena.names.get(name).unwrap();
                    assert_eq!(
                        outer.cellvars.contains(&name_id),
                        !future && name == "captured",
                        "outer: {version:?}, future={future}, {name}",
                    );
                    assert_eq!(
                        inner.required.contains(&name_id),
                        !future && name == "captured",
                        "inner: {version:?}, future={future}, {name}",
                    );
                }
                assert!(inner.locals.is_empty());
            }
        }
    }

    #[test]
    fn annotation_setup_includes_nonsimple_targets_and_stays_in_own_scope() {
        for (source, expected) in [
            ("if condition:\n    object.attribute: int\n", true),
            ("def inner():\n    value: int\n", false),
            ("class Inner:\n    value: int\n", false),
        ] {
            let parsed = parse_module(source).unwrap();
            assert_eq!(has_annotations(parsed.suite()), expected);
        }
    }

    #[test]
    fn scope_seed_names_are_unique() {
        assert_eq!(
            SCOPE_SEED_NAMES.into_iter().collect::<FxHashSet<_>>().len(),
            SCOPE_SEED_NAMES.len()
        );
    }

    #[test]
    fn definitely_evaluated_references_collects_loads_and_super() {
        let cases: &[(&str, &[&str])] = &[
            ("(target := call(value, value))", &["call", "value"]),
            ("left < right", &["left", "right"]),
            ("super()", &["super", "__class__"]),
            ("(__class__, super, __class__)", &["__class__", "super"]),
            ("object.super", &["object"]),
            ("[first, *rest]", &["first", "rest"]),
            ("42", &[]),
        ];

        for (source, expected) in cases {
            let parsed = parse_module(source).unwrap();
            let [ruff_python_ast::Stmt::Expr(statement)] = parsed.suite().as_slice() else {
                panic!("expected one expression statement");
            };
            assert_eq!(
                definitely_evaluated_references(&statement.value)
                    .map(|names| names.into_iter().collect::<FxHashSet<_>>()),
                Some(expected.iter().copied().collect()),
                "source:\n{source}"
            );
        }
    }

    #[test]
    fn definitely_evaluated_references_deduplicate_across_inline_and_spilled_storage() {
        let source = "root(first, second, first, third, fourth, fifth, second, super, __class__)";
        let parsed = parse_module(source).unwrap();
        let [ruff_python_ast::Stmt::Expr(statement)] = parsed.suite().as_slice() else {
            panic!("expected one expression statement");
        };
        let names = definitely_evaluated_references(&statement.value).unwrap();
        assert_eq!(
            names.as_slice(),
            [
                "__class__",
                "fifth",
                "first",
                "fourth",
                "root",
                "second",
                "super",
                "third"
            ]
        );

        let conditional =
            parse_module("root(first, second, third, fourth, fifth, left and right)").unwrap();
        let [ruff_python_ast::Stmt::Expr(statement)] = conditional.suite().as_slice() else {
            panic!("expected one expression statement");
        };
        assert!(definitely_evaluated_references(&statement.value).is_none());
    }

    #[test]
    fn definitely_evaluated_references_discards_loads_before_conditional_evaluation() {
        let cases = [
            "before(first, left and right, after)",
            "before(first, left if condition else right, after)",
            "before(first, lambda item=default: item, after)",
            "before(first, (item for item in values), after)",
            "before(first, [item for item in values], after)",
            "before(first, {item for item in values}, after)",
            "before(first, {item: value for item in values}, after)",
            "before(first, left < middle < right, after)",
        ];

        for source in cases {
            let parsed = parse_module(source).unwrap();
            let [ruff_python_ast::Stmt::Expr(statement)] = parsed.suite().as_slice() else {
                panic!("expected one expression statement");
            };
            assert_eq!(
                definitely_evaluated_references(&statement.value),
                None,
                "source:\n{source}"
            );
        }
    }

    #[test]
    fn scope_visitors_keep_only_attribute_bases_and_visit_interpolated_values() {
        let source = r"
def function():
    result = receiver.first.second
    other = factory(argument).third.fourth
    assigned.inner.final = before
    del deleted.inner.final
    values = [target.attr.chain for target in iterable.attr.chain if guard.attr.chain]
    callback = lambda bound=default.attr.chain: skipped.attr.chain
    ('plain' 'literal', b'bytes', 10, True, None, ...)
    return f'{formatted.inner.last} {super().method.attribute}'
";
        let parsed = parse_module(source).unwrap();
        let [Stmt::FunctionDef(function)] = parsed.suite().as_slice() else {
            panic!("expected one function");
        };
        let expected = [
            "receiver",
            "factory",
            "argument",
            "assigned",
            "before",
            "deleted",
            "target",
            "iterable",
            "guard",
            "default",
            "formatted",
            "super",
            "__class__",
        ];
        let owned = || {
            expected
                .into_iter()
                .map(str::to_owned)
                .collect::<FxHashSet<_>>()
        };

        let facts = super::ScopeBodyFacts::for_function(&function.body);
        assert_eq!(facts.references, owned());
        assert_eq!(
            facts.nested_lambda_requirements,
            std::collections::BTreeSet::from(["skipped".to_string()])
        );

        let mut references = super::ReferenceCollector::default();
        references.visit_body(&function.body);
        assert_eq!(references.references, owned());

        let mut locals = LocalCollector {
            candidate_bindings: Some(FxHashMap::default()),
            module_references_super: Some(false),
            ..LocalCollector::default()
        };
        locals.collect_suite(&function.body);
        assert_eq!(locals.module_references_super, Some(true));
        let candidates = locals.candidate_bindings.as_ref().unwrap();
        for name in expected.into_iter().filter(|name| *name != "__class__") {
            assert!(candidates.contains_key(name), "missing {name}");
        }
        for omitted in ["first", "inner", "chain", "skipped", "method", "attribute"] {
            assert!(!candidates.contains_key(omitted), "unexpected {omitted}");
        }
    }

    #[test]
    fn scope_assertion_facts_match_local_collection_boundaries() {
        for (source, expected) in [
            ("value = [item for item in values]\n", false),
            ("assert check\n", true),
            ("if condition:\n    assert check\n", true),
            ("for value in values:\n    assert value\n", true),
            (
                "while condition:\n    pass\nelse:\n    assert check\n",
                true,
            ),
            (
                "try:\n    operation()\nexcept Error:\n    assert check\n",
                true,
            ),
            ("try:\n    pass\nfinally:\n    assert check\n", true),
            ("match subject:\n    case _:\n        assert check\n", true),
            ("def nested():\n    assert check\n", false),
            ("class Nested:\n    assert check\n", false),
            ("return result\nassert check\n", true),
        ] {
            let parsed = parse_module(source).unwrap();
            let facts = super::ScopeBodyFacts::for_function(parsed.suite());
            let mut locals = LocalCollector {
                elide_assertions: true,
                ..LocalCollector::default()
            };
            locals.collect_suite(parsed.suite());
            assert_eq!(facts.has_assertions, expected, "{source}");
            assert_eq!(facts.has_assertions, locals.elided_assertion, "{source}");
        }
    }

    #[test]
    fn nested_first_iterables_reserve_each_scope_once() {
        let collector = LocalCollector {
            nonlocals: FxHashSet::from_iter(["unused".to_string()]),
            ..LocalCollector::default()
        };
        let mut source = "values".to_string();
        let mut expected = Vec::new();
        for depth in 0..32 {
            source = format!("[item_{depth} for item_{depth} in {source}]");
            expected.push(format!("item_{depth}"));
            let parsed = parse_module(&source).unwrap();
            let [ruff_python_ast::Stmt::Expr(statement)] = parsed.suite().as_slice() else {
                panic!("expected one expression statement");
            };
            let mut names = Vec::new();
            collector.collect_nested_comprehension_saves(&statement.value, &mut names);
            // Check the admissions before deduplication: duplicate visits multiply with depth.
            assert_eq!(names, expected, "first-iterable depth {}", depth + 1);
        }
    }

    #[test]
    fn copied_finally_locals_follow_unwind_order_and_loop_boundaries() {
        let cases: &[(&str, &[&str])] = &[
            (
                "try:\n    if flag:\n        return flag\n    later = flag\nfinally:\n    cleanup = flag\n",
                &["cleanup", "later"],
            ),
            (
                "try:\n    for item in items:\n        if flag:\n            break\n    later = flag\nfinally:\n    cleanup = flag\n",
                &["item", "later", "cleanup"],
            ),
            (
                "try:\n    for item in items:\n        if flag:\n            continue\n    later = flag\nfinally:\n    cleanup = flag\n",
                &["item", "later", "cleanup"],
            ),
            (
                "try:\n    for item in items:\n        if flag:\n            return flag\n    later = flag\nfinally:\n    cleanup = flag\n",
                &["item", "cleanup", "later"],
            ),
            (
                "for item in items:\n    try:\n        if flag:\n            break\n        later = flag\n    finally:\n        cleanup = flag\n",
                &["item", "cleanup", "later"],
            ),
            (
                "for item in items:\n    try:\n        if flag:\n            continue\n        later = flag\n    finally:\n        cleanup = flag\n",
                &["item", "cleanup", "later"],
            ),
            (
                "try:\n    try:\n        if flag:\n            return flag\n        later = flag\n    finally:\n        inner = flag\n        return inner\nfinally:\n    outer = flag\n",
                &["inner", "outer", "later"],
            ),
        ];
        for (source, expected) in cases {
            let parsed = parse_module(source).unwrap();
            let mut collector = LocalCollector::default();
            collector.collect_suite(parsed.suite());
            assert_eq!(collector.names, *expected, "source:\n{source}");
        }
    }

    #[test]
    fn seeded_name_interner_preserves_ids_order_and_static_storage() {
        let mut names = NameInterner::seeded();

        for (index, name) in SCOPE_SEED_NAMES.into_iter().enumerate() {
            let id = NameId::from_usize(index);
            assert_eq!(names.get(name), Some(id));
            assert_eq!(names.intern_name(&Name::new(name), name), id);
            assert_eq!(names.resolve(id), name);
            assert_eq!(names.clone_name(id), name);
            assert_eq!(names.seed_names[index], name);
        }
        assert!(names.names.is_empty());

        assert_eq!(names.intern("__user_name__"), NameId::from_u32(26));
        assert_eq!(names.names[0], "__user_name__");
        assert_eq!(names.intern("super"), NameId::from_u32(25));
        assert_eq!(names.intern_owned("super".to_owned()), NameId::from_u32(25));
    }

    #[test]
    fn interned_ast_names_retain_heap_storage() {
        let spelling = Name::new("identifier_that_does_not_fit_inline");
        for mut names in [NameInterner::seeded(), NameInterner::default()] {
            let id = names.intern_name(&spelling, spelling.as_str());
            assert_eq!(names.resolve(id).as_ptr(), spelling.as_str().as_ptr());
            assert_eq!(names.intern(spelling.as_str()), id);
            assert_eq!(
                names.intern_name(&Name::new(spelling.as_str()), spelling.as_str()),
                id
            );
            assert_eq!(names.names.len(), 1);
        }
    }

    #[test]
    fn cloned_names_retain_interned_heap_storage() {
        for mut names in [NameInterner::seeded(), NameInterner::default()] {
            let spelling = "identifier_that_does_not_fit_inline";
            let id = names.intern(spelling);
            let cloned = names.clone_name(id);
            assert_eq!(cloned.as_str(), spelling);
            assert_eq!(cloned.as_str().as_ptr(), names.resolve(id).as_ptr());
            drop(names);
            assert_eq!(cloned.as_str(), spelling);
        }
    }

    #[test]
    fn seed_candidates_keep_exact_ids_with_dynamic_and_unseeded_interners() {
        let mut seeded = NameInterner::seeded();
        let mut unseeded = NameInterner::default();
        let dynamic = [
            "ordinary",
            ".unknown",
            "\0unknown",
            "__unknown__",
            "_single",
            "former",
            "joins",
            "supers",
            "formatting",
            "__class_",
        ];
        for (index, spelling) in dynamic.into_iter().enumerate() {
            assert_eq!(
                seeded.intern(spelling),
                NameId::from_usize(SCOPE_SEED_NAMES.len() + index),
            );
        }
        for (index, spelling) in SCOPE_SEED_NAMES.into_iter().enumerate() {
            let id = NameId::from_usize(index);
            assert_eq!(seeded.get(spelling), Some(id));
            assert_eq!(seeded.intern(spelling), id);
            assert_eq!(seeded.intern_owned(spelling.to_owned()), id);
            assert_eq!(unseeded.get(spelling), None);
            assert_eq!(unseeded.intern(spelling), id);
            assert_eq!(unseeded.get(spelling), Some(id));
        }
        for (index, spelling) in dynamic.into_iter().enumerate() {
            let id = NameId::from_usize(SCOPE_SEED_NAMES.len() + index);
            assert_eq!(seeded.get(spelling), Some(id));
            assert_eq!(seeded.resolve(id), spelling);
        }
    }

    #[test]
    fn short_name_cache_preserves_lengths_unicode_and_direct_map_collisions() {
        use super::{NAME_CACHE_SIZE, ShortNameKey};

        let mut names = NameInterner::default();
        let spellings = [
            "x",
            "x\0",
            "x\0\0",
            "abcd",
            "abcd\0",
            "abcde\0",
            "abcdef\0",
            "abcdefg\0",
            "abcdefghx",
            "名",
            "名é",
            "😀x",
        ];
        for (index, spelling) in spellings.iter().enumerate() {
            assert_eq!(names.get(spelling), None);
            assert_eq!(names.intern(spelling), NameId::from_usize(index));
        }
        for (index, spelling) in spellings.iter().enumerate().rev() {
            let id = NameId::from_usize(index);
            assert_eq!(names.get(spelling), Some(id));
            assert_eq!(names.intern_owned((*spelling).to_owned()), id);
            assert_eq!(names.resolve(id), *spelling);
        }

        let mut slots = vec![None; NAME_CACHE_SIZE];
        let (first, second) = (0..=NAME_CACHE_SIZE)
            .find_map(|index| {
                let spelling = format!("v{index}");
                let slot = ShortNameKey::new(&spelling).unwrap().slot();
                slots[slot]
                    .replace(spelling.clone())
                    .map(|earlier| (earlier, spelling))
            })
            .expect("more spellings than cache slots must collide");
        let first_id = names.intern(&first);
        let second_id = names.intern(&second);
        for _ in 0..4 {
            assert_eq!(names.get(&first), Some(first_id));
            assert_eq!(names.get(&second), Some(second_id));
        }
        assert_ne!(first_id, second_id);
    }

    #[test]
    fn short_seed_ids_survive_collisions_without_allocating_the_cache() {
        use super::ShortNameKey;

        let mut names = NameInterner::seeded();
        let seed = "super";
        let seed_id = names.get(seed).unwrap();
        let seed_key = ShortNameKey::new(seed).unwrap();
        assert!(names.short_names.0.get().is_none());

        let colliding = (0..1000)
            .map(|index| format!("v{index}"))
            .find(|spelling| ShortNameKey::new(spelling).unwrap().slot() == seed_key.slot())
            .expect("a dynamic name should share the seed's cache slot");
        let dynamic_id = names.intern(&colliding);
        assert_ne!(seed_id, dynamic_id);
        for _ in 0..4 {
            assert_eq!(names.get(seed), Some(seed_id));
            assert_eq!(names.get(&colliding), Some(dynamic_id));
        }

        let mut unseeded = NameInterner::default();
        assert_eq!(unseeded.get(seed), None);
        assert_eq!(unseeded.intern(&colliding), NameId::from_usize(0));
        assert_eq!(unseeded.intern(seed), NameId::from_usize(1));
    }

    #[test]
    fn medium_name_cache_allocates_only_after_a_successful_medium_lookup() {
        let mut names = NameInterner::seeded();
        assert!(names.short_names.0.get().is_none());
        assert_eq!(names.get("not_present"), None);
        assert!(names.short_names.0.get().is_none());
        assert_eq!(
            names.get("__annotations__"),
            Some(NameInterner::seed_id("__annotations__").unwrap())
        );
        assert!(names.short_names.0.get().is_none());
        let dynamic = names.intern("new_medium_name");
        assert_eq!(names.get("new_medium_name"), Some(dynamic));
        assert!(names.short_names.0.get().unwrap().medium.get().is_some());
    }

    #[test]
    fn medium_name_cache_keeps_full_spellings_and_recovers_from_collisions() {
        use super::MediumNameKey;

        let mut names = NameInterner::seeded();
        let samples = [
            "abcdefghi",
            "abcdefghi\0",
            "abcdefghijklmnop",
            "abcdefghijklmnop\0",
            "abcdefgh11111111ijklmnop",
            "abcdefgh22222222ijklmnop",
            "abcdefgh11111111ijklmnox",
            "xbcdefgh11111111ijklmnop",
            "abcdefgh11111111ijklmnopx",
            "識別子の名前甲乙",
            "識別子の名前乙甲",
        ];
        for (index, spelling) in samples.into_iter().enumerate() {
            assert_eq!(names.get(spelling), None);
            let id = names.intern(spelling);
            assert_eq!(id, NameId::from_usize(SCOPE_SEED_NAMES.len() + index));
        }
        for (index, spelling) in samples.into_iter().enumerate().rev() {
            let id = NameId::from_usize(SCOPE_SEED_NAMES.len() + index);
            assert_eq!(names.get(spelling), Some(id));
            assert_eq!(names.resolve(id), spelling);
            assert_eq!(MediumNameKey::new(spelling).is_some(), spelling.len() <= 16);
        }
        let seed = "__annotations__";
        let seed_id = names.get(seed).unwrap();
        let seed_key = MediumNameKey::new(seed).unwrap();
        assert_eq!(names.short_names.get_medium(seed_key), Some(seed_id));
        let colliding = (0..1_000)
            .map(|index| format!("dynamic_{index:04}"))
            .find(|spelling| MediumNameKey::new(spelling).unwrap().slot() == seed_key.slot())
            .expect("a dynamic name should share the seed cache slot");
        let dynamic_id = names.intern(&colliding);
        assert_ne!(seed_id, dynamic_id);
        for _ in 0..4 {
            assert_eq!(names.get(seed), Some(seed_id));
            assert_eq!(names.get(&colliding), Some(dynamic_id));
        }
        let mut unseeded = NameInterner::default();
        assert_eq!(unseeded.get(seed), None);
        assert_eq!(unseeded.intern(seed), NameId::from_u32(0));
    }

    #[test]
    fn name_interner_preserves_ids_through_growth_and_repeated_lookup() {
        let mut names = NameInterner::seeded();
        for index in 0..2048 {
            let spelling = format!("name_{index}_名");
            let expected = NameId::from_usize(SCOPE_SEED_NAMES.len() + index);
            assert_eq!(names.intern_owned(spelling), expected);
        }
        for index in (0..2048).rev() {
            let spelling = format!("name_{index}_名");
            let expected = NameId::from_usize(SCOPE_SEED_NAMES.len() + index);
            assert_eq!(names.get(&spelling), Some(expected));
            assert_eq!(names.intern(&spelling), expected);
            assert_eq!(names.resolve(expected), spelling);
        }
        for (index, seed) in SCOPE_SEED_NAMES.iter().enumerate() {
            assert_eq!(names.intern(seed), NameId::from_usize(index));
            assert_eq!(names.seed_names[index], *seed);
        }
        assert_eq!(names.len(), SCOPE_SEED_NAMES.len() + 2048);
        assert_eq!(names.get("missing"), None);
    }

    #[test]
    fn default_name_interner_starts_with_zero_id() {
        let mut names = NameInterner::default();

        assert_eq!(names.get("super"), None);
        assert_eq!(names.intern("dynamic"), NameId::from_u32(0));
        assert_eq!(names.names[0], "dynamic");
    }

    #[test]
    fn module_name_walk_records_scope_definitions_in_preorder() {
        let source = "if condition:\n    def outer(value):\n        class Inner:\n            def method(self):\n                return value\nelse:\n    class Sibling:\n        def other(self):\n            return 1\n";
        let parsed = parse_module(source).unwrap();
        let mut names = NameInterner::seeded();

        let (_, definitions, requires_module_bindings) =
            ModuleNameCollector::collect(&mut names, parsed.suite(), false);

        assert!(!requires_module_bindings);
        assert_eq!(
            definitions
                .iter()
                .map(|input| {
                    let (name, flat) = match &input.definition {
                        ScopeDefinition::Function(definition, flat, _) => {
                            (definition.name.as_str(), flat.is_some())
                        }
                        ScopeDefinition::Class(definition, _) => (definition.name.as_str(), false),
                    };
                    (input.parent, name, flat)
                })
                .collect::<Vec<_>>(),
            [
                (ScopeId::MODULE, "outer", false),
                (ScopeId::from_usize(1), "Inner", false),
                (ScopeId::from_usize(2), "method", true),
                (ScopeId::MODULE, "Sibling", false),
                (ScopeId::from_usize(4), "other", true),
            ]
        );

        for version in [
            PythonVersion::Py312,
            PythonVersion::Py313,
            PythonVersion::Py314,
            PythonVersion::Py315,
        ] {
            let arena = ScopeArena::analyze_with_python_version(parsed.suite(), version);
            assert_eq!(arena.nodes.len(), definitions.len() + 1);
            for (index, input) in definitions.iter().enumerate() {
                let id = ScopeId::from_usize(index + 1);
                assert_eq!(arena.nodes[id].parent, Some(input.parent));
                match input.definition {
                    ScopeDefinition::Function(..) => assert!(arena.function(id).is_some()),
                    ScopeDefinition::Class(..) => assert!(arena.class(id).is_some()),
                }
            }
            let value = arena.names.get("value").unwrap();
            assert!(
                arena
                    .function(ScopeId::from_usize(1))
                    .unwrap()
                    .cellvars
                    .contains(&value)
            );
        }
    }

    #[test]
    fn module_binding_walk_only_runs_for_module_sensitive_inputs() {
        let cases = [
            (
                "def nested(values):\n    return [item for item in values]\n",
                false,
            ),
            ("[item for item in values]\n", true),
            (
                "@decorate([item for item in values])\ndef header():\n    pass\n",
                true,
            ),
            (
                "def header(value=[item for item in values]):\n    pass\n",
                true,
            ),
            ("(lambda value=[item for item in values]: value)()\n", true),
            ("def nested():\n    return super()\n", true),
        ];

        for (source, expected) in cases {
            let parsed = parse_module(source).unwrap();
            let mut names = NameInterner::seeded();
            let (_, _, requires_module_bindings) =
                ModuleNameCollector::collect(&mut names, parsed.suite(), false);
            assert_eq!(requires_module_bindings, expected, "source:\n{source}");
        }
    }

    #[test]
    fn flat_function_inputs_preserve_first_occurrence_and_late_binding() {
        let mut inputs = FlatFunctionInputs {
            names: Vec::new(),
            name_positions: None,
            has_annotations: false,
            has_assertions: false,
            in_assertion: true,
            implicit_class_reference: false,
            complex: false,
        };

        inputs.record(NameId::from_u32(2), false);
        inputs.in_assertion = false;
        inputs.record(NameId::from_u32(1), true);
        inputs.record(NameId::from_u32(2), true);
        inputs.in_assertion = true;
        inputs.record(NameId::from_u32(1), false);

        assert_eq!(
            inputs.names,
            [
                (NameId::from_u32(2), true, true),
                (NameId::from_u32(1), true, false),
            ]
        );
        assert!(inputs.name_positions.is_none());
        assert_eq!(
            std::mem::size_of::<(NameId, bool, bool)>(),
            std::mem::size_of::<(NameId, bool)>(),
        );
    }

    #[test]
    fn flat_augmented_assignments_match_full_scope_analysis() {
        let source = "def simple():\n    early += late\n    late = 1\n    item[index] += operand\n    object.field += early\n    object = item = index = 1\nclass Example:\n    def method(self):\n        __slot += _Example__slot\n        _Example__slot = 1\n        self.__field += self[index]\n";
        let parsed = parse_module(source).unwrap();
        let fast = ScopeArena::analyze(parsed.suite());
        let mut full = ScopeArena {
            names: NameInterner::seeded(),
            ..ScopeArena::default()
        };
        let (_, mut definitions, _) =
            ModuleNameCollector::collect(&mut full.names, parsed.suite(), false);
        for input in &mut definitions {
            if let ScopeDefinition::Function(_, flat, _) = &mut input.definition {
                assert!(flat.take().is_some());
            }
        }
        full.build_scopes(definitions, false);

        for (scope, expected_locals, expected_required) in [
            (
                ScopeId::from_usize(1),
                ["early", "late", "item", "index", "object"].as_slice(),
                ["operand"].as_slice(),
            ),
            (
                ScopeId::from_usize(3),
                ["self", "_Example__slot"].as_slice(),
                ["index"].as_slice(),
            ),
        ] {
            let fast_plan = fast.function(scope).unwrap();
            let full_plan = full.function(scope).unwrap();
            assert_eq!(fast_plan.locals, full_plan.locals);
            assert_eq!(fast_plan.required, full_plan.required);
            assert_eq!(fast_plan.local_aliases, full_plan.local_aliases);
            assert_eq!(
                fast_plan
                    .locals
                    .iter()
                    .map(|name| fast.names.resolve(*name))
                    .collect::<Vec<_>>(),
                expected_locals,
            );
            assert_eq!(
                fast_plan.required,
                expected_required
                    .iter()
                    .map(|name| fast.names.get(name).unwrap())
                    .collect(),
            );
        }
        let method = fast.function(ScopeId::from_usize(3)).unwrap();
        assert_eq!(
            method.local_aliases,
            [(
                fast.names.get("__slot").unwrap(),
                fast.names.get("_Example__slot").unwrap(),
            )],
        );
    }

    #[test]
    fn flat_annotated_functions_match_full_scope_analysis_for_all_versions() {
        let body = r"
@decorate((lambda header: header)(decorator_only))
def simple(pos: Pos, /, normal: Normal = default_only, *args: Var,
           only: Only, **kwargs: Kw) -> Return:
    runtime = pos
    return runtime, body_only

class _Owner:
    def method(self, __private: _Owner__Alias, *, other: __Alias) -> list[__Return]:
        __slot = 1
        _Owner__slot = __slot
        return other, __slot

    def scopes(self, value: (lambda x: x + __captured)(outer)) -> tuple[(item for item in __items)]:
        return value, body_only

def outer():
    annotation_local = default_local = decorator_local = None
    @decorate(decorator_local)
    def nested(value: annotation_local = default_local) -> (lambda t: t + annotation_local):
        return value, body_only
    return nested

def generic[T](value: T) -> T:
    return value

def complex(value: Complex) -> Result:
    local: Declared = value
    return local

def local_order():
    early: list[AnnotationOnly] = late
    late: dict[str, int] = {}
    return early, late

def local_super(value):
    local: super | __class__ = value
    return local

class LocalOwner:
    def private(self, value):
        __slot: __Annotation = _LocalOwner__slot
        _LocalOwner__slot = value
        return __slot

def local_only():
    local: AnnotationOnly
    return local

def local_attribute(owner, value):
    owner.local: AnnotationOnly = value

def local_nested(value):
    local: (lambda: captured) = value
    return local

def local_comprehension(value):
    local: [item for item in captured] = value
    return local

def local_walrus(value):
    local: (bound := AnnotationOnly) = value
    return local

def local_value_walrus(value):
    local: AnnotationOnly = (bound := value)
    return local, bound

class _Generic[__T]:
    def typed(self, __value: __T, *, alias: _Generic__T) -> list[__T]:
        __local = __value
        _Generic__local = __local
        return alias, __local

class SuperOwner:
    def method_super(self):
        return super().method()

    def shadow_super(self, super):
        return super, __class__

    def bind_class(self):
        first = super()
        __class__ = later
        return first, __class__

    def delete_super(self):
        del super
        return super()

    def private_super(self, __private):
        _SuperOwner__private = __private
        return super(), __private

    async def async_super(self):
        return await super().method()

    def annotated_super(self: super) -> __class__:
        return super()

    def annotated_class(self):
        __class__: Type
        return super()

def outside_class(super):
    return super()

def enclosing_class():
    __class__ = captured
    def inner_super():
        return super()
    return inner_super

def conditional_assert(value):
    if value:
        assert first, detail
    second = 1
    first = 2
    return first, second

def assert_no_names():
    assert True

def assert_global() -> Result:
    assert external, detail

def assert_generator():
    assert (yield value), detail

async def assert_coroutine():
    assert await work()

def assert_binding_order():
    assert later
    earlier = 1
    later = 2
    return earlier, later

def assert_binding_first(value):
    first = value
    assert first, detail
    second = first
    return first, second

def assert_load_first():
    first = later
    assert later
    later = second = value
    return first, later, second

def assert_mixed(first):
    assert first, later
    earlier = first
    later = value
    return earlier, later

def assert_parameters(pos, /, normal, *args, only, **kwargs):
    assert pos, normal
    assert only, args
    assert kwargs
    return normal

def assert_deleted():
    del local
    assert local

def assert_walrus():
    assert (bound := value)
    return bound

def assert_walrus_after_binding(value):
    bound = value
    assert (bound := other)
    return bound

def assert_enclosing():
    captured = value
    def assert_capture():
        assert captured
    def assert_capture_with_local(value):
        local = value
        assert captured, local
        return local
    return assert_capture, assert_capture_with_local

class AssertOwner:
    def assert_private():
        assert __hidden, __class__
        assert super()

    def assert_alias_before(self):
        assert __slot
        earlier = value
        _AssertOwner__slot = other
        return earlier, __slot

    def assert_alias_after(self):
        _AssertOwner__slot = value
        assert __slot
        return _AssertOwner__slot

    def assert_canonical_before(self):
        assert _AssertOwner__slot
        earlier = value
        __slot = other
        return earlier, _AssertOwner__slot
";
        for version in [
            PythonVersion::Py312,
            PythonVersion::Py313,
            PythonVersion::Py314,
            PythonVersion::Py315,
        ] {
            for (future, optimization_level) in [false, true]
                .into_iter()
                .flat_map(|future| (0..=2).map(move |level| (future, level)))
            {
                let source = if future {
                    format!("from __future__ import annotations\n{body}")
                } else {
                    body.to_owned()
                };
                let parsed = parse_module(&source).unwrap();
                let assertion_mode = if optimization_level == 0 {
                    AssertionMode::Keep
                } else {
                    AssertionMode::Elide
                };
                let fast = ScopeArena::analyze_with_source_options(
                    parsed.suite(),
                    version,
                    &mut super::SourceAnalysis::new(version, optimization_level),
                    assertion_mode,
                );
                let deferred = matches!(version, PythonVersion::Py314 | PythonVersion::Py315);
                let mut full = ScopeArena {
                    names: NameInterner::seeded(),
                    deferred_annotations: deferred,
                    python_version: version,
                    assertion_mode,
                    ..ScopeArena::default()
                };
                let (_, mut definitions, _) = ModuleNameCollector::collect_with_source(
                    &mut full.names,
                    parsed.suite(),
                    !deferred && !future,
                    &mut super::SourceAnalysis::new(version, optimization_level),
                    true,
                );
                let functions = definitions
                    .iter_mut()
                    .enumerate()
                    .filter_map(|(index, input)| {
                        let ScopeDefinition::Function(definition, flat, _) = &mut input.definition
                        else {
                            return None;
                        };
                        let definition = *definition;
                        Some((
                            definition.name.as_str(),
                            ScopeId::from_usize(index + 1),
                            flat.take().is_some(),
                        ))
                    })
                    .collect::<Vec<_>>();
                assert_eq!(
                    functions
                        .iter()
                        .map(|&(name, _, flat)| (name, flat))
                        .collect::<Vec<_>>(),
                    [
                        ("simple", true),
                        ("method", true),
                        ("scopes", true),
                        ("outer", false),
                        ("nested", true),
                        ("generic", false),
                        ("complex", deferred || future),
                        ("local_order", deferred || future),
                        ("local_super", deferred || future),
                        ("private", deferred || future),
                        ("local_only", false),
                        ("local_attribute", false),
                        ("local_nested", false),
                        ("local_comprehension", false),
                        ("local_walrus", false),
                        ("local_value_walrus", false),
                        ("typed", true),
                        ("method_super", true),
                        ("shadow_super", true),
                        ("bind_class", true),
                        ("delete_super", true),
                        ("private_super", true),
                        ("async_super", true),
                        ("annotated_super", true),
                        ("annotated_class", false),
                        ("outside_class", true),
                        ("enclosing_class", false),
                        ("inner_super", true),
                        ("conditional_assert", true),
                        ("assert_no_names", true),
                        ("assert_global", true),
                        ("assert_generator", true),
                        ("assert_coroutine", true),
                        ("assert_binding_order", true),
                        ("assert_binding_first", true),
                        ("assert_load_first", true),
                        ("assert_mixed", true),
                        ("assert_parameters", true),
                        ("assert_deleted", true),
                        ("assert_walrus", false),
                        ("assert_walrus_after_binding", false),
                        ("assert_enclosing", false),
                        ("assert_capture", true),
                        ("assert_capture_with_local", true),
                        ("assert_private", true),
                        ("assert_alias_before", true),
                        ("assert_alias_after", true),
                        ("assert_canonical_before", true),
                    ],
                    "{version:?}, future={future}, O{optimization_level}"
                );
                full.build_scopes(definitions, future);

                for (name, id, _) in &functions {
                    let fast_plan = fast.function(*id).unwrap();
                    let full_plan = full.function(*id).unwrap();
                    let context =
                        format!("{version:?}, future={future}, O{optimization_level}, {name}");
                    assert_eq!(fast_plan.locals, full_plan.locals, "{context}");
                    assert_eq!(
                        fast_plan.local_aliases, full_plan.local_aliases,
                        "{context}"
                    );
                    assert_eq!(fast_plan.globals, full_plan.globals, "{context}");
                    assert_eq!(
                        fast_plan.lexical_bindings, full_plan.lexical_bindings,
                        "{context}"
                    );
                    assert_eq!(
                        fast_plan.annotation_references, full_plan.annotation_references,
                        "{context}"
                    );
                    assert_eq!(fast_plan.cellvars, full_plan.cellvars, "{context}");
                    assert_eq!(fast_plan.freevars, full_plan.freevars, "{context}");
                    assert_eq!(
                        fast_plan.annotation_freevars, full_plan.annotation_freevars,
                        "{context}"
                    );
                    assert_eq!(fast_plan.required, full_plan.required, "{context}");
                    assert_eq!(
                        fast_plan.inlined_comprehension_cellvars,
                        full_plan.inlined_comprehension_cellvars,
                        "{context}"
                    );
                    assert_eq!(
                        fast_plan.comprehension_shadowed_targets,
                        full_plan.comprehension_shadowed_targets,
                        "{context}"
                    );
                    assert_eq!(
                        fast_plan.type_parameter_names, full_plan.type_parameter_names,
                        "{context}"
                    );
                    // An existing flat private-alias plan can omit this unused sorting cache.
                    if !fast_plan.cellvars.is_empty() {
                        assert_eq!(
                            fast_plan.cell_sort_names, full_plan.cell_sort_names,
                            "{context}"
                        );
                    }
                }

                let plan = fast.function(functions[0].1).unwrap();
                let expected_annotations: FxHashSet<_> = if future {
                    FxHashSet::default()
                } else {
                    ["Pos", "Normal", "Var", "Only", "Kw", "Return"]
                        .map(|name| fast.names.get(name).unwrap())
                        .into_iter()
                        .collect()
                };
                assert_eq!(plan.annotation_references, expected_annotations);
                assert_eq!(
                    plan.required,
                    FxHashSet::from_iter([fast.names.get("body_only").unwrap()])
                );
                let nested = fast.function(functions[4].1).unwrap();
                assert_eq!(
                    nested
                        .annotation_references
                        .contains(&fast.names.get("annotation_local").unwrap()),
                    !future
                );
            }
        }
    }

    #[test]
    fn flat_exception_handlers_match_full_scope_analysis() {
        let source = "def handling():\n    try:\n        body = first\n        helper()\n    except (FirstError, SecondError) as first:\n        handler = first\n    except ThirdError as second:\n        later = second\n    except:\n        final = fallback\n    return body, first, handler, second, later, final\ndef star():\n    try:\n        passed = start\n    except* StarError as failure:\n        recovered = failure\n    return passed, recovered\ndef with_else():\n    try:\n        body()\n    except Error as failure:\n        handler()\n    else:\n        fallback()\ndef with_finally():\n    try:\n        body()\n    finally:\n        cleanup()\ndef shadows_super():\n    try:\n        body()\n    except Error as super:\n        pass\n";
        let parsed = parse_module(source).unwrap();
        let fast = ScopeArena::analyze(parsed.suite());
        let mut full = ScopeArena {
            names: NameInterner::seeded(),
            ..ScopeArena::default()
        };
        let (_, mut definitions, _) =
            ModuleNameCollector::collect(&mut full.names, parsed.suite(), false);
        let flat = definitions
            .iter_mut()
            .map(|input| {
                let ScopeDefinition::Function(definition, flat, _) = &mut input.definition else {
                    panic!("expected only functions");
                };
                (definition.name.as_str(), flat.take().is_some())
            })
            .collect::<Vec<_>>();
        assert_eq!(
            flat,
            [
                ("handling", true),
                ("star", true),
                ("with_else", false),
                ("with_finally", false),
                ("shadows_super", false),
            ],
        );
        full.build_scopes(definitions, false);

        for (scope, expected_locals, expected_required) in [
            (
                ScopeId::from_usize(1),
                ["first", "body", "handler", "second", "later", "final"].as_slice(),
                [
                    "helper",
                    "FirstError",
                    "SecondError",
                    "ThirdError",
                    "fallback",
                ]
                .as_slice(),
            ),
            (
                ScopeId::from_usize(2),
                ["passed", "failure", "recovered"].as_slice(),
                ["start", "StarError"].as_slice(),
            ),
        ] {
            let fast_plan = fast.function(scope).unwrap();
            let full_plan = full.function(scope).unwrap();
            assert_eq!(fast_plan.locals, full_plan.locals);
            assert_eq!(fast_plan.required, full_plan.required);
            assert_eq!(
                fast_plan
                    .locals
                    .iter()
                    .map(|name| fast.names.resolve(*name))
                    .collect::<Vec<_>>(),
                expected_locals,
            );
            assert_eq!(
                fast_plan.required,
                expected_required
                    .iter()
                    .map(|name| fast.names.get(name).unwrap())
                    .collect(),
            );
        }
    }

    #[test]
    fn indexed_flat_function_inputs_preserve_first_occurrence_and_late_binding() {
        let mut inputs = FlatFunctionInputs {
            names: Vec::new(),
            name_positions: None,
            has_annotations: false,
            has_assertions: false,
            in_assertion: false,
            implicit_class_reference: false,
            complex: false,
        };

        for name in 0..=FlatFunctionInputs::LINEAR_SEARCH_LIMIT {
            inputs.in_assertion = name % 2 == 0;
            inputs.record(NameId::from_usize(name), false);
        }
        for name in (0..=FlatFunctionInputs::LINEAR_SEARCH_LIMIT).rev() {
            inputs.in_assertion = name % 2 != 0;
            inputs.record(NameId::from_usize(name), true);
        }

        assert_eq!(
            inputs.names,
            (0..=FlatFunctionInputs::LINEAR_SEARCH_LIMIT)
                .map(|name| (NameId::from_usize(name), true, name % 2 == 0))
                .collect::<Vec<_>>()
        );
        assert!(inputs.name_positions.is_some());
    }

    #[test]
    fn complex_function_inputs_discard_and_stop_recording_names() {
        let mut inputs = FlatFunctionInputs {
            names: vec![
                (NameId::from_u32(1), false, true),
                (NameId::from_u32(2), true, false),
            ],
            name_positions: Some(FxHashMap::from_iter([
                (NameId::from_u32(1), 0),
                (NameId::from_u32(2), 1),
            ])),
            has_annotations: false,
            has_assertions: false,
            in_assertion: false,
            implicit_class_reference: false,
            complex: false,
        };

        inputs.mark_complex();
        inputs.record(NameId::from_u32(3), true);
        inputs.record(NameId::from_u32(1), true);

        assert!(inputs.complex);
        assert!(inputs.names.is_empty());
        assert!(inputs.name_positions.is_none());
    }
}

#[cfg(test)]
mod snapshots;
