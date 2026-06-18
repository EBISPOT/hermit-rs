// Ports of org.semanticweb.HermiT.tableau.{DependencySet, PermanentDependencySet,
// UnionDependencySet, DependencySetFactory}.
//
// A dependency set records the branching points on which a derived fact
// depends, for dependency-directed backtracking. Logically it is a set of
// non-negative branching-point integers (with the empty set written `{ }`).
//
// HermiT stores permanent dependency sets as a shared descending linked list,
// canonicalized by an identity-keyed table with usage-counted garbage
// collection. This port preserves the *logic* (the set semantics and every
// factory operation) with a content-keyed interner; the shared-tail linked list
// and free-list are memory optimizations that do not affect results, so the
// usage counting here simply prunes unreferenced canonical sets.

use rustc_hash::FxHashMap as HashMap;
use std::sync::Arc;

/// The `DependencySet` interface.
pub trait DependencySetOps {
    fn contains_branching_point(&self, branching_point: i32) -> bool;
    fn is_empty(&self) -> bool;
    fn get_maximum_branching_point(&self) -> i32;
}

/// A permanent dependency set: an immutable, canonicalized set of branching
/// points, stored sorted in descending order (so the maximum is the head, as in
/// HermiT's descending linked list).
#[derive(Clone)]
pub struct PermanentDependencySet(Arc<Vec<i32>>);

impl PartialEq for PermanentDependencySet {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0) || self.0 == other.0
    }
}
impl Eq for PermanentDependencySet {}
impl std::hash::Hash for PermanentDependencySet {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}
impl std::fmt::Debug for PermanentDependencySet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{ ")?;
        for (i, bp) in self.0.iter().enumerate() {
            if i != 0 {
                write!(f, ",")?;
            }
            write!(f, "{bp}")?;
        }
        write!(f, " }}")
    }
}

impl PermanentDependencySet {
    /// Reproduces HermiT's reference-equality fast path: interned canonical sets
    /// share one allocation, so this holds exactly for equal sets.
    pub fn ptr_eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}

impl DependencySetOps for PermanentDependencySet {
    fn contains_branching_point(&self, branching_point: i32) -> bool {
        // Java's PermanentDependencySet list terminates at the empty-set node whose
        // branching point is -1, so containsBranchingPoint(-1) is always true.
        branching_point == -1 || self.0.contains(&branching_point)
    }
    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
    fn get_maximum_branching_point(&self) -> i32 {
        // HermiT's empty set reports -1.
        self.0.first().copied().unwrap_or(-1)
    }
}

/// A temporary union of dependency sets (the Java `UnionDependencySet`), which
/// can be created directly and turned into a permanent set by the factory.
#[derive(Clone, Debug, Default)]
pub struct UnionDependencySet {
    dependency_sets: Vec<DependencySet>,
}

impl UnionDependencySet {
    pub fn new(number_of_constituents: usize) -> UnionDependencySet {
        UnionDependencySet {
            dependency_sets: Vec::with_capacity(number_of_constituents),
        }
    }
    pub fn number_of_constituents(&self) -> usize {
        self.dependency_sets.len()
    }
    pub fn constituent(&self, index: usize) -> &DependencySet {
        &self.dependency_sets[index]
    }
    pub fn set_constituent(&mut self, index: usize, constituent: DependencySet) {
        self.dependency_sets[index] = constituent;
    }
    pub fn clear_constituents(&mut self) {
        self.dependency_sets.clear();
    }
    pub fn add_constituent(&mut self, constituent: DependencySet) {
        self.dependency_sets.push(constituent);
    }
}

impl DependencySetOps for UnionDependencySet {
    fn contains_branching_point(&self, branching_point: i32) -> bool {
        self.dependency_sets
            .iter()
            .rev()
            .any(|set| set.contains_branching_point(branching_point))
    }
    fn get_maximum_branching_point(&self) -> i32 {
        self.dependency_sets
            .iter()
            .map(|set| set.get_maximum_branching_point())
            .max()
            .unwrap_or(-1)
    }
    fn is_empty(&self) -> bool {
        self.dependency_sets.iter().all(|set| set.is_empty())
    }
}

/// A dependency set, either permanent or a temporary union.
#[derive(Clone, Debug)]
pub enum DependencySet {
    Permanent(PermanentDependencySet),
    Union(UnionDependencySet),
}

impl DependencySetOps for DependencySet {
    fn contains_branching_point(&self, branching_point: i32) -> bool {
        match self {
            DependencySet::Permanent(s) => s.contains_branching_point(branching_point),
            DependencySet::Union(s) => s.contains_branching_point(branching_point),
        }
    }
    fn is_empty(&self) -> bool {
        match self {
            DependencySet::Permanent(s) => s.is_empty(),
            DependencySet::Union(s) => s.is_empty(),
        }
    }
    fn get_maximum_branching_point(&self) -> i32 {
        match self {
            DependencySet::Permanent(s) => s.get_maximum_branching_point(),
            DependencySet::Union(s) => s.get_maximum_branching_point(),
        }
    }
}

impl From<PermanentDependencySet> for DependencySet {
    fn from(s: PermanentDependencySet) -> Self {
        DependencySet::Permanent(s)
    }
}
impl From<UnionDependencySet> for DependencySet {
    fn from(s: UnionDependencySet) -> Self {
        DependencySet::Union(s)
    }
}

struct CanonicalEntry {
    set: PermanentDependencySet,
    usage: usize,
}

/// The factory that canonicalizes permanent dependency sets and implements the
/// add/remove/union operations (the Java `DependencySetFactory`).
pub struct DependencySetFactory {
    canonical: HashMap<Vec<i32>, CanonicalEntry>,
    empty_set: PermanentDependencySet,
}

impl DependencySetFactory {
    pub fn new() -> DependencySetFactory {
        let empty_set = PermanentDependencySet(Arc::new(Vec::new()));
        let mut canonical = HashMap::default();
        canonical.insert(
            Vec::new(),
            CanonicalEntry { set: empty_set.clone(), usage: 1 },
        );
        DependencySetFactory { canonical, empty_set }
    }

    pub fn empty_set(&self) -> PermanentDependencySet {
        self.empty_set.clone()
    }

    /// Port of `DependencySetFactory.clear()` (DependencySetFactory.java:55-70):
    /// discards every interned (non-empty) dependency set and the usage/unused
    /// bookkeeping, leaving only the empty set with usage 1. This is per-test
    /// state: every interned set's branching points belong to a test's branching
    /// trail, so it must be reset between satisfiability tests.
    pub fn clear(&mut self) {
        let empty_set = PermanentDependencySet(Arc::new(Vec::new()));
        self.empty_set = empty_set.clone();
        self.canonical.clear();
        self.canonical.insert(
            Vec::new(),
            CanonicalEntry { set: empty_set, usage: 1 },
        );
    }

    /// Emulates Java's `DependencySetFactory.sizeInMemory()` = `m_entries.length*4 + m_size*20`.
    /// Java uses an open-addressed array starting at capacity 16, resizing (doubling) whenever
    /// `m_size >= 0.75 * capacity` (DependencySetFactory.java:52-54, resizeEntries at :194-209).
    /// We synthesise the equivalent capacity from the live canonical-set count, then apply the
    /// same formula so that the timing-monitor statistics line is numerically identical.
    pub fn size_in_memory(&self) -> usize {
        // Java's `m_size` counts only the non-empty interned sets held in
        // `m_entries`; the empty set lives in the separate `m_emptySet` field and
        // is never counted. Our `canonical` map also holds the empty set, so
        // exclude it.
        let m_size = self.canonical.len() - 1;
        // Reproduce Java's initial capacity=16, load factor=0.75, doubling rule.
        let mut capacity: usize = 16;
        while (m_size as f64) >= capacity as f64 * 0.75 {
            capacity *= 2;
        }
        capacity * 4 + m_size * 20
    }

    /// Interns a set of branching points, returning the canonical instance.
    fn intern(&mut self, mut branching_points: Vec<i32>) -> PermanentDependencySet {
        // Canonical form: sorted descending, duplicate-free.
        branching_points.sort_unstable_by(|a, b| b.cmp(a));
        branching_points.dedup();
        if let Some(entry) = self.canonical.get(&branching_points) {
            return entry.set.clone();
        }
        let set = PermanentDependencySet(Arc::new(branching_points.clone()));
        self.canonical
            .insert(branching_points, CanonicalEntry { set: set.clone(), usage: 0 });
        set
    }

    /// Flattens any union into a canonical permanent dependency set.
    /// The interned permanent union of the (present) `constituents` -- the
    /// branching points of every `Some` constituent, canonicalised. This is what
    /// the clause evaluator needs for a derived fact's dependency set; computing
    /// it directly avoids building a throwaway `UnionDependencySet` (a `Vec` plus
    /// an `Arc` clone per constituent) and then re-walking it in `get_permanent`.
    pub fn permanent_union_of(
        &mut self,
        constituents: &[Option<PermanentDependencySet>],
    ) -> PermanentDependencySet {
        let mut branching_points: Vec<i32> = Vec::new();
        for constituent in constituents {
            if let Some(dependency_set) = constituent {
                branching_points.extend(dependency_set.0.iter().copied());
            }
        }
        self.intern(branching_points)
    }

    pub fn get_permanent(&mut self, dependency_set: &DependencySet) -> PermanentDependencySet {
        match dependency_set {
            DependencySet::Permanent(s) => s.clone(),
            DependencySet::Union(_) => {
                let mut branching_points: Vec<i32> = Vec::new();
                collect_branching_points(dependency_set, &mut branching_points);
                self.intern(branching_points)
            }
        }
    }

    pub fn add_branching_point(
        &mut self,
        dependency_set: &DependencySet,
        branching_point: i32,
    ) -> PermanentDependencySet {
        let permanent = self.get_permanent(dependency_set);
        if permanent.contains_branching_point(branching_point) {
            return permanent;
        }
        let mut branching_points = (*permanent.0).clone();
        branching_points.push(branching_point);
        self.intern(branching_points)
    }

    pub fn remove_branching_point(
        &mut self,
        dependency_set: &DependencySet,
        branching_point: i32,
    ) -> PermanentDependencySet {
        let permanent = self.get_permanent(dependency_set);
        if !permanent.contains_branching_point(branching_point) {
            return permanent;
        }
        let branching_points: Vec<i32> = permanent
            .0
            .iter()
            .copied()
            .filter(|bp| *bp != branching_point)
            .collect();
        self.intern(branching_points)
    }

    pub fn union_with(
        &mut self,
        set1: &DependencySet,
        set2: &DependencySet,
    ) -> PermanentDependencySet {
        let permanent1 = self.get_permanent(set1);
        let permanent2 = self.get_permanent(set2);
        if permanent1 == permanent2 {
            return permanent1;
        }
        let mut branching_points = (*permanent1.0).clone();
        branching_points.extend(permanent2.0.iter().copied());
        self.intern(branching_points)
    }

    // -- Usage counting / garbage collection (memory management only) --------

    pub fn add_usage(&mut self, dependency_set: &PermanentDependencySet) {
        if let Some(entry) = self.canonical.get_mut(&*dependency_set.0) {
            entry.usage += 1;
        }
    }

    pub fn remove_usage(&mut self, dependency_set: &PermanentDependencySet) {
        if let Some(entry) = self.canonical.get_mut(&*dependency_set.0) {
            if entry.usage > 0 {
                entry.usage -= 1;
            }
        }
    }

    pub fn remove_unused_sets(&mut self) {
        // Keep the empty set (always in use) and any set with non-zero usage.
        self.canonical
            .retain(|key, entry| key.is_empty() || entry.usage > 0);
    }
}

impl Default for DependencySetFactory {
    fn default() -> Self {
        DependencySetFactory::new()
    }
}

fn collect_branching_points(dependency_set: &DependencySet, out: &mut Vec<i32>) {
    match dependency_set {
        DependencySet::Permanent(s) => out.extend(s.0.iter().copied()),
        DependencySet::Union(u) => {
            for index in 0..u.number_of_constituents() {
                collect_branching_points(u.constituent(index), out);
            }
        }
    }
}
