// Port of org.semanticweb.HermiT.blocking.SetFactory.
//
// Interns sets so that each distinct set (compared with order-independent set
// equality) exists only once, allowing the resulting labels -- used throughout
// blocking -- to be compared by identity. Sets are reference-counted and can be
// made permanent; non-permanent sets are dropped when unreferenced or by
// `clear_nonpermanent`.
//
// HermiT's `Entry` is an array-backed `Set` placed in a hand-rolled hash table
// with a free list; this port keeps the same order-independent hashing
// (sum of element hashes) and equality (equal size + containment), with the
// canonical sets handed out as `Rc`-backed handles.

use std::collections::hash_map::DefaultHasher;
use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

/// A canonical, immutable interned set. Equality and hashing are by identity
/// (the canonical instance), reproducing HermiT's `==` comparison of labels.
pub struct InternedSet<E>(Rc<Vec<E>>);

impl<E> Clone for InternedSet<E> {
    fn clone(&self) -> Self {
        InternedSet(self.0.clone())
    }
}
impl<E> PartialEq for InternedSet<E> {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}
impl<E> Eq for InternedSet<E> {}
impl<E> Hash for InternedSet<E> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (Rc::as_ptr(&self.0) as *const () as usize).hash(state);
    }
}

impl<E: PartialEq> InternedSet<E> {
    pub fn contains(&self, object: &E) -> bool {
        self.0.iter().any(|e| e == object)
    }
}

impl<E> InternedSet<E> {
    pub fn len(&self) -> usize {
        self.0.len()
    }
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
    pub fn iter(&self) -> std::slice::Iter<'_, E> {
        self.0.iter()
    }
    pub fn as_slice(&self) -> &[E] {
        &self.0
    }
}

struct Meta {
    reference_count: i32,
    permanent: bool,
}

pub struct SetFactory<E> {
    /// Order-independent content hash -> canonical sets in that bucket.
    buckets: HashMap<u64, Vec<InternedSet<E>>>,
    meta: HashMap<InternedSet<E>, Meta>,
}

fn element_hash<E: Hash>(element: &E) -> u64 {
    let mut hasher = DefaultHasher::new();
    element.hash(&mut hasher);
    hasher.finish()
}

fn set_hash<E: Hash>(elements: &[E]) -> u64 {
    let mut sum: u64 = 0;
    for element in elements {
        sum = sum.wrapping_add(element_hash(element));
    }
    sum
}

impl<E: Hash + Eq + Clone> SetFactory<E> {
    pub fn new() -> SetFactory<E> {
        SetFactory {
            buckets: HashMap::new(),
            meta: HashMap::new(),
        }
    }

    /// Returns the canonical set equal to `elements`, creating it if necessary.
    pub fn get_set(&mut self, elements: &[E]) -> InternedSet<E> {
        let hash = set_hash(elements);
        if let Some(candidates) = self.buckets.get(&hash) {
            for candidate in candidates {
                if equals_to(candidate, elements) {
                    return candidate.clone();
                }
            }
        }
        let set = InternedSet(Rc::new(elements.to_vec()));
        self.buckets.entry(hash).or_default().push(set.clone());
        self.meta.insert(
            set.clone(),
            Meta { reference_count: 0, permanent: false },
        );
        set
    }

    pub fn add_reference(&mut self, set: &InternedSet<E>) {
        if let Some(meta) = self.meta.get_mut(set) {
            meta.reference_count += 1;
        }
    }

    pub fn remove_reference(&mut self, set: &InternedSet<E>) {
        let should_remove = if let Some(meta) = self.meta.get_mut(set) {
            meta.reference_count -= 1;
            meta.reference_count == 0 && !meta.permanent
        } else {
            false
        };
        if should_remove {
            self.remove_set(set);
        }
    }

    pub fn make_permanent(&mut self, set: &InternedSet<E>) {
        if let Some(meta) = self.meta.get_mut(set) {
            meta.permanent = true;
        }
    }

    pub fn clear_nonpermanent(&mut self) {
        let to_remove: Vec<InternedSet<E>> = self
            .meta
            .iter()
            .filter(|(_, meta)| !meta.permanent)
            .map(|(set, _)| set.clone())
            .collect();
        for set in to_remove {
            self.remove_set(&set);
        }
    }

    fn remove_set(&mut self, set: &InternedSet<E>) {
        self.meta.remove(set);
        let hash = set_hash(set.as_slice());
        if let Some(candidates) = self.buckets.get_mut(&hash) {
            candidates.retain(|candidate| !candidate.eq(set));
            if candidates.is_empty() {
                self.buckets.remove(&hash);
            }
        }
    }
}

impl<E: Hash + Eq + Clone> Default for SetFactory<E> {
    fn default() -> Self {
        SetFactory::new()
    }
}

/// Order-independent set equality (equal length and containment), matching
/// HermiT's `Entry.equalsTo`.
fn equals_to<E: PartialEq>(set: &InternedSet<E>, elements: &[E]) -> bool {
    if set.len() != elements.len() {
        return false;
    }
    set.iter().all(|e| elements.contains(e))
}
