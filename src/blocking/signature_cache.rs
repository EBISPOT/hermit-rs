// Port of org.semanticweb.HermiT.blocking.BlockingSignatureCache.
//
// When a clash-free model is found, the blocking strategy's `modelFound` hook
// records the *blocking signature* of every active, unblocked, blockable node
// into a `BlockingSignatureCache`. On a later satisfiability test the strategy
// can then short-circuit `computeBlocking`: a node whose signature is already in
// the cache is immediately marked blocked (Java's
// `Node.SIGNATURE_CACHE_BLOCKER`), because a previously-found model already
// witnessed that this signature is satisfiable, so its existentials need not be
// re-expanded.
//
// Java keys the cache on the `DirectBlockingChecker`'s blocking hash code and a
// `BlockingSignature` object whose `blocksNode` compares the interned label
// identities. This port keeps the same SEMANTICS without the `SetFactory`
// interning + `Node.getBlockingObject()` plumbing (which the Rust engine does not
// use): a signature is the concrete value HermiT's signature would compare equal
// to -- the single atomic-concept label, or the pairwise tuple (node label,
// parent label, parent->node edge, node->parent edge). Membership is exact set
// equality, exactly as `blocksNode` compares interned-set identity.
//
// The cache is only used when the ontology has NO nominals and the blocking
// strategy is not a core/validated one -- this mirrors `Reasoner.createTableau`,
// which constructs a `BlockingSignatureCache` only in that case (a nominal or a
// core-validated block can be invalidated by later merges, so caching its
// signature would be unsound).

use std::collections::BTreeSet;
use std::collections::HashSet;

use crate::model::{AtomicConcept, AtomicRole};

/// The cached blocking signature of a model node. The variant matches the
/// configured `DirectBlockingChecker`: `Single` is the node's own
/// atomic-concept label only (`SingleBlockingSignature`); `Pairwise` is the
/// four-component double-blocking signature (`PairWiseBlockingSignature`).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum CachedSignature {
    /// `SingleBlockingSignature`: the node's atomic-concept label.
    Single(BTreeSet<AtomicConcept>),
    /// `PairWiseBlockingSignature`: (node label, parent label, parent->node edge
    /// roles, node->parent edge roles).
    Pairwise(
        BTreeSet<AtomicConcept>,
        BTreeSet<AtomicConcept>,
        BTreeSet<AtomicRole>,
        BTreeSet<AtomicRole>,
    ),
}

/// Port of `BlockingSignatureCache`: a set of node blocking signatures seen in a
/// previously-found model. `add_node`/`contains_signature` mirror the Java
/// methods; the Java open-addressing bucket array is replaced by a `HashSet`
/// (membership and insertion have the same observable behaviour -- the hash
/// scrambling in Java is purely an implementation detail of its table).
#[derive(Debug, Default, Clone)]
pub struct BlockingSignatureCache {
    signatures: HashSet<CachedSignature>,
}

impl BlockingSignatureCache {
    pub fn new() -> BlockingSignatureCache {
        BlockingSignatureCache { signatures: HashSet::new() }
    }

    /// `isEmpty`.
    pub fn is_empty(&self) -> bool {
        self.signatures.is_empty()
    }

    /// `addNode`: record this node's signature. Returns `true` if it was newly
    /// added (Java returns `false` when an equal signature was already present).
    pub fn add_signature(&mut self, signature: CachedSignature) -> bool {
        self.signatures.insert(signature)
    }

    /// `containsSignature`: whether a model node with this exact signature has
    /// already been recorded.
    pub fn contains_signature(&self, signature: &CachedSignature) -> bool {
        self.signatures.contains(signature)
    }

    /// The number of cached signatures (for tests / statistics).
    pub fn len(&self) -> usize {
        self.signatures.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::AtomicConcept;

    fn concept(iri: &str) -> AtomicConcept {
        AtomicConcept::create(iri)
    }

    #[test]
    fn add_and_contains_single_signature() {
        let mut cache = BlockingSignatureCache::new();
        assert!(cache.is_empty());
        let mut label = BTreeSet::new();
        label.insert(concept("http://example.org/A"));
        let sig = CachedSignature::Single(label.clone());
        // First add succeeds; a duplicate add returns false but membership holds.
        assert!(cache.add_signature(sig.clone()));
        assert!(!cache.add_signature(sig.clone()));
        assert!(cache.contains_signature(&sig));
        assert_eq!(cache.len(), 1);

        // A different label is not a member.
        let mut other = BTreeSet::new();
        other.insert(concept("http://example.org/B"));
        assert!(!cache.contains_signature(&CachedSignature::Single(other)));
    }

    #[test]
    fn single_and_pairwise_signatures_are_distinct() {
        let mut a = BTreeSet::new();
        a.insert(concept("http://example.org/A"));
        let single = CachedSignature::Single(a.clone());
        let pairwise =
            CachedSignature::Pairwise(a, BTreeSet::new(), BTreeSet::new(), BTreeSet::new());
        assert_ne!(single, pairwise);
    }
}
