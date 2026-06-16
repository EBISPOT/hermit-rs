// Port of the org.semanticweb.HermiT.blocking package: the blocking strategies
// that ensure termination of the hypertableau expansion. This module holds the
// `SetFactory` label interner and the signature/validation machinery; the
// strategies themselves operate on the tableau `Node`s (see `tableau`).

pub mod dl_clause_info;
pub mod set_factory;
pub mod signature_cache;

pub use dl_clause_info::{ArgumentType, ConsequenceAtom, DLClauseInfo, YConstraint};
pub use set_factory::{InternedSet, SetFactory};
pub use signature_cache::{BlockingSignatureCache, CachedSignature};
