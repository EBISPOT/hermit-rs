// Port of org.semanticweb.HermiT.model.InterningManager.
//
// The original HermiT uses a per-class `InterningManager<E>` -- a weak-reference
// hash map that guarantees a single canonical instance per distinct value, so
// that model objects can be compared with Java reference equality (`==`) and
// used as identity-hash keys.
//
// In this Rust port the same guarantee is provided by `intern`, which keeps a
// process-wide `HashSet<Arc<T>>` per interned type and hands back a shared
// `Arc` for equal values. Because every distinct value has exactly one backing
// allocation, `Arc::ptr_eq` reproduces the Java `==` fast path, while the
// derived content-based `Eq`/`Hash` give identical *logical* results.

use std::collections::HashSet;
use std::hash::Hash;
use std::sync::{Mutex, OnceLock};

/// Intern `value` into the given per-type registry, returning a `&'static`
/// reference to the canonical instance. If an equal value was interned before,
/// that reference is returned; otherwise `value` is leaked into a permanent
/// allocation and becomes the canonical instance.
///
/// This mirrors Java HermiT's interned model objects: the canonical instance
/// lives for the whole run (HermiT's `InterningManager` keeps it; we leak it —
/// the previous `Arc` registry also pinned it forever, so the memory behaviour
/// is unchanged) and a handle to it is a plain pointer, copied for free and
/// compared by identity (`==`). Unlike an `Arc`, copying the handle costs no
/// atomic reference-count traffic — the tableau is single-threaded, so that
/// traffic was pure overhead Java never paid.
pub fn intern_into<T: Eq + Hash>(
    registry: &OnceLock<Mutex<HashSet<&'static T>>>,
    value: T,
) -> &'static T {
    let set = registry.get_or_init(|| Mutex::new(HashSet::new()));
    let mut guard = set.lock().expect("interner mutex poisoned");
    if let Some(existing) = guard.get(&value) {
        return existing;
    }
    let leaked: &'static T = Box::leak(Box::new(value));
    guard.insert(leaked);
    leaked
}

/// Implements `Display` for a type that has an inherent
/// `to_string_prefixes(&self, &Prefixes) -> String` method, using the standard
/// (well-known Semantic Web) prefixes -- the equivalent of the no-argument
/// `toString()` overloads in the Java sources.
#[macro_export]
macro_rules! impl_display_prefixes {
    ($($t:ty),+ $(,)?) => {
        $(
            impl ::std::fmt::Display for $t {
                fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
                    write!(f, "{}", self.to_string_prefixes($crate::prefixes::Prefixes::standard()))
                }
            }
        )+
    };
}

/// Declares an interned wrapper type `$name` around an inner data struct
/// `$data`. The wrapper is a cheaply-cloneable handle (an `Arc`) whose equality
/// and hashing delegate to the interned content, mirroring HermiT's interned
/// model objects.
#[macro_export]
macro_rules! interned {
    ($(#[$meta:meta])* $vis:vis $name:ident => $data:ty) => {
        $(#[$meta])*
        #[derive(Clone, Copy)]
        $vis struct $name(&'static $data);

        impl ::std::ops::Deref for $name {
            type Target = $data;
            #[inline]
            fn deref(&self) -> &$data {
                self.0
            }
        }

        impl ::std::cmp::PartialEq for $name {
            #[inline]
            fn eq(&self, other: &Self) -> bool {
                // Interning guarantees one canonical allocation per distinct value
                // (`intern_into` returns the existing handle for equal content), so
                // identity equality on the canonical pointer IS content equality --
                // exactly Java HermiT's `==` on interned model objects.
                ::std::ptr::eq(self.0, other.0)
            }
        }
        impl ::std::cmp::Eq for $name {}

        impl ::std::hash::Hash for $name {
            #[inline]
            fn hash<H: ::std::hash::Hasher>(&self, state: &mut H) {
                // The canonical pointer is a collision-free proxy for the content
                // (see `eq`), so hashing it is consistent with `Eq` and turns every
                // hash of an interned model object (atomic concepts, roles, terms --
                // pervasive as extension-table / tuple-index keys) from an O(IRI
                // length) string hash into an O(1) word hash. The tableau maps are
                // content-addressed by identity and confluent, so the resulting
                // hash-bucket order does not affect the classification.
                (self.0 as *const $data as usize).hash(state);
            }
        }

        impl $name {
            /// Interns `data`, returning the canonical handle (a `Copy` pointer to
            /// the forever-lived canonical instance, like a Java object reference).
            fn intern(data: $data) -> $name {
                static REGISTRY: ::std::sync::OnceLock<
                    ::std::sync::Mutex<::std::collections::HashSet<&'static $data>>,
                > = ::std::sync::OnceLock::new();
                $name($crate::intern::intern_into(&REGISTRY, data))
            }

            /// Reproduces HermiT's Java reference-equality (`==`) fast path.
            #[inline]
            pub fn ptr_eq(&self, other: &Self) -> bool {
                ::std::ptr::eq(self.0, other.0)
            }

            /// The canonical interned-allocation address, a stable per-value word
            /// id (one allocation per distinct value). Equal values share it;
            /// distinct values do not. Use as a cheap total-order/hash key wherever
            /// only a *consistent* order is needed (e.g. the sorted-`Vec` set
            /// canonical form of a blocking signature), avoiding the O(IRI) `Ord`
            /// string comparison. Run-to-run unstable (addresses vary), so never use
            /// it where cross-run-stable ordering is required.
            #[inline]
            pub fn intern_ptr(&self) -> usize {
                self.0 as *const $data as usize
            }
        }

        impl ::std::fmt::Debug for $name {
            fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
                ::std::fmt::Debug::fmt(&*self.0, f)
            }
        }
    };
}
