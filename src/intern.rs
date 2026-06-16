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
use std::sync::{Arc, Mutex, OnceLock};

/// Intern `value` into the given per-type registry, returning the canonical
/// `Arc`. If an equal value was interned before, the existing `Arc` is cloned
/// and returned; otherwise `value` becomes the canonical instance.
pub fn intern_into<T: Eq + Hash>(registry: &OnceLock<Mutex<HashSet<Arc<T>>>>, value: T) -> Arc<T> {
    let set = registry.get_or_init(|| Mutex::new(HashSet::new()));
    let mut guard = set.lock().expect("interner mutex poisoned");
    if let Some(existing) = guard.get(&value) {
        return existing.clone();
    }
    let arc = Arc::new(value);
    guard.insert(arc.clone());
    arc
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
        #[derive(Clone)]
        $vis struct $name(::std::sync::Arc<$data>);

        impl ::std::ops::Deref for $name {
            type Target = $data;
            #[inline]
            fn deref(&self) -> &$data {
                &self.0
            }
        }

        impl ::std::cmp::PartialEq for $name {
            #[inline]
            fn eq(&self, other: &Self) -> bool {
                // Interning guarantees one allocation per value, so pointer
                // equality is the common fast path; fall back to content.
                ::std::sync::Arc::ptr_eq(&self.0, &other.0) || *self.0 == *other.0
            }
        }
        impl ::std::cmp::Eq for $name {}

        impl ::std::hash::Hash for $name {
            #[inline]
            fn hash<H: ::std::hash::Hasher>(&self, state: &mut H) {
                (*self.0).hash(state);
            }
        }

        impl $name {
            /// Interns `data`, returning the canonical handle.
            fn intern(data: $data) -> $name {
                static REGISTRY: ::std::sync::OnceLock<
                    ::std::sync::Mutex<::std::collections::HashSet<::std::sync::Arc<$data>>>,
                > = ::std::sync::OnceLock::new();
                $name($crate::intern::intern_into(&REGISTRY, data))
            }

            /// Reproduces HermiT's Java reference-equality (`==`) fast path.
            #[inline]
            pub fn ptr_eq(&self, other: &Self) -> bool {
                ::std::sync::Arc::ptr_eq(&self.0, &other.0)
            }
        }

        impl ::std::fmt::Debug for $name {
            fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
                ::std::fmt::Debug::fmt(&*self.0, f)
            }
        }
    };
}
