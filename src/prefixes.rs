// Port of org.semanticweb.HermiT.Prefixes.
//
// Responsible for abbreviating and expanding IRIs against a set of prefix
// declarations. The behaviour mirrors the Java original, including the
// "longest prefix IRI first" matching order and the PN_LOCAL local-name grammar.

use std::collections::BTreeMap;
use std::sync::OnceLock;

use regex::Regex;

const PN_CHARS_BASE: &str = "[A-Za-z\\x{00C0}-\\x{00D6}\\x{00D8}-\\x{00F6}\\x{00F8}-\\x{02FF}\\x{0370}-\\x{037D}\\x{037F}-\\x{1FFF}\\x{200C}-\\x{200D}\\x{2070}-\\x{218F}\\x{2C00}-\\x{2FEF}\\x{3001}-\\x{D7FF}\\x{F900}-\\x{FDCF}\\x{FDF0}-\\x{FFFD}]";
const PN_CHARS: &str = "[A-Za-z0-9_\\x{002D}\\x{00B7}\\x{00C0}-\\x{00D6}\\x{00D8}-\\x{00F6}\\x{00F8}-\\x{02FF}\\x{0300}-\\x{036F}\\x{0370}-\\x{037D}\\x{037F}-\\x{1FFF}\\x{200C}-\\x{200D}\\x{203F}-\\x{2040}\\x{2070}-\\x{218F}\\x{2C00}-\\x{2FEF}\\x{3001}-\\x{D7FF}\\x{F900}-\\x{FDCF}\\x{FDF0}-\\x{FFFD}]";

fn local_name_checker() -> &'static Regex {
    static RE: OnceLock<Regex> = OnceLock::new();
    RE.get_or_init(|| {
        // Anchored full match, matching Java's Matcher.matches().
        let pattern = format!(
            "^(?:({base}|_|[0-9])(?:(?:{chars}|[.])*({chars}))?)$",
            base = PN_CHARS_BASE,
            chars = PN_CHARS
        );
        Regex::new(&pattern).expect("local name regex")
    })
}

/// The well-known Semantic Web prefixes (prefix name -> prefix IRI).
pub fn semantic_web_prefixes() -> &'static BTreeMap<String, String> {
    static MAP: OnceLock<BTreeMap<String, String>> = OnceLock::new();
    MAP.get_or_init(|| {
        let mut m = BTreeMap::new();
        m.insert("rdf:".to_string(), "http://www.w3.org/1999/02/22-rdf-syntax-ns#".to_string());
        m.insert("rdfs:".to_string(), "http://www.w3.org/2000/01/rdf-schema#".to_string());
        m.insert("owl:".to_string(), "http://www.w3.org/2002/07/owl#".to_string());
        m.insert("xsd:".to_string(), "http://www.w3.org/2001/XMLSchema#".to_string());
        m.insert("swrl:".to_string(), "http://www.w3.org/2003/11/swrl#".to_string());
        m.insert("swrlb:".to_string(), "http://www.w3.org/2003/11/swrlb#".to_string());
        m.insert("swrlx:".to_string(), "http://www.w3.org/2003/11/swrlx#".to_string());
        m.insert("ruleml:".to_string(), "http://www.w3.org/2003/11/ruleml#".to_string());
        m
    })
}

#[derive(Clone, Debug, Default)]
pub struct Prefixes {
    prefix_iris_by_prefix_name: BTreeMap<String, String>,
    prefix_names_by_prefix_iri: BTreeMap<String, String>,
    /// Cache of `(prefix_name, prefix_iri)` ordered longest prefix-IRI first --
    /// the analogue of Java's `m_prefixIRIMatchingPattern`. Rebuilt by
    /// `build_prefix_iri_matching_pattern` whenever the declarations change, so
    /// `abbreviate_iri` does not re-sort on every call.
    prefix_iri_matching_order: Vec<(String, String)>,
    /// When true, declarations are rejected (the standard immutable instance).
    immutable: bool,
}

impl Prefixes {
    pub fn new() -> Self {
        Prefixes::default()
    }

    /// The shared, immutable instance carrying the well-known Semantic Web
    /// prefixes -- equivalent to `Prefixes.ImmutablePrefixes.getStandartPrefixes()`.
    pub fn standard() -> &'static Prefixes {
        static STD: OnceLock<Prefixes> = OnceLock::new();
        STD.get_or_init(|| {
            let mut p = Prefixes::new();
            for (name, iri) in semantic_web_prefixes() {
                p.declare_prefix_raw(name, iri).ok();
            }
            p.build_prefix_iri_matching_pattern();
            p.immutable = true;
            p
        })
    }

    /// Port of `Prefixes.buildPrefixIRIMatchingPattern`: rebuild the cached
    /// longest-prefix-IRI-first matching order from the current declarations.
    /// Called by every declaration mutator (mirroring Java rebuilding
    /// `m_prefixIRIMatchingPattern`), so `abbreviate_iri` never re-sorts.
    fn build_prefix_iri_matching_pattern(&mut self) {
        let mut list: Vec<(String, String)> = self
            .prefix_names_by_prefix_iri
            .iter()
            .map(|(iri, name)| (name.clone(), iri.clone()))
            .collect();
        // Sort the prefix IRIs, longest first.
        list.sort_by(|lhs, rhs| rhs.1.len().cmp(&lhs.1.len()));
        self.prefix_iri_matching_order = list;
    }

    pub fn abbreviate_iri(&self, iri: &str) -> String {
        // Java `Prefixes.abbreviateIRI` selects the single *longest* prefix IRI that
        // prefixes `iri` (its matching pattern is the prefix IRIs in longest-first
        // alternation, matched once). If that prefix's local name is invalid it
        // returns `<iri>` outright -- it does NOT fall back to a shorter prefix.
        for (prefix, prefix_iri) in &self.prefix_iri_matching_order {
            if let Some(local_name) = iri.strip_prefix(prefix_iri.as_str()) {
                if Self::is_valid_local_name(local_name) {
                    return format!("{prefix}{local_name}");
                }
                break;
            }
        }
        format!("<{iri}>")
    }

    pub fn expand_abbreviated_iri(&self, abbreviation: &str) -> Result<String, String> {
        if abbreviation.starts_with('<') {
            if !abbreviation.ends_with('>') {
                return Err(format!(
                    "The string '{abbreviation}' is not a valid abbreviation: IRIs must be enclosed in '<' and '>'."
                ));
            }
            return Ok(abbreviation[1..abbreviation.len() - 1].to_string());
        }
        match abbreviation.find(':') {
            Some(pos) => {
                let prefix = &abbreviation[..pos + 1];
                match self.prefix_iris_by_prefix_name.get(prefix) {
                    Some(prefix_iri) => Ok(format!("{prefix_iri}{}", &abbreviation[pos + 1..])),
                    None => {
                        if prefix == "http:" {
                            Err(format!("The IRI '{abbreviation}' must be enclosed in '<' and '>' to be used as an abbreviation."))
                        } else {
                            Err(format!("The string '{prefix}' is not a registered prefix name."))
                        }
                    }
                }
            }
            None => Err(format!(
                "The abbreviation '{abbreviation}' is not valid (it does not start with a colon)."
            )),
        }
    }

    pub fn can_be_expanded(&self, iri: &str) -> bool {
        if iri.starts_with('<') {
            false
        } else if let Some(pos) = iri.find(':') {
            self.prefix_iris_by_prefix_name.contains_key(&iri[..pos + 1])
        } else {
            false
        }
    }

    pub fn declare_prefix(&mut self, prefix_name: &str, prefix_iri: &str) -> Result<bool, String> {
        let contains_prefix = self.declare_prefix_raw(prefix_name, prefix_iri)?;
        self.build_prefix_iri_matching_pattern();
        Ok(contains_prefix)
    }

    fn declare_prefix_raw(&mut self, prefix_name: &str, prefix_iri: &str) -> Result<bool, String> {
        if self.immutable {
            return Err("The well-known standard Prefix instance cannot be modified.".to_string());
        }
        if !prefix_name.ends_with(':') {
            return Err(format!(
                "Prefix name '{prefix_name}' should end with a colon character."
            ));
        }
        if let Some(existing) = self.prefix_names_by_prefix_iri.get(prefix_iri) {
            if existing != prefix_name {
                return Err(format!(
                    "The prefix IRI '{prefix_iri}' has already been associated with the prefix name '{existing}'."
                ));
            }
        }
        self.prefix_names_by_prefix_iri
            .insert(prefix_iri.to_string(), prefix_name.to_string());
        let previous = self
            .prefix_iris_by_prefix_name
            .insert(prefix_name.to_string(), prefix_iri.to_string());
        Ok(previous.is_none())
    }

    pub fn declare_default_prefix(&mut self, default_prefix_iri: &str) -> Result<bool, String> {
        self.declare_prefix(":", default_prefix_iri)
    }

    pub fn get_prefix_iri(&self, prefix_name: &str) -> Option<&String> {
        self.prefix_iris_by_prefix_name.get(prefix_name)
    }

    pub fn get_prefix_name(&self, prefix_iri: &str) -> Option<&String> {
        self.prefix_names_by_prefix_iri.get(prefix_iri)
    }

    /// Declares the standard Semantic Web prefixes, returning whether at least
    /// one prefix was *newly* added (Java `declareSemanticWebPrefixes` returns
    /// the OR of `declarePrefixRaw`, which is `true` when the prefix name was not
    /// already present). The previous implementation inverted this.
    pub fn declare_semantic_web_prefixes(&mut self) -> bool {
        let mut contains_prefix = false;
        for (name, iri) in semantic_web_prefixes() {
            if let Ok(true) = self.declare_prefix_raw(name, iri) {
                contains_prefix = true;
            }
        }
        self.build_prefix_iri_matching_pattern();
        contains_prefix
    }

    /// Port of `Prefixes.declareInternalPrefixes`: registers the HermiT-internal
    /// prefixes used to abbreviate generated IRIs in debug/`toString` output --
    /// `def:`, `defdata:`, `nnq:`, `all:`, `swrl:`, `prop:`, one `nom`/`nom2`/...
    /// per named individual, one `anon`/`anon2`/... per anonymous individual, and
    /// `nam:`. Returns `true` if any prefix was newly added.
    pub fn declare_internal_prefixes<'a, I, A>(
        &mut self,
        individual_iris: I,
        anon_individual_iris: A,
    ) -> bool
    where
        I: IntoIterator<Item = &'a str>,
        A: IntoIterator<Item = &'a str>,
    {
        let mut contains_prefix = false;
        let mut declare = |this: &mut Self, name: &str, iri: &str| {
            if let Ok(true) = this.declare_prefix_raw(name, iri) {
                contains_prefix = true;
            }
        };
        declare(self, "def:", "internal:def#");
        declare(self, "defdata:", "internal:defdata#");
        declare(self, "nnq:", "internal:nnq#");
        declare(self, "all:", "internal:all#");
        declare(self, "swrl:", "internal:swrl#");
        declare(self, "prop:", "internal:prop#");
        for (index, iri) in individual_iris.into_iter().enumerate() {
            let suffix = if index == 0 { String::new() } else { (index + 1).to_string() };
            declare(self, &format!("nom{suffix}:"), &format!("internal:nom#{iri}"));
        }
        for (index, iri) in anon_individual_iris.into_iter().enumerate() {
            let suffix = if index == 0 { String::new() } else { (index + 1).to_string() };
            declare(self, &format!("anon{suffix}:"), &format!("internal:anon#{iri}"));
        }
        declare(self, "nam:", "internal:nam#");
        self.build_prefix_iri_matching_pattern();
        contains_prefix
    }

    /// Port of `Prefixes.addPrefixes`: registers every prefix from `other`,
    /// returning `true` if at least one prefix name was *newly* added (the OR of
    /// `declarePrefixRaw`, which is `true` when the name was not already present).
    pub fn add_prefixes(&mut self, other: &Prefixes) -> bool {
        let mut contains_prefix = false;
        for (name, iri) in &other.prefix_iris_by_prefix_name {
            if let Ok(true) = self.declare_prefix_raw(name, iri) {
                contains_prefix = true;
            }
        }
        self.build_prefix_iri_matching_pattern();
        contains_prefix
    }

    /// Returns a reference to the sorted prefix-name → prefix-IRI map, mirroring
    /// Java's `Prefixes.getPrefixIRIsByPrefixName()` (used by `DumpPrefixesAction`).
    pub fn prefix_iris_by_prefix_name(&self) -> &BTreeMap<String, String> {
        &self.prefix_iris_by_prefix_name
    }

    pub fn is_internal_iri(iri: &str) -> bool {
        iri.starts_with("internal:")
    }

    pub fn is_valid_local_name(local_name: &str) -> bool {
        local_name_checker().is_match(local_name)
    }
}

impl std::fmt::Display for Prefixes {
    /// Port of `Prefixes.toString`, which returns `m_prefixIRIsByPrefixName
    /// .toString()`. The Java map is a `TreeMap`, so its `toString` is the
    /// key-sorted `{name=iri, name=iri}` form, which `BTreeMap`'s ordered
    /// iteration reproduces.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{")?;
        for (index, (name, iri)) in self.prefix_iris_by_prefix_name.iter().enumerate() {
            if index != 0 {
                write!(f, ", ")?;
            }
            write!(f, "{name}={iri}")?;
        }
        write!(f, "}}")
    }
}

#[cfg(test)]
mod tests {
    use super::Prefixes;

    #[test]
    fn declare_semantic_web_prefixes_matches_java_return() {
        let mut prefixes = Prefixes::new();
        // First declaration on an empty instance adds the prefixes -> true.
        assert!(prefixes.declare_semantic_web_prefixes());
        // Re-declaration adds nothing new -> false.
        assert!(!prefixes.declare_semantic_web_prefixes());
    }

    #[test]
    fn declare_internal_prefixes_registers_internal_and_per_individual() {
        let mut prefixes = Prefixes::new();
        let added = prefixes.declare_internal_prefixes(
            ["http://ex/a", "http://ex/b"],
            ["http://ex/anon1"],
        );
        assert!(added);
        // Fixed internal prefixes.
        assert_eq!(prefixes.get_prefix_iri("def:"), Some(&"internal:def#".to_string()));
        assert_eq!(prefixes.get_prefix_iri("nam:"), Some(&"internal:nam#".to_string()));
        // Per-individual: first is `nom:`, second `nom2:` (Java's index==1 ? "" : index).
        assert_eq!(prefixes.get_prefix_iri("nom:"), Some(&"internal:nom#http://ex/a".to_string()));
        assert_eq!(prefixes.get_prefix_iri("nom2:"), Some(&"internal:nom#http://ex/b".to_string()));
        assert_eq!(
            prefixes.get_prefix_iri("anon:"),
            Some(&"internal:anon#http://ex/anon1".to_string())
        );
        // Idempotent re-declaration adds nothing.
        assert!(!prefixes.declare_internal_prefixes(["http://ex/a", "http://ex/b"], ["http://ex/anon1"]));
    }

    #[test]
    fn declare_prefix_returns_true_only_for_new_name() {
        let mut prefixes = Prefixes::new();
        assert_eq!(prefixes.declare_prefix("ex:", "http://example.org/"), Ok(true));
        // Same name re-declared (to the same IRI) is no longer new -> false.
        assert_eq!(prefixes.declare_prefix("ex:", "http://example.org/"), Ok(false));
    }

    #[test]
    fn add_prefixes_merges_and_reports_new() {
        let mut source = Prefixes::new();
        source.declare_prefix("ex:", "http://example.org/").unwrap();
        source.declare_prefix("foo:", "http://foo.org/").unwrap();

        let mut target = Prefixes::new();
        // Both prefixes are new -> true, and they become usable for abbreviation.
        assert!(target.add_prefixes(&source));
        assert_eq!(target.get_prefix_iri("ex:"), Some(&"http://example.org/".to_string()));
        assert_eq!(
            target.abbreviate_iri("http://example.org/Thing"),
            "ex:Thing"
        );
        // Re-adding the same prefixes adds nothing new -> false.
        assert!(!target.add_prefixes(&source));
    }

    #[test]
    fn display_matches_treemap_tostring() {
        let mut prefixes = Prefixes::new();
        prefixes.declare_prefix("ex:", "http://example.org/").unwrap();
        prefixes.declare_prefix("a:", "http://a.org/").unwrap();
        // Java `Prefixes.toString` is the key-sorted TreeMap form.
        assert_eq!(
            prefixes.to_string(),
            "{a:=http://a.org/, ex:=http://example.org/}"
        );
    }

    #[test]
    fn declare_prefix_rejects_conflicting_iri() {
        let mut prefixes = Prefixes::new();
        prefixes.declare_prefix("a:", "http://example.org/x").unwrap();
        // The same IRI under a different name is a conflict (Java throws).
        assert!(prefixes.declare_prefix("b:", "http://example.org/x").is_err());
    }
}
