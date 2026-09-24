//! Profile a merged Functional Syntax import closure, supplied as separate files.
//! OWLMAKE_CLASSIFY_THREADS=1 cargo run --release --example profile_reasoner --
//! instances root.ofn import1.ofn import2.ofn > pairs.tsv
//! Use `classify` instead of `instances` to profile class classification.

use hermit_rs::{hierarchy::ClassificationProgressMonitor, reasoner, structural::A};
use horned_owl::{
    model::{AnnotatedComponent, Build, Class, Component, MutableOntology},
    ontology::{component_mapped::ComponentMappedOntology, set::SetOntology},
};
use std::{fs::File, io::BufReader, time::Instant};

struct Progress(Instant);
impl ClassificationProgressMonitor<Class<A>> for Progress {
    fn element_classified(&mut self, _: &Class<A>) {}
    fn classification_phase(&mut self, phase: &str) {
        eprintln!("{phase}: {:?}", self.0.elapsed());
    }
}

fn main() -> Result<(), String> {
    let args: Vec<_> = std::env::args().skip(1).collect();
    if args.len() < 2 || !matches!(args[0].as_str(), "classify" | "instances") {
        return Err(
            "Usage: profile_reasoner classify|instances FILE [IMPORT_FILE ...] (Functional Syntax)"
                .into(),
        );
    }
    let mut ontology = SetOntology::<A>::new();
    let build = Build::new_arc();
    for path in &args[1..] {
        let file = File::open(path).map_err(|e| format!("{path}: {e}"))?;
        let (part, _): (ComponentMappedOntology<A, AnnotatedComponent<A>>, _) =
            horned_owl::io::ofn::reader::read(
                &mut BufReader::new(file),
                horned_owl::io::ParserConfiguration::new(&build),
            )
            .map_err(|e| format!("{path}: {e}"))?;
        for axiom in horned_owl::model::Ontology::iter(&part) {
            if !matches!(
                axiom.component,
                Component::OntologyID(_) | Component::Import(_) | Component::OntologyAnnotation(_)
            ) {
                ontology.insert(axiom.clone());
            }
        }
    }
    eprintln!(
        "{} axioms; imports supplied by caller",
        ontology.iter().count()
    );
    let start = Instant::now();
    if args[0] == "classify" {
        let h = reasoner::classify_with_monitor(&ontology, &mut Progress(start))?;
        eprintln!("{} classes", h.all_elements().count());
    } else {
        let mut index = reasoner::ObjectPropertyInstanceIndex::new(&ontology)?;
        eprintln!("index: {:?}", start.elapsed());
        let mut count = 0;
        for property in index.object_properties() {
            let mut pairs: Vec<_> = index
                .object_property_instances(property.clone().into())?
                .into_iter()
                .collect();
            pairs.sort();
            count += pairs.len();
            for (source, target) in pairs {
                println!("{}\t{}\t{}", property.0, source.0, target.0);
            }
        }
        eprintln!("{count} property pairs");
    }
    eprintln!("total: {:?}", start.elapsed());
    Ok(())
}
