use hermit_rs::{
    model::{DLClause, DLOntology},
    reasoner::{IncrementalReasoner, Reasoner},
    structural::A,
};
use horned_owl::ontology::set::SetOntology;

#[test]
fn conflicting_string_cardinalities_across_rule_orders() {
    let source = include_str!(
        "java/ontologies/b4b3b3fbd6ed86b2fda8ba58ddf208beef2ed9e8f968cf7f28acd4bdb991e38d.ofn"
    );
    let ontology: SetOntology<A> =
        horned_owl::io::ofn::reader::read(&mut std::io::Cursor::new(source), Default::default())
            .unwrap()
            .0;
    let mut reasoner = IncrementalReasoner::new(ontology);
    let original = reasoner.dl_ontology();
    for seed in 0..64u64 {
        let mut random = seed + 1;
        let mut shuffle = |items: &mut Vec<_>| {
            for i in (1..items.len()).rev() {
                random = random.wrapping_mul(6364136223846793005).wrapping_add(1);
                items.swap(i, (random >> 32) as usize % (i + 1));
            }
        };
        let mut clauses: Vec<_> = original.get_dl_clauses().iter().cloned().collect();
        shuffle(&mut clauses);
        let clauses = clauses
            .into_iter()
            .map(|clause| {
                let mut head = clause.get_head_atoms();
                let mut body = clause.get_body_atoms();
                if !head.is_empty() {
                    let n = seed as usize % head.len();
                    head.rotate_left(n);
                }
                if seed % 2 == 0 {
                    head.reverse();
                    body.reverse();
                }
                DLClause::create(head, body)
            })
            .collect();
        let dl = DLOntology::new(
            "urn:branch-order",
            clauses,
            original.get_positive_facts().clone(),
            original.get_negative_facts().clone(),
            None,
            None,
            None,
            Some(original.get_all_atomic_data_roles().clone()),
            None,
            Some(original.get_defined_datatype_iris().clone()),
            None,
            original.has_inverse_roles(),
            original.has_at_most_restrictions(),
            original.has_nominals(),
            original.has_datatypes(),
        );
        assert!(
            !Reasoner::new(&dl).is_consistent(),
            "rule order {seed}: {:?}",
            dl.get_dl_clauses()
        );
    }
}

#[test]
fn tuple_index_preserves_distinct_predicate_allocations() {
    use hermit_rs::{
        model::{AtomicRole, DLPredicate, InternalDatatype},
        tableau::{object::TableauObject, tuple_index::TupleIndex},
    };
    let mut index = TupleIndex::new(vec![0]);
    let mut objects = Vec::new();
    // These payloads have the same allocation size. Interleaving them exercises
    // nearby addresses whose old XOR-based keys could alias across variants.
    for i in 0..512 {
        let iri = format!("urn:tuple-identity:{i}");
        objects.push(TableauObject::DLPredicate(DLPredicate::AtomicRole(
            AtomicRole::create(&iri),
        )));
        objects.push(TableauObject::DLPredicate(DLPredicate::InternalDatatype(
            InternalDatatype::create(&iri),
        )));
    }
    for (i, object) in objects.iter().enumerate() {
        assert_eq!(index.add_tuple(&[*object], i as i32), i as i32);
    }
    for (i, object) in objects.iter().enumerate() {
        assert_eq!(index.get_tuple_index(&[*object]), i as i32);
    }
}
