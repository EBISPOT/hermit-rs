//! Documented corrections of recorded Java expectations (`java/corrections.json`).
use serde_json::Value;
use std::collections::HashMap;

// Replaces each recorded Java expectation of `name` that contradicts the OWL 2
// or XSD specifications with its documented correction. An entry corrects one
// operation, or lists several under `operations`. A correction gives the Java
// value and the corrected one, or, for a list, the Java elements to `remove`.
// The trace keeps the Java value, and the correction applies only while it
// still matches, so regenerated traces cannot silently change what is
// corrected. A corrected value `{"invalid": error}` says the ontology is
// rejected: the reasoner's `create` becomes an `invalid` operation, as Java
// records a rejected ontology, and the reasoner's queries are dropped. Native datatype traces name their operation in `operation`,
// replayed traces in `op`.
pub fn correct(name: &str, rows: &mut Vec<Value>) {
    let corrections: HashMap<String, Value> =
        serde_json::from_str(include_str!("../java/corrections.json")).unwrap();
    let Some(entry) = corrections.get(name) else {
        return;
    };
    let single = [entry.clone()];
    let operations = entry["operations"].as_array().map_or(&single[..], Vec::as_slice);
    let mut rejected: Vec<(Value, Value)> = Vec::new();
    for correction in operations {
        let row = &mut rows[correction["operation"].as_u64().unwrap() as usize];
        let op = if row["operation"].is_string() { &row["operation"] } else { &row["op"] };
        assert_eq!(op, &correction["op"], "{name}: stale correction of the recorded Java operation");
        if let Some(remove) = correction["remove"].as_array() {
            let recorded = row["expected"].as_array_mut().unwrap();
            for value in remove {
                let index = recorded.iter().position(|v| v == value);
                let index = index.unwrap_or_else(|| panic!("{name}: stale correction, {value} not recorded"));
                recorded.remove(index);
            }
        } else {
            assert_eq!(
                row["expected"], correction["java"],
                "{name}: stale correction of the recorded Java expectation"
            );
            match correction["corrected"].get("invalid") {
                Some(error) => rejected.push((row["id"].clone(), error.clone())),
                None => row["expected"] = correction["corrected"].clone(),
            }
        }
    }
    for (id, error) in rejected {
        let create = rows.iter().position(|row| row["op"] == "create" && row["id"] == id);
        let create = create.unwrap_or_else(|| panic!("{name}: no reasoner {id} to reject"));
        let ontology = rows[create]["ontology"].clone();
        rows[create] = serde_json::json!({"op": "invalid", "ontology": ontology, "error": error});
        let mut index = 0;
        rows.retain(|row| {
            index += 1;
            index - 1 == create || row["id"] != id
        });
    }
}
