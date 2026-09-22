//! Explicit parity debt: execute every case, then reject any changed outcome.
//! HERMIT_JAVA_STRICT=1 exposes all mismatches as ordinary failing tests.
use serde_json::Value;
use std::sync::OnceLock;
fn expected() -> &'static Value {
    static EXPECTED: OnceLock<Value> = OnceLock::new();
    EXPECTED.get_or_init(|| {
        serde_json::from_str(include_str!("../java/expected-failures.json")).unwrap()
    })
}
#[allow(dead_code)] // Used by the replay runner, not the native unit-test runner.
pub fn is_known_failure(name: &str) -> bool {
    expected().get(name).is_some()
}
pub fn signature(output: &str) -> String {
    if output.contains("512 MiB allocation budget") {
        return "allocation budget".into();
    }
    if output.contains("case timed out") || output.contains("worker None") {
        return "timeout".into();
    }
    let lines: Vec<_> = output.lines().collect();
    let operation = lines
        .iter()
        .rev()
        .find(|s| s.contains(" operation "))
        .copied()
        .unwrap_or("");
    let message = lines
        .iter()
        .position(|s| s.contains("panicked at "))
        .and_then(|i| lines.get(i + 1))
        .copied()
        .unwrap_or("worker failed without a panic message");
    format!("{operation}\n{message}")
}
pub fn check(name: &str, result: Result<(), String>) -> Result<(), String> {
    if std::env::var_os("HERMIT_JAVA_STRICT").is_some() {
        return result;
    }
    check_against(name, expected().get(name), result)
}
fn check_against(
    name: &str,
    known: Option<&Value>,
    result: Result<(), String>,
) -> Result<(), String> {
    match (known, result) {
        (None, result) => result,
        (Some(_), Ok(())) => Err(format!(
            "{name}: known failure now passes; remove its stale parity exception"
        )),
        (Some(known), Err(output)) => {
            let actual = signature(&output);
            if known["signature"] == actual {
                eprintln!("XFAIL {name}: {}", known["origin"].as_str().unwrap());
                Ok(())
            } else {
                Err(format!(
                    "{name}: failure changed; expected {}, got {actual}\n{output}",
                    known["signature"]
                ))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    #[allow(unused_imports)] // libtest-mimic does not collect this module's tests.
    use super::*;
    #[test]
    fn parity_gate_rejects_new_failures_and_stale_exceptions() {
        let failure="case operation 1: isConsistent\nthread 'main' panicked at worker.rs:20:2:\nassertion failed: consistent";
        let known = serde_json::json!({"signature":signature(failure),"origin":"test"});
        assert!(check_against("case", None, Ok(())).is_ok());
        assert!(check_against("case", None, Err(failure.into())).is_err());
        assert!(check_against("case", Some(&known), Err(failure.into())).is_ok());
        assert!(check_against("case", Some(&known), Ok(())).is_err());
        assert!(check_against("case", Some(&known), Err("case timed out".into())).is_err());
        assert!(check_against(
            "case",
            Some(&known),
            Err(failure.replace("consistent", "different assertion"))
        )
        .is_err());
    }
    #[test]
    fn failure_signature_keeps_operation_and_failure_kind() {
        let original="case operation 1: isConsistent\nthread 'main' panicked at worker.rs:20:2:\nassertion failed";
        assert_eq!(
            signature(original),
            signature(&original.replace("worker.rs:20:2", "some/other/location.rs:50:3"))
        );
        assert_ne!(
            signature(original),
            signature(&original.replace("operation 1", "operation 2"))
        );
        assert_ne!(
            signature(original),
            signature("test worker exceeded its 512 MiB allocation budget")
        );
    }
}
