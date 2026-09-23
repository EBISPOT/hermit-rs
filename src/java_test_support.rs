//! Process and allocation limits for imported tests against private internals.
#[path = "../tests/support/clause_compare.rs"]
mod clause_compare;
#[path = "../tests/support/memory_budget.rs"]
mod memory_budget;
#[path = "../tests/support/java_outcome.rs"]
mod outcome;
pub(crate) fn isolated(name: &str) -> bool {
    if std::env::var("HERMIT_JAVA_NATIVE_WORKER").as_deref() == Ok(name) {
        return false;
    }
    let log = std::env::temp_dir().join(format!(
        "hermit-native-{}-{}.log",
        std::process::id(),
        name.replace("::", "-")
    ));
    let file = std::fs::File::create(&log).unwrap();
    let mut child = std::process::Command::new(std::env::current_exe().unwrap())
        .args(["--exact", name, "--nocapture", "--test-threads=1"])
        .env("HERMIT_JAVA_NATIVE_WORKER", name)
        .env("OWLMAKE_CLASSIFY_THREADS", "1")
        .stdout(file.try_clone().unwrap())
        .stderr(file)
        .spawn()
        .unwrap();
    let start = std::time::Instant::now();
    let status = loop {
        if let Some(status) = child.try_wait().unwrap() {
            break Some(status);
        }
        if start.elapsed() > std::time::Duration::from_secs(120) {
            child.kill().unwrap();
            child.wait().unwrap();
            break None;
        }
        std::thread::sleep(std::time::Duration::from_millis(10));
    };
    let output = std::fs::read_to_string(&log).unwrap();
    std::fs::remove_file(log).unwrap();
    let result = if status.is_some_and(|s| s.success()) {
        Ok(())
    } else {
        Err(format!("{name}: worker {status:?}\n{output}"))
    };
    outcome::check(name, result).unwrap_or_else(|error| panic!("{error}"));
    true
}
