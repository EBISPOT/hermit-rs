//! Closest-supported port of HermiT's `examples/.../HermiTDebugger.java`.
//!
//! ## Port-API gap
//! The Java `HermiTDebugger` sets `Configuration.tableauMonitorType =
//! DEBUGGER_HISTORY_ON`, which makes HermiT open an **interactive Swing debugger
//! window**: the user types `c` to continue, `showModel` / `showSubtree` /
//! `dertree clash` to inspect the tableau, etc. That interactive REPL + GUI
//! viewers (`ConsoleTextArea`, `DerivationViewer`, `SubtreeViewer`) are not
//! ported -- there is no headless way to "open a window and wait for keystrokes".
//!
//! What the port DOES expose is the non-GUI core of that package
//! (`hermit_rs::debugger`):
//!   * `DerivationHistory` -- how each derived fact was produced (the data behind
//!     `dertree`), and
//!   * `Debugger` -- the command registry/dispatch (`help`, `showDLClauses`,
//!     `showModel`, ...), which build their textual output as a `String` instead
//!     of painting a Swing window.
//!
//! This example demonstrates that core non-interactively: it reproduces the
//! exact `dertree clash` walkthrough from the Java comments (CheesyVegetableTopping
//! is unsatisfiable because CheeseTopping and VegetableTopping are disjoint) by
//! recording the derivation and printing the tree, and it lists the available
//! debugger commands via the dispatcher.
//!
//! Run with:  cargo run --example hermit_debugger

use hermit_rs::debugger::{Debugger, Derivation, DerivationHistory};

fn main() {
    // --- The non-GUI derivation history (the data behind `dertree clash`) -----
    // Mirrors the Java comment's worked example for CheesyVegetableTopping:
    //   :CheeseTopping(6)    <-- DL clause  :CheeseTopping(X) :- :CheesyVegetableTopping(X)
    //   :VegetableTopping(6) <-- DL clause  :VegetableTopping(X) :- :CheesyVegetableTopping(X)
    //   clash                <-- DL clause  :- :CheeseTopping(x), :VegetableTopping(x)
    let mut history = DerivationHistory::new();
    history.record(":CheesyVegetableTopping(6)", Derivation::BaseFact, vec![]);
    history.record(
        ":CheeseTopping(6)",
        Derivation::DLClauseApplication {
            dl_clause: ":CheeseTopping(X) :- :CheesyVegetableTopping(X)".into(),
        },
        vec![":CheesyVegetableTopping(6)".into()],
    );
    history.record(
        ":VegetableTopping(6)",
        Derivation::DLClauseApplication {
            dl_clause: ":VegetableTopping(X) :- :CheesyVegetableTopping(X)".into(),
        },
        vec![":CheesyVegetableTopping(6)".into()],
    );
    history.record(
        "clash",
        Derivation::DLClauseApplication {
            dl_clause: ":- :CheeseTopping(x), :VegetableTopping(x)".into(),
        },
        vec![":CheeseTopping(6)".into(), ":VegetableTopping(6)".into()],
    );

    println!("=== `dertree clash` (the derivation history of the clash) ===");
    print!("{}", history.derivation_tree("clash"));
    println!();

    // --- The command dispatcher (the `help` listing) --------------------------
    // In Java these run inside the interactive window; here the same commands
    // produce their text directly. `process_command_line("help")` is the headless
    // equivalent of typing `help` at the debugger's `>` prompt.
    let debugger = Debugger::new();
    println!("=== available debugger commands (the `help` command, non-interactively) ===");
    print!("{}", debugger.process_command_line("help"));
}
