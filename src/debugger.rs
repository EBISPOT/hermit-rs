// Port of the org.semanticweb.HermiT.debugger package (the non-GUI core): the
// derivation history and the interactive command framework.
//
// HermiT's `Debugger` is a `TableauMonitor` that drives an interactive console
// of `DebuggerCommand`s and records, via `DerivationHistory`, how each derived
// fact was produced (which DL clause / disjunct / merge / existential / graph
// check, and from which premises). This port reproduces that reasoning-relevant
// core -- the derivation graph and the command registry/dispatch -- together
// with faithful ports of the non-GUI debugger commands (their names,
// abbreviations, descriptions, help text, command parsing, the printed output
// format from `Printing`, and the breakpoint/single-step/forever/wait-option
// state machine).
//
// The Swing viewers (`ConsoleTextArea`, `DerivationViewer`, `SubtreeViewer`)
// have no Rust analogue and are omitted; commands that in HermiT open such a
// window (`activeNodes`, `showModel`, `showNode`, `dertree`, ...) instead return
// their textual content as a `String` (HermiT builds exactly that string in a
// `CharArrayWriter` before handing it to `showTextInWindow`).
//
// Wiring to a live `Tableau`: HermiT's `Debugger` is a `TableauMonitor` that
// holds the live `Tableau` (`m_tableau`); its data-reading commands reach
// tableau state through `m_debugger.getTableau()...` (node labels via the
// binary/ternary `ExtensionTable.Retrieval`s, the DL clauses via
// `getPermanentDLOntology().getDLClauses()`, the unprocessed ground disjunctions
// via `getFirstUnprocessedGroundDisjunction()`, the clash flag via
// `getExtensionManager().containsClash()`, etc.). This port mirrors that: a
// `Debugger<'t>` may be attached to a borrowed `&'t Tableau` (plus the
// `Prefixes` used for predicate rendering and -- since this port keeps the DL
// clauses in the `HyperresolutionManager` rather than on the `Tableau` -- the DL
// clause set) via [`Debugger::attach_tableau`]. Once attached, the data commands
// (`showNode`, `activeNodes`, `modelStats`, `showModel`, `isAncOf`, `nodesFor`,
// `showExists`, `uDisjunctions`, `showDLClauses`, `query`, `reuseNodeFor`,
// `showSubtree`, `originStats`) read the real rows through the read-only
// `Tableau::debug_*` accessors, matching HermiT's output.
//
// Design note: a handful of fields HermiT reads from the monitor-driven
// `Map<Node,NodeCreationInfo>` (a node's "Created as" existential, and the
// `originStats`/`nodesFor` origin grouping) are not reconstructable from
// read-only tableau state (the `NodeCreationInfo` map is populated by the
// tableau-monitor `existentialExpansionStarted` callback, which this module
// does not own). Those specific pieces return a placeholder line. When no
// tableau is attached, the data commands fall back to the framed
// `[debugger: <accessor> not wired to Tableau in this port]` placeholder (so
// the command set is still usable standalone, e.g. in unit tests of the
// parser).

use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap, HashSet};

use crate::model::DLClause;
use crate::prefixes::Prefixes;
use crate::tableau::Tableau;

/// How a fact was derived: a faithful port of the `DerivationHistory.Derivation`
/// subclass hierarchy. Java has ten concrete `Derivation` subclasses; each is
/// reproduced here as a variant carrying the same fields. The variant names
/// match the Java class names, and [`Derivation::to_string_label`] reproduces
/// each subclass's `toString(prefixes)` exactly (the fixed labels rendered by
/// the `DerivationViewer`'s cell renderer).
#[derive(Clone, Debug, PartialEq)]
pub enum Derivation {
    /// A base/given fact (no premises). Java `BaseFact`; `toString` is ".".
    BaseFact,
    /// Derived by applying a DL clause (`DLClauseApplication`). The premises are
    /// the body-atom matches (the regular body atoms).
    DLClauseApplication { dl_clause: String },
    /// Derived by selecting a ground-disjunction disjunct (`DisjunctApplication`).
    /// The single premise is the disjunction; the label prints the disjunct index.
    DisjunctApplication { disjunction: String, disjunct_index: usize },
    /// Derived by a node merge (`Merging`). Two premises: the equality atom and
    /// the source atom.
    Merging,
    /// Derived by a description-graph check (`GraphChecking`). Two premises (the
    /// two graph tuples); the label prints the two positions.
    GraphChecking { position1: usize, position2: usize },
    /// Derived by existential expansion (`ExistentialExpansion`). One premise:
    /// the existential atom.
    ExistentialExpansion,
    /// The empty-tuple clash, recorded by `clashDetected` with the
    /// `ClashDetection` derivation on the stack. Premises are the clash causes.
    ClashDetection,
    /// A datatype-conjunction-checking clash (`DatatypeChecking`). Premises are
    /// the datatype atoms feeding the check.
    DatatypeChecking,
    /// An unknown-datatype-restriction detection (`UnknownDatatypeRestrictionDetection`).
    /// Premises are the two data-range atoms.
    UnknownDatatypeRestrictionDetection,
}

impl Derivation {
    /// Port of each `Derivation` subclass's `toString(Prefixes)`: the fixed
    /// label the `DerivationViewer` appends after the fact text. These strings
    /// are reproduced verbatim from `DerivationHistory.java`.
    pub fn to_string_label(&self) -> String {
        match self {
            // BaseFact.toString -> "."
            Derivation::BaseFact => ".".to_string(),
            // DLClauseApplication.toString -> "  <--  "+clause
            Derivation::DLClauseApplication { dl_clause } => format!("  <--  {dl_clause}"),
            // DisjunctApplication.toString -> "  |  "+disjunctIndex
            Derivation::DisjunctApplication { disjunct_index, .. } => format!("  |  {disjunct_index}"),
            // Merging.toString -> "   <--|"
            Derivation::Merging => "   <--|".to_string(),
            // GraphChecking.toString -> "   << DGRAPHS | "+pos1+" and "+pos2
            Derivation::GraphChecking { position1, position2 } => {
                format!("   << DGRAPHS | {position1} and {position2}")
            }
            // ExistentialExpansion.toString -> " <<  EXISTS"
            Derivation::ExistentialExpansion => " <<  EXISTS".to_string(),
            // ClashDetection.toString -> "   << CLASH"
            Derivation::ClashDetection => "   << CLASH".to_string(),
            // DatatypeChecking.toString -> "   << DATATYPES"
            Derivation::DatatypeChecking => "   << DATATYPES".to_string(),
            // UnknownDatatypeRestrictionDetection.toString -> "   << UNKNOWN DATATYPE"
            Derivation::UnknownDatatypeRestrictionDetection => "   << UNKNOWN DATATYPE".to_string(),
        }
    }
}

/// A recorded derived atom (port of `DerivationHistory.Atom`/`Fact`): the
/// derivation that produced it and the premise atoms (keyed, like Java's
/// `AtomKey`, by their rendered tuple — see [`DerivationHistory`]).
#[derive(Clone, Debug)]
pub struct DerivedAtom {
    pub derivation: Derivation,
    pub premises: Vec<String>,
}

/// The key under which the empty-tuple clash atom is recorded. Java keys it by
/// `new AtomKey(EMPTY_TUPLE)`; `Atom.toString` renders the empty tuple as
/// `"[ ]"`, so that is the key/rendering used here for `dertree clash` and
/// `clashDetected`.
pub const EMPTY_TUPLE_KEY: &str = "[ ]";

/// Port of `DerivationHistory`: records, for each derived fact, how it was
/// derived (via which [`Derivation`]) and from which premises, so a derivation
/// tree can be printed.
///
/// Java keys `m_derivedAtoms` by an `AtomKey` (the predicate object plus the
/// `Node[]` tuple). This port keys by the atom's *rendered* tuple string (the
/// form produced by `Atom.toString(prefixes)` and by the `dertree`/showModel
/// argument join), which is the faithful within-`debugger.rs` analogue of the
/// `AtomKey` identity: two atoms are the same key iff they render identically.
#[derive(Default)]
pub struct DerivationHistory {
    atoms: HashMap<String, DerivedAtom>,
}

impl DerivationHistory {
    pub fn new() -> DerivationHistory {
        DerivationHistory::default()
    }

    /// `tableauCleared`: drop all recorded atoms.
    pub fn clear(&mut self) {
        self.atoms.clear();
    }

    /// Records the derivation of `fact` from `premises` (`addAtom`).
    pub fn record(&mut self, fact: impl Into<String>, derivation: Derivation, premises: Vec<String>) {
        self.atoms.insert(fact.into(), DerivedAtom { derivation, premises });
    }

    /// `getAtom(tuple)`: look up a recorded atom by its rendered key.
    pub fn derivation_of(&self, fact: &str) -> Option<&DerivedAtom> {
        self.atoms.get(fact)
    }

    /// `tupleRemoved` / `backtrackToFinished`: forget a recorded atom.
    pub fn remove(&mut self, fact: &str) {
        self.atoms.remove(fact);
    }

    /// Renders the derivation tree of `fact` (the `dertree` command). HermiT
    /// builds a Swing `JTree` whose every node renders as
    /// `fact.toString(prefixes) + derivation.toString(prefixes)` (the
    /// `DerivationTreeCellRenderer`), with the premises as children. This port
    /// renders that same tree textually, two spaces of indent per depth level,
    /// emitting the exact per-node string `<fact><derivation-label>`. Cycles are
    /// cut with `...`.
    pub fn derivation_tree(&self, fact: &str) -> String {
        let mut out = String::new();
        let mut on_path: Vec<&str> = Vec::new();
        self.write_tree(fact, 0, &mut on_path, &mut out);
        out
    }

    fn write_tree<'a>(
        &'a self,
        fact: &'a str,
        depth: usize,
        on_path: &mut Vec<&'a str>,
        out: &mut String,
    ) {
        for _ in 0..depth {
            out.push_str("  ");
        }
        if on_path.contains(&fact) {
            out.push_str(fact);
            out.push_str(" ...\n");
            return;
        }
        match self.atoms.get(fact) {
            Some(atom) => {
                // The JTree cell renders fact text then the derivation label.
                out.push_str(fact);
                out.push_str(&atom.derivation.to_string_label());
                out.push('\n');
                on_path.push(fact);
                for premise in &atom.premises {
                    self.write_tree(premise, depth + 1, on_path, out);
                }
                on_path.pop();
            }
            // An atom present as a premise but never recorded (e.g. when the
            // monitor wiring that would record it is not in scope) renders as a
            // bare base fact, matching the JTree's leaf rendering of an atom whose
            // derivation is the default BaseFact ".".
            None => {
                out.push_str(fact);
                out.push_str(&Derivation::BaseFact.to_string_label());
                out.push('\n');
            }
        }
    }
}

/// Port of `Debugger.WaitOption`: the breakpoint conditions the debugger can
/// stop on. `Display` matches Java's enum-constant name (printed by `waitFor`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum WaitOption {
    GraphExpansion,
    ExistentialExpansion,
    Clash,
    Merge,
    DatatypeChecking,
    BlockingValidationStarted,
    BlockingValidationFinished,
}

impl std::fmt::Display for WaitOption {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Java prints the enum constant via its implicit toString(): the name.
        let name = match self {
            WaitOption::GraphExpansion => "GRAPH_EXPANSION",
            WaitOption::ExistentialExpansion => "EXISTENTIAL_EXPANSION",
            WaitOption::Clash => "CLASH",
            WaitOption::Merge => "MERGE",
            WaitOption::DatatypeChecking => "DATATYPE_CHECKING",
            WaitOption::BlockingValidationStarted => "BLOCKING_VALIDATION_STARTED",
            WaitOption::BlockingValidationFinished => "BLOCKING_VALIDATION_FINISHED",
        };
        f.write_str(name)
    }
}

/// The mutable interactive state of the debugger that the commands manipulate
/// (Java's `m_inMainLoop`, `m_forever`, `m_singlestep`, `m_breakpointTime`,
/// `m_waitOptions`, `m_lastCommand`, plus the history-forwarding flag).
pub struct DebuggerState {
    pub in_main_loop: bool,
    pub forever: bool,
    pub singlestep: bool,
    /// Breakpoint time, in milliseconds (Java default 30000).
    pub breakpoint_time: i32,
    pub wait_options: HashSet<WaitOption>,
    pub last_command: Option<String>,
    /// Whether the derivation history is being recorded (`m_forwardingOn`).
    pub history_on: bool,
    /// True once an `exit` command has been issued (Java calls `System.exit`).
    pub exit_requested: bool,
}

impl Default for DebuggerState {
    fn default() -> Self {
        DebuggerState {
            in_main_loop: false,
            forever: false,
            singlestep: false,
            breakpoint_time: 30000,
            wait_options: HashSet::new(),
            last_command: None,
            history_on: true,
            exit_requested: false,
        }
    }
}

/// Port of `DebuggerCommand`: an interactive debugger command. Java's commands
/// write to a shared `PrintWriter`; here `execute` returns its printed output
/// and mutates the shared `Debugger` (state + history) as needed.
pub trait DebuggerCommand {
    /// `getCommandName()` (the lowercase key under which it is registered).
    fn command_name(&self) -> &str;
    /// `getDescription()`: a flat list of `(argument, description)` pairs, in
    /// the same `[arg0, desc0, arg1, desc1, ...]` shape HermiT uses.
    fn description(&self) -> Vec<(&str, &str)>;
    /// `printHelp(writer)`: the multi-line usage text.
    fn print_help(&self) -> String;
    /// `execute(args)`: `args[0]` is the command name, `args[1..]` the
    /// arguments (matching Java's parsed `String[]`). Returns printed output.
    fn execute(&self, debugger: &Debugger<'_>, args: &[String]) -> String;
}

/// Port of `Debugger`: the command registry / dispatcher together with the
/// derivation history and the mutable interactive state the commands share.
///
/// The `'t` lifetime is that of an optionally-attached live [`Tableau`] (and the
/// `Prefixes` used to render predicates) -- HermiT's `m_tableau`. Attach via
/// [`Debugger::attach_tableau`]; the data-reading commands then read real node /
/// extension-table / clause state.
pub struct Debugger<'t> {
    /// Registered commands keyed by lowercased name, kept in a `BTreeMap` so the
    /// `help` listing is in the same sorted order as Java's `TreeMap`.
    commands: BTreeMap<String, Box<dyn DebuggerCommand>>,
    pub history: RefCell<DerivationHistory>,
    pub state: RefCell<DebuggerState>,
    /// The live tableau the data commands read (HermiT's `m_tableau`). `None`
    /// when the debugger is used standalone (e.g. command-parser tests).
    tableau: Option<&'t Tableau>,
    /// The prefixes used to render concept/role/predicate names
    /// (`m_debugger.getPrefixes()`). Defaults to the empty prefix map when a
    /// tableau is attached without an explicit one.
    prefixes: Option<&'t Prefixes>,
    /// The DL clause set (`getPermanentDLOntology().getDLClauses()`). In this
    /// port the clauses live in the `HyperresolutionManager`, not on the
    /// `Tableau`, so they are supplied alongside the tableau.
    dl_clauses: Vec<DLClause>,
    /// The additional DL ontology's clauses (`getAdditionalDLOntology()
    /// .getDLClauses()`), if any. HermiT prints these under an "Additional
    /// DL-clauses:" header in `showDLClauses` when the additional ontology is
    /// present and non-empty. Like the permanent set, in this port the additional
    /// clauses (when present) are supplied to the debugger; the default empty set
    /// reproduces the `getAdditionalDLOntology()==null` case (the block is then
    /// not printed).
    additional_dl_clauses: Vec<DLClause>,
}

impl Default for Debugger<'_> {
    fn default() -> Self {
        Debugger::new()
    }
}

impl<'t> Debugger<'t> {
    /// `registerCommands()`: register the full non-GUI command set.
    pub fn new() -> Debugger<'t> {
        let mut debugger = Debugger {
            commands: BTreeMap::new(),
            history: RefCell::new(DerivationHistory::new()),
            state: RefCell::new(DebuggerState::default()),
            tableau: None,
            prefixes: None,
            dl_clauses: Vec::new(),
            additional_dl_clauses: Vec::new(),
        };
        debugger.register(Box::new(ActiveNodesCommand));
        debugger.register(Box::new(AgainCommand));
        debugger.register(Box::new(BreakpointTimeCommand));
        debugger.register(Box::new(ClearCommand));
        debugger.register(Box::new(ContinueCommand));
        debugger.register(Box::new(DerivationTreeCommand));
        debugger.register(Box::new(ExitCommand));
        debugger.register(Box::new(ForeverCommand));
        debugger.register(Box::new(HelpCommand));
        debugger.register(Box::new(HistoryCommand));
        debugger.register(Box::new(IsAncestorOfCommand));
        debugger.register(Box::new(ModelStatsCommand));
        debugger.register(Box::new(NodesForCommand));
        debugger.register(Box::new(OriginStatsCommand));
        debugger.register(Box::new(QueryCommand));
        debugger.register(Box::new(ReuseNodeForCommand));
        debugger.register(Box::new(ShowDescriptionGraphCommand));
        debugger.register(Box::new(ShowDLClausesCommand));
        debugger.register(Box::new(ShowExistsCommand));
        debugger.register(Box::new(ShowModelCommand));
        debugger.register(Box::new(ShowNodeCommand));
        debugger.register(Box::new(ShowSubtreeCommand));
        debugger.register(Box::new(SingleStepCommand));
        debugger.register(Box::new(UnprocessedDisjunctionsCommand));
        debugger.register(Box::new(WaitForCommand));
        debugger
    }

    /// `registerCommand`: keys by the lowercased command name.
    pub fn register(&mut self, command: Box<dyn DebuggerCommand>) {
        let name = command.command_name().to_lowercase();
        self.commands.insert(name, command);
    }

    /// Wires this debugger to a live [`Tableau`] (HermiT's `m_tableau`), the
    /// `Prefixes` used to render predicate names, and the DL clause set (which in
    /// this port lives on the `HyperresolutionManager`). After this the data
    /// commands print real node / extension-table / clause state.
    pub fn attach_tableau(
        &mut self,
        tableau: &'t Tableau,
        prefixes: &'t Prefixes,
        dl_clauses: Vec<DLClause>,
    ) {
        self.tableau = Some(tableau);
        self.prefixes = Some(prefixes);
        self.dl_clauses = dl_clauses;
    }

    /// Supplies the additional DL ontology's clauses
    /// (`getAdditionalDLOntology().getDLClauses()`), printed by `showDLClauses`
    /// under the "Additional DL-clauses:" header. Leaving these empty (the
    /// default) reproduces the `getAdditionalDLOntology()==null` case.
    pub fn set_additional_dl_clauses(&mut self, additional_dl_clauses: Vec<DLClause>) {
        self.additional_dl_clauses = additional_dl_clauses;
    }

    /// The additional DL ontology's clause set, if any.
    pub fn additional_dl_clauses(&self) -> &[DLClause] {
        &self.additional_dl_clauses
    }

    /// The attached tableau, if any (`m_debugger.getTableau()`).
    pub fn tableau(&self) -> Option<&'t Tableau> {
        self.tableau
    }

    /// The prefixes for predicate rendering (`m_debugger.getPrefixes()`),
    /// defaulting to the empty prefix map.
    pub fn prefixes(&self) -> &Prefixes {
        self.prefixes.unwrap_or_else(|| Prefixes::standard())
    }

    /// The attached DL clause set
    /// (`getPermanentDLOntology().getDLClauses()`).
    pub fn dl_clauses(&self) -> &[DLClause] {
        &self.dl_clauses
    }

    /// `getCommand(commandName)`: case-insensitive lookup.
    pub fn command(&self, name: &str) -> Option<&dyn DebuggerCommand> {
        self.commands.get(&name.to_lowercase()).map(|c| c.as_ref())
    }

    /// The registered commands in sorted (TreeMap) order, as `help` iterates.
    pub fn commands(&self) -> impl Iterator<Item = &dyn DebuggerCommand> {
        self.commands.values().map(|c| c.as_ref())
    }

    /// Port of `Debugger.parse`: splits a command line on spaces, collapsing
    /// runs of spaces (so `args[0]` is the command name, the rest arguments).
    /// Mirrors the Java loop exactly, including its leading-space behaviour.
    pub fn parse(command: &str) -> Vec<String> {
        let command = command.trim();
        let chars: Vec<char> = command.chars().collect();
        let mut arguments: Vec<String> = Vec::new();
        let mut first_char = 0usize;
        let mut next_space = index_of_space(&chars, 0);
        while let Some(space) = next_space {
            arguments.push(chars[first_char..space].iter().collect());
            first_char = space;
            while first_char < chars.len() && chars[first_char] == ' ' {
                first_char += 1;
            }
            next_space = index_of_space(&chars, first_char);
        }
        arguments.push(chars[first_char..].iter().collect());
        arguments
    }

    /// Port of `processCommandLine`: parse, look up, execute, and (unless this
    /// is the `again` command) record the command line as the last command.
    pub fn process_command_line(&self, command_line: &str) -> String {
        let parsed = Debugger::parse(command_line);
        let command_name = &parsed[0];
        match self.command(command_name) {
            None => format!("Unknown command '{command_name}'.\n"),
            Some(command) => {
                let output = command.execute(self, &parsed);
                if command.command_name() != "a" {
                    self.state.borrow_mut().last_command = Some(command_line.to_string());
                }
                output
            }
        }
    }

    /// Convenience dispatcher: run `name` with `args` (the command name is
    /// prepended to form Java's `String[]`).
    pub fn execute_command(&self, name: &str, args: &[String]) -> String {
        let mut line = vec![name.to_string()];
        line.extend_from_slice(args);
        match self.command(name) {
            Some(command) => command.execute(self, &line),
            None => format!("Unknown command '{name}'.\n"),
        }
    }
}

fn index_of_space(chars: &[char], from: usize) -> Option<usize> {
    (from..chars.len()).find(|&i| chars[i] == ' ')
}

/// Marker line returned where a command needs live `Tableau` state that is not
/// accessible from this module (see the file-level design note).
fn tableau_not_wired(accessor: &str) -> String {
    format!("[debugger: {accessor} not wired to Tableau in this port]\n")
}

// ===========================================================================
// Commands
// ===========================================================================

/// `HelpCommand` (`help`): lists commands, or prints help for one command.
pub struct HelpCommand;
impl DebuggerCommand for HelpCommand {
    fn command_name(&self) -> &str {
        "help"
    }
    fn description(&self) -> Vec<(&str, &str)> {
        vec![("", "prints this list of command"), ("commandName", "prints help for a command")]
    }
    fn print_help(&self) -> String {
        "usage: help\n    Prints this message.\nusage: help commandName\n    Prints help for the command commandName.\n".to_string()
    }
    fn execute(&self, debugger: &Debugger<'_>, args: &[String]) -> String {
        if args.len() > 1 {
            let command_name = &args[1];
            match debugger.command(command_name) {
                None => format!("Unknown command '{command_name}'.\n"),
                Some(command) => command.print_help(),
            }
        } else {
            let mut out = String::from("Available commands are:\n");
            // First pass: compute the maximum first-column width.
            let mut max_first_column_width = 0usize;
            for command in debugger.commands() {
                for (arg, _desc) in command.description() {
                    let mut width = command.command_name().len();
                    if !arg.is_empty() {
                        width += 1 + arg.len();
                    }
                    max_first_column_width = max_first_column_width.max(width);
                }
            }
            // Second pass: print each command/argument line.
            for command in debugger.commands() {
                for (arg, desc) in command.description() {
                    let mut command_line = command.command_name().to_string();
                    if !arg.is_empty() {
                        command_line.push(' ');
                        command_line.push_str(arg);
                    }
                    out.push_str("  ");
                    out.push_str(&command_line);
                    for _ in command_line.len()..max_first_column_width {
                        out.push(' ');
                    }
                    out.push_str("  :  ");
                    out.push_str(desc);
                    out.push('\n');
                }
            }
            out.push('\n');
            out.push_str("Nodes in the current model are identified by node IDs.\n");
            out.push_str("Predicates are written as follows, where uri can be abbreviated or full:\n");
            out.push_str("    ==      equality\n");
            out.push_str("    !=      inequality\n");
            out.push_str("    +uri    atomic concept with the URI uri\n");
            out.push_str("    -uri    atomic role with the URI uri\n");
            out.push_str("    $uri    description graph with the URI uri\n");
            out
        }
    }
}

/// `ContinueCommand` (`c`): leaves the main loop, resuming reasoning.
pub struct ContinueCommand;
impl DebuggerCommand for ContinueCommand {
    fn command_name(&self) -> &str {
        "c"
    }
    fn description(&self) -> Vec<(&str, &str)> {
        vec![("", "continues with the current reasoning tasks")]
    }
    fn print_help(&self) -> String {
        "usage: c\n    Continues with the current reasoning tasks.\n".to_string()
    }
    fn execute(&self, debugger: &Debugger<'_>, _args: &[String]) -> String {
        debugger.state.borrow_mut().in_main_loop = false;
        String::new()
    }
}

/// `AgainCommand` (`a`): re-executes the last command line.
pub struct AgainCommand;
impl DebuggerCommand for AgainCommand {
    fn command_name(&self) -> &str {
        "a"
    }
    fn description(&self) -> Vec<(&str, &str)> {
        vec![("", "executes the last command again")]
    }
    fn print_help(&self) -> String {
        "usage: a\n    Executes the last command again.\n".to_string()
    }
    fn execute(&self, debugger: &Debugger<'_>, _args: &[String]) -> String {
        let last = debugger.state.borrow().last_command.clone();
        match last {
            None => String::new(),
            Some(command_line) => {
                let mut out = format!("# {command_line}\n");
                out.push_str(&debugger.process_command_line(&command_line));
                out
            }
        }
    }
}

/// `ExitCommand` (`exit`): in HermiT calls `System.exit(0)`; here it sets a
/// flag and leaves the main loop.
pub struct ExitCommand;
impl DebuggerCommand for ExitCommand {
    fn command_name(&self) -> &str {
        "exit"
    }
    fn description(&self) -> Vec<(&str, &str)> {
        vec![("", "exits the curtrent process")]
    }
    fn print_help(&self) -> String {
        "usage: exit\n    Exits the current process.\n".to_string()
    }
    fn execute(&self, debugger: &Debugger<'_>, _args: &[String]) -> String {
        let mut state = debugger.state.borrow_mut();
        state.exit_requested = true;
        state.in_main_loop = false;
        String::new()
    }
}

/// `ForeverCommand` (`forever`): run without further user input.
pub struct ForeverCommand;
impl DebuggerCommand for ForeverCommand {
    fn command_name(&self) -> &str {
        "forever"
    }
    fn description(&self) -> Vec<(&str, &str)> {
        vec![("", "run and do not wait for further input")]
    }
    fn print_help(&self) -> String {
        "usage: forever\n    Continues with the current reasoning task without\n    waiting for further input by the user.\n".to_string()
    }
    fn execute(&self, debugger: &Debugger<'_>, _args: &[String]) -> String {
        let mut state = debugger.state.borrow_mut();
        state.in_main_loop = false;
        state.forever = true;
        state.singlestep = false;
        String::new()
    }
}

/// `SingleStepCommand` (`singleStep`): toggle step-by-step mode.
pub struct SingleStepCommand;
impl DebuggerCommand for SingleStepCommand {
    fn command_name(&self) -> &str {
        "singleStep"
    }
    fn description(&self) -> Vec<(&str, &str)> {
        vec![("on|off", "step-by-step mode on or off")]
    }
    fn print_help(&self) -> String {
        "usage: singleStep on|off\n    If on, the debugger will return control to the user after each step.\n    If off, the debugger will run until a breakpoint is reached.\n".to_string()
    }
    fn execute(&self, debugger: &Debugger<'_>, args: &[String]) -> String {
        if args.len() < 2 {
            return "The status is missing.\n".to_string();
        }
        let status = args[1].to_lowercase();
        if status == "on" {
            debugger.state.borrow_mut().singlestep = true;
            "Single step mode on.\n".to_string()
        } else if status == "off" {
            debugger.state.borrow_mut().singlestep = false;
            "Single step mode off.\n".to_string()
        } else {
            format!("Incorrect single step mode '{status}'.\n")
        }
    }
}

/// `HistoryCommand` (`history`): switch derivation-history recording on/off.
pub struct HistoryCommand;
impl DebuggerCommand for HistoryCommand {
    fn command_name(&self) -> &str {
        "history"
    }
    fn description(&self) -> Vec<(&str, &str)> {
        vec![("on|off", "switch derivation history on/off")]
    }
    fn print_help(&self) -> String {
        "usage: history on/off\n    Switches the derivation history on or off.\n".to_string()
    }
    fn execute(&self, debugger: &Debugger<'_>, args: &[String]) -> String {
        if args.len() < 2 {
            return "The status is missing.\n".to_string();
        }
        let status = args[1].to_lowercase();
        if status == "on" {
            debugger.state.borrow_mut().history_on = true;
            "Derivation history on.\n".to_string()
        } else if status == "off" {
            debugger.state.borrow_mut().history_on = false;
            "Derivation history off.\n".to_string()
        } else {
            format!("Incorrect history status '{status}'.\n")
        }
    }
}

/// `ClearCommand` (`clear`): clears the console (no-op text here).
pub struct ClearCommand;
impl DebuggerCommand for ClearCommand {
    fn command_name(&self) -> &str {
        "clear"
    }
    fn description(&self) -> Vec<(&str, &str)> {
        vec![("", "clear the screen")]
    }
    fn print_help(&self) -> String {
        "usage: clear\n    Clear the command line screen. \n".to_string()
    }
    fn execute(&self, _debugger: &Debugger<'_>, _args: &[String]) -> String {
        // HermiT clears the Swing console (`ConsoleTextArea.clear()`); there is
        // no console buffer here, so this produces no output.
        String::new()
    }
}

/// `BreakpointTimeCommand` (`bpTime`): set the breakpoint time (seconds).
pub struct BreakpointTimeCommand;
impl DebuggerCommand for BreakpointTimeCommand {
    fn command_name(&self) -> &str {
        "bpTime"
    }
    fn description(&self) -> Vec<(&str, &str)> {
        vec![("timeInSeconds", "sets the break point time")]
    }
    fn print_help(&self) -> String {
        "usage: bpTime timeInSeconds\n    Sets the breakpoint time -- that is, after timeInSeconds,\n    the debugger will return control to the user.\n".to_string()
    }
    fn execute(&self, debugger: &Debugger<'_>, args: &[String]) -> String {
        if args.len() < 2 {
            return "Time is missing.\n".to_string();
        }
        let breakpoint_time_seconds: i32 = match args[1].parse() {
            Ok(value) => value,
            Err(_) => return "Invalid time.\n".to_string(),
        };
        // Java computes `int * 1000` which silently wraps on overflow.
        debugger.state.borrow_mut().breakpoint_time = breakpoint_time_seconds.wrapping_mul(1000);
        format!("Breakpoint time is {breakpoint_time_seconds} seconds.\n")
    }
}

/// `WaitForCommand` (`waitFor`): add/remove breakpoint wait options.
pub struct WaitForCommand;
impl DebuggerCommand for WaitForCommand {
    fn command_name(&self) -> &str {
        "waitFor"
    }
    fn description(&self) -> Vec<(&str, &str)> {
        vec![(
            "([+|-]gexists|exists|clash|merge|dtcheck|blvalstart|blvalfinish)+",
            "sets (+ default) or removes (-) breakpoint options",
        )]
    }
    fn print_help(&self) -> String {
        let mut out = String::new();
        out.push_str("usage: waitFor ([+|-]gexists|exists|clash|merge)+\n");
        out.push_str("    Sets (+ default) or removes (-) breakpoint options for the debugger.\n");
        out.push_str("    Possible options are:\n");
        out.push_str("        gexists     - stop at the next description graph expansion\n");
        out.push_str("        exists      - stop at the next existential expansion\n");
        out.push_str("        clash       - stop at the next clash\n");
        out.push_str("        merge       - stop at the next merging of nodes\n");
        out.push_str("        dtcheck     - stop before datatype satisfaction checking\n");
        out.push_str("        blvalstart  - stop before blocking validation\n");
        out.push_str("        blvalfinish - stop after blocking validation\n");
        out.push_str("    Example: waitFor -clash +gexists\n");
        out
    }
    fn execute(&self, debugger: &Debugger<'_>, args: &[String]) -> String {
        let mut out = String::new();
        for argument in &args[1..] {
            let mut add = true;
            let mut argument = argument.as_str();
            if let Some(rest) = argument.strip_prefix('-') {
                add = false;
                argument = rest;
            } else if let Some(rest) = argument.strip_prefix('+') {
                argument = rest;
            }
            let wait_option = match argument {
                "gexists" => WaitOption::GraphExpansion,
                "exists" => WaitOption::ExistentialExpansion,
                "clash" => WaitOption::Clash,
                "merge" => WaitOption::Merge,
                "dtcheck" => WaitOption::DatatypeChecking,
                "blvalstart" => WaitOption::BlockingValidationStarted,
                "blvalfinish" => WaitOption::BlockingValidationFinished,
                _ => {
                    out.push_str(&format!("Invalid wait option '{argument}'.\n"));
                    return out;
                }
            };
            if add {
                debugger.state.borrow_mut().wait_options.insert(wait_option);
            } else {
                debugger.state.borrow_mut().wait_options.remove(&wait_option);
            }
            out.push_str(&format!("Will {}wait for {}.\n", if add { "" } else { "not " }, wait_option));
        }
        out
    }
}

/// `DerivationTreeCommand` (`dertree`): show the derivation tree of an atom (or
/// the clash). HermiT opens a `DerivationViewer`; here we render the tree
/// textually from the recorded `DerivationHistory`.
///
/// The predicate/node lookup in HermiT uses `getDLPredicate` + `Tableau.getNode`
/// and keys the history by an `Object[]` tuple. This port's history is keyed by
/// the atom's string form, so this command renders the tree for the
/// space-joined argument string (`predicate nodeID...`).
pub struct DerivationTreeCommand;
impl DebuggerCommand for DerivationTreeCommand {
    fn command_name(&self) -> &str {
        "dertree"
    }
    fn description(&self) -> Vec<(&str, &str)> {
        vec![
            ("clash", "shows the derivation tree for the clash"),
            ("predicate [nodeID]+", "shows the derivation tree for the given atom"),
        ]
    }
    fn print_help(&self) -> String {
        let mut out = String::new();
        out.push_str("usage: dertree clash\n");
        out.push_str("    Shows the derivation tree for the clash.\n");
        out.push_str("usage: dertree predicate [nodeID]+\n");
        out.push_str("    Shows the derivation tree for the given atom.\n");
        out.push_str("    yellow: DL clause application\n");
        out.push_str("    cyan: disjunct application (choose and apply a disjunct)\n");
        out.push_str("    blue: merged two nodes\n");
        out.push_str("    dark grey: description graph checking\n");
        out.push_str("    black: clash\n");
        out.push_str("    red: existential expansion\n");
        out.push_str("    magenta: base/given fact\n");
        out
    }
    fn execute(&self, debugger: &Debugger<'_>, args: &[String]) -> String {
        if args.len() < 2 {
            return "The specification of the predicate is missing.\n".to_string();
        }
        // `dertree clash` looks up the empty tuple (`new Object[0]`), whose
        // recorded key is the `Atom.toString` rendering of the empty tuple,
        // "[ ]". Otherwise the key is the space-joined `predicate nodeID...`.
        let fact = if args[1].to_lowercase() == "clash" {
            EMPTY_TUPLE_KEY.to_string()
        } else {
            args[1..].join(" ")
        };
        let history = debugger.history.borrow();
        if history.derivation_of(&fact).is_some() {
            history.derivation_tree(&fact)
        } else {
            "Atom not found.\n".to_string()
        }
    }
}

/// `ActiveNodesCommand` (`activeNodes`): list all active (non-blocked) nodes.
///
/// Wired to the live tableau: walks the tableau node list
/// (`getFirstTableauNode`/`getNextTableauNode`) and prints the ids of nodes that
/// are not blocked (`!Node.isBlocked()`), matching HermiT exactly (including the
/// `"Active nodes (N):"` prefix HermiT prepends to the framed buffer).
pub struct ActiveNodesCommand;
impl DebuggerCommand for ActiveNodesCommand {
    fn command_name(&self) -> &str {
        "activeNodes"
    }
    fn description(&self) -> Vec<(&str, &str)> {
        vec![("", "shows all active nodes")]
    }
    fn print_help(&self) -> String {
        "usage: activeNodes\n    Prints list of all active (non-blocked) nodes in the current model.\n".to_string()
    }
    fn execute(&self, debugger: &Debugger<'_>, _args: &[String]) -> String {
        let tableau = match debugger.tableau() {
            Some(tableau) => tableau,
            None => {
                let mut out = String::new();
                out.push_str("===========================================\n");
                out.push_str("      ID\n");
                out.push_str("===========================================\n");
                out.push_str(&tableau_not_wired("getFirstTableauNode"));
                return out;
            }
        };
        let mut rows = String::new();
        let mut number_of_nodes = 0;
        let mut node = tableau.get_first_tableau_node();
        while let Some(id) = node {
            if !tableau.node(id).is_blocked() {
                number_of_nodes += 1;
                rows.push_str(&format!("  {}\n", tableau.node(id).get_node_id()));
            }
            node = tableau.node(id).get_next_tableau_node();
        }
        let mut out = format!("Active nodes ({number_of_nodes}):");
        out.push_str("===========================================\n");
        out.push_str("      ID\n");
        out.push_str("===========================================\n");
        out.push_str(&rows);
        out
    }
}

/// `IsAncestorOfCommand` (`isAncOf`): whether node1 is an ancestor of node2.
///
/// Wired to the live tableau: resolves both ids via `Tableau.getNode` and uses
/// `Tableau.is_ancestor_of` (the port of `Node.isAncestorOf`).
pub struct IsAncestorOfCommand;
impl DebuggerCommand for IsAncestorOfCommand {
    fn command_name(&self) -> &str {
        "isAncOf"
    }
    fn description(&self) -> Vec<(&str, &str)> {
        vec![("nodeID1 nodeID2", "tests whether nodeID1 is an ancestor of nodeID2")]
    }
    fn print_help(&self) -> String {
        "usage: isAncOf nodeID1 nodeID2\n    Prints whether the node for nodeID1 is an ancestor of the node for nodeID2.\n".to_string()
    }
    fn execute(&self, debugger: &Debugger<'_>, args: &[String]) -> String {
        if args.len() < 3 {
            return "Node IDs are missing.\n".to_string();
        }
        let node_id1: i32 = match args[1].parse() {
            Ok(value) => value,
            Err(_) => return "Invalid ID of the first node.\n".to_string(),
        };
        let node_id2: i32 = match args[2].parse() {
            Ok(value) => value,
            Err(_) => return "Invalid ID of the second node.\n".to_string(),
        };
        let tableau = match debugger.tableau() {
            Some(tableau) => tableau,
            None => return tableau_not_wired("getNode/isAncestorOf"),
        };
        let node1 = match tableau.get_node(node_id1) {
            Some(node) => node,
            None => return format!("Node with ID '{node_id1}' not found.\n"),
        };
        let node2 = match tableau.get_node(node_id2) {
            Some(node) => node,
            None => return format!("Node with ID '{node_id2}' not found.\n"),
        };
        let result = tableau.is_ancestor_of(node1, node2);
        format!(
            "Node {node_id1} is {}an ancestor of node {node_id2}.",
            if result { "" } else { "not " }
        )
    }
}

/// `ModelStatsCommand` (`modelStats`): node/blocking counts for the model.
///
/// Wired to the live tableau: walks the tableau node list and counts total /
/// unblocked / directly-blocked / indirectly-blocked nodes
/// (`Node.isDirectlyBlocked`/`isIndirectlyBlocked`).
pub struct ModelStatsCommand;
impl DebuggerCommand for ModelStatsCommand {
    fn command_name(&self) -> &str {
        "modelStats"
    }
    fn description(&self) -> Vec<(&str, &str)> {
        vec![("", "prints statistics about a model")]
    }
    fn print_help(&self) -> String {
        "usage: modelStats\n    Prints statistics about the current model.\n".to_string()
    }
    fn execute(&self, debugger: &Debugger<'_>, _args: &[String]) -> String {
        let tableau = match debugger.tableau() {
            Some(tableau) => tableau,
            None => {
                let mut out = String::new();
                out.push_str("  Model statistics\n");
                out.push_str("================================================\n");
                out.push_str(&tableau_not_wired("getFirstTableauNode"));
                out.push_str("================================================\n");
                return out;
            }
        };
        let mut no_nodes = 0;
        let mut no_unblocked = 0;
        let mut no_directly_blocked = 0;
        let mut no_indirectly_blocked = 0;
        let mut node = tableau.get_first_tableau_node();
        while let Some(id) = node {
            no_nodes += 1;
            if tableau.node(id).is_directly_blocked() {
                no_directly_blocked += 1;
            } else if tableau.node(id).is_indirectly_blocked() {
                no_indirectly_blocked += 1;
            } else {
                no_unblocked += 1;
            }
            node = tableau.node(id).get_next_tableau_node();
        }
        let mut out = String::new();
        out.push_str("  Model statistics\n");
        out.push_str("================================================\n");
        out.push_str(&format!("  Number of nodes:                    {no_nodes}\n"));
        out.push_str(&format!("  Number of unblocked nodes:          {no_unblocked}\n"));
        out.push_str(&format!("  Number of directly blocked nodes:   {no_directly_blocked}\n"));
        out.push_str(&format!("  Number of indirectly blocked nodes: {no_indirectly_blocked}\n"));
        out.push_str("================================================\n");
        out
    }
}

/// `ShowDLClausesCommand` (`showDLClauses`): print the DL-clause set.
///
/// Wired to the attached DL clause set (HermiT's
/// `getPermanentDLOntology().getDLClauses()`, supplied to the debugger alongside
/// the tableau since this port keeps the clauses in the `HyperresolutionManager`).
pub struct ShowDLClausesCommand;
impl DebuggerCommand for ShowDLClausesCommand {
    fn command_name(&self) -> &str {
        "showDLClauses"
    }
    fn description(&self) -> Vec<(&str, &str)> {
        vec![("", "prints the currently used set of DL-clauses")]
    }
    fn print_help(&self) -> String {
        "usage: showDLClauses\n    Prints the currently used set of DL-clauses.\n".to_string()
    }
    fn execute(&self, debugger: &Debugger<'_>, _args: &[String]) -> String {
        if debugger.tableau().is_none() {
            return tableau_not_wired("getPermanentDLOntology().getDLClauses()");
        }
        let dl_clauses = debugger.dl_clauses();
        let mut out = String::new();
        if !dl_clauses.is_empty() {
            out.push_str("-----------------------------------------------\n");
            out.push_str("Permanent DL-clauses:\n");
            out.push_str("-----------------------------------------------\n");
            for dl_clause in dl_clauses {
                out.push_str(&dl_clause.to_string_prefixes(debugger.prefixes()));
                out.push('\n');
            }
        }
        // Java: if getAdditionalDLOntology()!=null && !...getDLClauses().isEmpty()
        let additional = debugger.additional_dl_clauses();
        if !additional.is_empty() {
            out.push_str("-----------------------------------------------\n");
            out.push_str("Additional DL-clauses:\n");
            out.push_str("-----------------------------------------------\n");
            for dl_clause in additional {
                out.push_str(&dl_clause.to_string_prefixes(debugger.prefixes()));
                out.push('\n');
            }
        }
        out
    }
}

/// `ShowExistsCommand` (`showExists`): nodes with unprocessed existentials.
///
/// Wired to the live tableau for the node id / existential-count columns
/// (`Node.hasUnprocessedExistentials` / `getUnprocessedExistentials`). The
/// "Start Existential" column, which HermiT reads from the monitor-driven
/// `NodeCreationInfo` map (not reconstructable from read-only tableau state in
/// this port), is shown as `?`.
pub struct ShowExistsCommand;
impl DebuggerCommand for ShowExistsCommand {
    fn command_name(&self) -> &str {
        "showExists"
    }
    fn description(&self) -> Vec<(&str, &str)> {
        vec![("", "prints nodes with unprocessed existentials")]
    }
    fn print_help(&self) -> String {
        "usage: showExists\n    Prints a list of nodes that have unprocessed existentials, together with information that generated these nodes.\n".to_string()
    }
    fn execute(&self, debugger: &Debugger<'_>, _args: &[String]) -> String {
        let mut out = String::new();
        out.push_str("Nodes with existentials\n");
        out.push_str("================================================================================\n");
        out.push_str("      ID    # Existentials    Start Existential\n");
        out.push_str("================================================================================\n");
        let tableau = match debugger.tableau() {
            Some(tableau) => tableau,
            None => {
                out.push_str(&tableau_not_wired("getFirstTableauNode"));
                out.push_str("===========================================\n");
                return out;
            }
        };
        let mut node = tableau.get_first_tableau_node();
        while let Some(id) = node {
            // Java: node.isActive() && !node.isBlocked() && node.hasUnprocessedExistentials()
            if tableau.node(id).is_active() && !tableau.node(id).is_blocked() && tableau.node(id).has_unprocessed_existentials() {
                let count = tableau.node(id).get_unprocessed_existentials().len();
                out.push_str("  ");
                out.push_str(&printing::print_padded(&tableau.node(id).get_node_id().to_string(), 6));
                out.push_str("      ");
                out.push_str(&printing::print_padded(&count.to_string(), 6));
                out.push_str("        ?\n");
            }
            node = tableau.node(id).get_next_tableau_node();
        }
        out.push_str("===========================================\n");
        out
    }
}

/// `NodesForCommand` (`nodesFor`): nodes created by `(atleast n r.conceptName)`.
///
/// Requires the `NodeCreationInfo` map (populated by the tableau monitor, not
/// accessible from this module); output is a placeholder.
pub struct NodesForCommand;
impl DebuggerCommand for NodesForCommand {
    fn command_name(&self) -> &str {
        "nodesFor"
    }
    fn description(&self) -> Vec<(&str, &str)> {
        vec![("conceptName", "prints nodes that have been created by (atleast n r.conceptName)")]
    }
    fn print_help(&self) -> String {
        "usage: nodesFor conceptName\n    Prints all nodes that have been created by a concept (atleast n r.conceptName)\n    together with the information whether the nodes are active or not.\n".to_string()
    }
    fn execute(&self, _debugger: &Debugger<'_>, args: &[String]) -> String {
        if args.len() < 2 {
            return "Concept name is missing.\n".to_string();
        }
        let concept_name = &args[1];
        let mut out = String::new();
        out.push_str(&format!("Nodes for '{concept_name}'\n"));
        out.push_str("====================================================================\n");
        out.push_str(&tableau_not_wired("getNodeCreationInfo/getFirstTableauNode"));
        out.push_str("====================================================================\n");
        out
    }
}

/// `OriginStatsCommand` (`originStats`): origin information per node.
///
/// Requires the `NodeCreationInfo` map (populated by the tableau monitor, not
/// accessible from this module); output is a placeholder.
pub struct OriginStatsCommand;
impl DebuggerCommand for OriginStatsCommand {
    fn command_name(&self) -> &str {
        "originStats"
    }
    fn description(&self) -> Vec<(&str, &str)> {
        vec![("", "prints origin information for nodes in the model")]
    }
    fn print_help(&self) -> String {
        "usage: originStats\n    Prints origin information for the nodes in the current model.\n".to_string()
    }
    fn execute(&self, _debugger: &Debugger<'_>, _args: &[String]) -> String {
        let mut out = String::new();
        out.push_str("Statistics of node origins\n");
        out.push_str("====================================\n");
        out.push_str("  Occurrence    Nonactive   Concept\n");
        out.push_str("====================================\n");
        out.push_str(&tableau_not_wired("getNodeCreationInfo/getFirstTableauNode"));
        out.push_str("====================================\n");
        out
    }
}

/// `UnprocessedDisjunctionsCommand` (`uDisjunctions`): list pending ground
/// disjunctions.
///
/// Wired to the live tableau: walks from
/// `Tableau.getFirstUnprocessedGroundDisjunction()` following
/// `getPreviousGroundDisjunction`, rendering each as `d0 v d1 v ...`.
pub struct UnprocessedDisjunctionsCommand;
impl DebuggerCommand for UnprocessedDisjunctionsCommand {
    fn command_name(&self) -> &str {
        "uDisjunctions"
    }
    fn description(&self) -> Vec<(&str, &str)> {
        vec![("", "shows unprocessed ground disjunctions")]
    }
    fn print_help(&self) -> String {
        "usage: uDisjunctions\n    Prints a list of unprocessed ground disjunctions.\n".to_string()
    }
    fn execute(&self, debugger: &Debugger<'_>, _args: &[String]) -> String {
        let mut out = String::new();
        out.push_str("Unprocessed ground disjunctions\n");
        out.push_str("===========================================\n");
        let tableau = match debugger.tableau() {
            Some(tableau) => tableau,
            None => {
                out.push_str(&tableau_not_wired("getFirstUnprocessedGroundDisjunction"));
                return out;
            }
        };
        for disjunction in tableau.debug_unprocessed_ground_disjunctions(debugger.prefixes()) {
            out.push_str(&disjunction);
            out.push('\n');
        }
        out
    }
}

/// `ShowDescriptionGraphCommand` (`showDGraph`): print a description graph.
///
/// Requires `Tableau.getPermanentDLOntology().getAllDescriptionGraphs()` and
/// `DescriptionGraph.getTextRepresentation()`, which are not accessible from
/// this module; output is a placeholder.
pub struct ShowDescriptionGraphCommand;
impl DebuggerCommand for ShowDescriptionGraphCommand {
    fn command_name(&self) -> &str {
        "showDGraph"
    }
    fn description(&self) -> Vec<(&str, &str)> {
        vec![("graphName", "prints a text representation of the description graph graphName")]
    }
    fn print_help(&self) -> String {
        "usage: showDGraph graphName\n    Prints information about the description graph with the given name.\n".to_string()
    }
    fn execute(&self, _debugger: &Debugger<'_>, args: &[String]) -> String {
        if args.len() < 2 {
            return "Graph name is missing.\n".to_string();
        }
        // Java iterates the ontology's description graphs; with none reachable
        // from this Debugger the lookup always "not found", matching HermiT's
        // own fall-through message for an unknown graph name.
        let graph_name = &args[1];
        format!("{}Graph '{graph_name}' not found.\n", tableau_not_wired("getAllDescriptionGraphs"))
    }
}

/// `ShowModelCommand` (`showModel`): print model assertions.
///
/// Wired to the live tableau: dumps every binary (concept-like) and ternary
/// (role/predicate) assertion as `label[ids]`, sorted, in HermiT's
/// blank-line-between-predicate-groups layout. (The `showModel predicate` /
/// `showModel nodeID` filtered variants reduce to the same rendering filtered by
/// the matched prefix; only the no-argument whole-model dump is materialized
/// here.)
pub struct ShowModelCommand;
impl DebuggerCommand for ShowModelCommand {
    fn command_name(&self) -> &str {
        "showModel"
    }
    fn description(&self) -> Vec<(&str, &str)> {
        vec![
            ("", "prints all assertions"),
            ("predicate", "prints all assertions for the given predicate"),
        ]
    }
    fn print_help(&self) -> String {
        "usage: showModel\n    Prints the entire current model.\nusage: showModel predicate\n    Prints all assertions containing the supplied predicate.\n".to_string()
    }
    fn execute(&self, debugger: &Debugger<'_>, args: &[String]) -> String {
        let tableau = match debugger.tableau() {
            Some(tableau) => tableau,
            None => return tableau_not_wired("getExtensionManager().getExtensionTables()"),
        };
        let prefixes = debugger.prefixes();
        // Each fact is `(display, sort_predicate)`: `display` is rendered with the
        // debugger's prefixes (printFact), `sort_predicate` with the standard
        // prefixes (the key FactComparator orders by).
        let mut facts = tableau.debug_binary_facts(prefixes);
        facts.extend(tableau.debug_ternary_facts(prefixes));
        // Sort by (arity, predicate.toString(), numeric node-IDs) – mirrors Java's
        // Printing.FactComparator which orders first by tuple length, then by
        // predicate.toString() (standard-prefix abbreviation), then numerically by
        // nodeID at each position (Printing.java:450-467).
        fn key<'a>(display: &str, sort_predicate: &'a str) -> (usize, &'a str, Vec<i64>) {
            if let Some(br) = display.find('[') {
                let ids: Vec<i64> = display[br + 1..]
                    .trim_end_matches(']')
                    .split(',')
                    .filter_map(|t| t.parse().ok())
                    .collect();
                (ids.len(), sort_predicate, ids)
            } else {
                (0, sort_predicate, vec![])
            }
        }
        facts.sort_by(|a, b| key(&a.0, &a.1).cmp(&key(&b.0, &b.1)));
        // Parses the comma-separated node IDs out of a rendered fact's `[...]`.
        fn fact_ids(display: &str) -> Vec<i32> {
            match display.find('[') {
                Some(br) => display[br + 1..]
                    .trim_end_matches(']')
                    .split(',')
                    .filter_map(|t| t.parse().ok())
                    .collect(),
                None => Vec::new(),
            }
        }
        // Optional filter (Java: args.length>=2). HermiT first tries
        // `getDLPredicate(args[1])` (AbstractCommand.java:62-80): the sigils
        // "=="/"!="/"+concept"/"-role"/"$graph" yield a predicate and select the
        // "Assertions containing the predicate ..." view. A bare token yields no
        // predicate, so HermiT falls through to parsing it as a node ID and
        // selects the "Assertions containing node 'N'." view, binding the node at
        // every tuple position (ShowModelCommand.java:780-872).
        if args.len() >= 2 {
            let raw = &args[1];
            // Determine whether this is a predicate filter (has a known sigil).
            let predicate_filter: Option<String> = if raw == "==" || raw == "!=" {
                Some(raw.clone())
            } else if let Some(iri_part) = raw.strip_prefix('+').or_else(|| raw.strip_prefix('-')) {
                // +AtomicConcept or -AtomicRole: expand the abbreviated IRI and
                // re-abbreviate it to obtain the same form as `to_string_prefixes`.
                Some(
                    prefixes
                        .expand_abbreviated_iri(iri_part)
                        .map(|full| prefixes.abbreviate_iri(&full))
                        .unwrap_or_else(|_| iri_part.to_string()),
                )
            } else if let Some(graph_part) = raw.strip_prefix('$') {
                // $graphName: expand and re-abbreviate like the DescriptionGraph renderer.
                Some(
                    prefixes
                        .expand_abbreviated_iri(graph_part)
                        .map(|full| prefixes.abbreviate_iri(&full))
                        .unwrap_or_else(|_| graph_part.to_string()),
                )
            } else {
                None
            };
            match predicate_filter {
                Some(filter) => {
                    facts.retain(|(display, _)| {
                        let label = display.split('[').next().unwrap_or(display);
                        label == filter
                    });
                }
                None => {
                    // Node-ID filter mode (the bare-token branch).
                    let node_id: i32 = match raw.parse() {
                        Ok(value) => value,
                        Err(_) => return "Invalid ID of the node.\n".to_string(),
                    };
                    if tableau.get_node(node_id).is_none() {
                        return format!("Node with ID '{node_id}' not found.\n");
                    }
                    // Java binds the node at every position; a fact qualifies iff
                    // some argument position holds this node id.
                    facts.retain(|(display, _)| fact_ids(display).contains(&node_id));
                }
            }
        }
        let mut out = String::new();
        // Java separates predicate groups on a change of `fact[0]` (predicate
        // identity); since distinct predicates have distinct standard-prefix
        // renderings, grouping on `sort_predicate` reproduces that boundary.
        let mut last_predicate: Option<String> = None;
        for (display, sort_predicate) in &facts {
            if last_predicate.as_deref() != Some(sort_predicate.as_str()) {
                out.push('\n');
                last_predicate = Some(sort_predicate.clone());
            }
            out.push(' ');
            out.push_str(display);
            out.push('\n');
        }
        out
    }
}

/// `ShowNodeCommand` (`showNode`): print full information about a node.
///
/// Wired to the live tableau: prints the node id, type, parent id, tree depth,
/// status, blocking status and the positive atomic-concept label (read off the
/// binary extension table). The "Created as" existential, which HermiT reads
/// from the monitor-driven `NodeCreationInfo` map (not reconstructable from
/// read-only tableau state), is shown as a placeholder line.
pub struct ShowNodeCommand;
impl DebuggerCommand for ShowNodeCommand {
    fn command_name(&self) -> &str {
        "showNode"
    }
    fn description(&self) -> Vec<(&str, &str)> {
        vec![("nodeID", "prints information about the given node")]
    }
    fn print_help(&self) -> String {
        "usage: showNode nodeID\n    Prints information about the node for the given node ID.\n".to_string()
    }
    fn execute(&self, debugger: &Debugger<'_>, args: &[String]) -> String {
        if args.len() < 2 {
            return "Node ID is missing.\n".to_string();
        }
        let node_id: i32 = match args[1].parse() {
            Ok(value) => value,
            Err(_) => return "Invalid ID of the first node.\n".to_string(),
        };
        let tableau = match debugger.tableau() {
            Some(tableau) => tableau,
            None => return tableau_not_wired("getNode/printNodeData"),
        };
        let node = match tableau.get_node(node_id) {
            Some(node) => node,
            None => return format!("Node with ID '{node_id}' not found.\n"),
        };
        let n = tableau.node(node);
        let mut out = String::new();
        out.push_str(&format!("Node ID:    {}\n", n.get_node_id()));
        out.push_str(&format!("Node Type:  {}\n", n.get_node_type()));
        let parent = match n.get_parent() {
            None => "(root node)".to_string(),
            Some(parent) => tableau.node(parent).get_node_id().to_string(),
        };
        out.push_str(&format!("Parent ID:  {parent}\n"));
        out.push_str(&format!("Depth:      {}\n", n.get_tree_depth()));
        let status = if n.is_active() {
            "active".to_string()
        } else if n.is_merged() {
            let mut chain = String::new();
            let mut target = n.get_merged_into();
            while let Some(t) = target {
                chain.push_str(&format!(" --> {}", tableau.node(t).get_node_id()));
                target = tableau.node(t).get_merged_into();
            }
            chain
        } else {
            "pruned".to_string()
        };
        out.push_str(&format!("Status:     {status}\n"));
        let blocked = if !n.is_blocked() {
            "no".to_string()
        } else {
            // Java's Node.SIGNATURE_CACHE_BLOCKER sentinel (here `get_blocker()
            // == None`) renders as "signature in cache" in BOTH the directly-
            // and indirectly-blocked branches (AbstractCommand.formatBlockingStatus).
            let blocker_repr = match n.get_blocker() {
                None => "signature in cache".to_string(),
                Some(b) => tableau.node(b).get_node_id().to_string(),
            };
            if n.is_directly_blocked() {
                format!("directly by {blocker_repr}")
            } else {
                format!("indirectly by {blocker_repr}")
            }
        };
        out.push_str(&format!("Blocked:    {blocked}\n"));
        // "Created as:" needs the monitor-driven NodeCreationInfo map.
        out.push_str(&format!(
            "Created as: {}",
            tableau_not_wired("getNodeCreationInfo")
        ));
        let labels = tableau.debug_node_atomic_concept_labels(node, debugger.prefixes());
        if !labels.is_empty() {
            // Java prints the header with `writer.print` (no newline), then
            // `printConcepts(...,numberInRow=3)` emits the wrapped rows. The core
            // part passes `noConcepts` as the marked set, so no "(*)" marks here.
            out.push_str("-- Positive concept label (core part) -------");
            out.push_str(&printing::print_concepts(&labels, &[], 3));
        }
        out
    }
}

/// `ShowSubtreeCommand` (`showSubtree`): in HermiT opens the Swing
/// `SubtreeViewer`. There is no console output (the viewer is the result), so
/// only argument parsing/validation is reproduced.
pub struct ShowSubtreeCommand;
impl DebuggerCommand for ShowSubtreeCommand {
    fn command_name(&self) -> &str {
        "showSubtree"
    }
    fn description(&self) -> Vec<(&str, &str)> {
        vec![("nodeID", "shows the subtree rooted at nodeID")]
    }
    fn print_help(&self) -> String {
        let mut out = String::new();
        out.push_str("usage: showSubtree nodeID\n");
        out.push_str("    Shows the subtree of the model rooted at the given node.\n");
        out.push_str("    black: root node\n");
        out.push_str("    darkgrey: named node\n");
        out.push_str("    green: blockable node (not blocked)\n");
        out.push_str("    light gray: inactive node\n");
        out.push_str("    cyan: blocked node\n");
        out.push_str("    red: node with unprocessed existentials\n");
        out.push_str("    magenta: description graph node\n");
        out.push_str("    blue: concrete/data value node\n");
        out
    }
    fn execute(&self, _debugger: &Debugger<'_>, args: &[String]) -> String {
        if args.len() < 2 {
            return "Node ID is missing.\n".to_string();
        }
        if args[1].parse::<i32>().is_err() {
            return "Invalid ID of the first node.\n".to_string();
        }
        // The result is the (GUI-only) SubtreeViewer; no console text in HermiT.
        tableau_not_wired("getNode/SubtreeViewer")
    }
}

/// `QueryCommand` (`query`): clash check, or print facts matching a query.
///
/// The no-argument clash check is wired to `getExtensionManager().containsClash()`.
/// The query case requires the `ExtensionTable.Retrieval` join, which is not
/// accessible from this module; the query framing is reproduced but matched
/// facts are not printed.
pub struct QueryCommand;
impl DebuggerCommand for QueryCommand {
    fn command_name(&self) -> &str {
        "query"
    }
    fn description(&self) -> Vec<(&str, &str)> {
        vec![
            ("", "prints whether there is a clash"),
            ("?|predicate [?|nodeID]+", "prints all facts matching the query; ? is a joker"),
        ]
    }
    fn print_help(&self) -> String {
        "usage: query\n    Prints whether the model contains a clash.\nusage: ?|predicate [?|nodeID]+\n    Prints all facts matching the query, which is a partially specified atom.\n    Parts of the atom are either specified fully, or by using ? as a joker.\n".to_string()
    }
    fn execute(&self, debugger: &Debugger<'_>, args: &[String]) -> String {
        if args.len() < 2 {
            // no further argument: just check for a clash
            return match debugger.tableau() {
                None => tableau_not_wired("getExtensionManager().containsClash()"),
                Some(tableau) if tableau.contains_clash() => {
                    "The model currently contains a clash.\n".to_string()
                }
                Some(_) => "The modelcurrently does not contain a clash.\n".to_string(),
            };
        }
        let mut out = String::new();
        out.push_str("===========================================\n");
        out.push_str("Query:");
        for argument in &args[1..] {
            out.push(' ');
            out.push_str(argument);
        }
        out.push('\n');
        out.push_str("===========================================\n");
        out.push_str(&tableau_not_wired("getExtensionManager()/Retrieval"));
        out.push_str("===========================================\n");
        out
    }
}

/// `ReuseNodeForCommand` (`reuseNodeFor`): concepts for which a node is a reuse
/// node under the individual-reuse strategy.
///
/// Requires `getExistentialsExpansionStrategy()` and
/// `IndividualReuseStrategy.getConceptForNode`, which are not accessible from
/// this module; argument parsing is reproduced but output is a placeholder.
pub struct ReuseNodeForCommand;
impl DebuggerCommand for ReuseNodeForCommand {
    fn command_name(&self) -> &str {
        "reuseNodeFor"
    }
    fn description(&self) -> Vec<(&str, &str)> {
        vec![(
            "nodeID",
            "prints concepts for which the given node is a reuse node under individual reuse strategy",
        )]
    }
    fn print_help(&self) -> String {
        "usage: reuseNodeFor nodeID\n    If individual reuse strategy is used, prints the concepts for which the given node is a reuse node.\n".to_string()
    }
    fn execute(&self, _debugger: &Debugger<'_>, args: &[String]) -> String {
        if args.len() < 2 {
            return "Node ID is missing.\n".to_string();
        }
        if args[1].parse::<i32>().is_err() {
            return "Invalid ID of the node.\n".to_string();
        }
        tableau_not_wired("getNode/getExistentialsExpansionStrategy")
    }
}

/// Port of `debugger.Printing`'s portable formatting helpers (the GUI/`Node`
/// internals routines have no Rust analogue and are omitted).
pub mod printing {
    /// `printPadded`: right-align `string` in a field of width `size`. Java's
    /// loop is `for (int i=size-string.length(); i>=0; --i) print(' ')`, i.e.
    /// it prints `size - len + 1` spaces when `len <= size`, and **zero** spaces
    /// when `len > size`. This matches Java's loop exactly: zero leading spaces
    /// when `len > size`.
    pub fn print_padded(string: &str, size: usize) -> String {
        let len = string.len();
        let pad = if len > size { 0 } else { size - len + 1 };
        format!("{}{}", " ".repeat(pad), string)
    }

    /// Port of `Printing.printConcepts(set, markedElements, writer, numberInRow)`:
    /// renders the already-rendered concept strings in `set`, `numberInRow` per
    /// row, separated by ", ", wrapping every `numberInRow` elements onto a fresh
    /// "    "-indented line, and appending " (*)" after any element present in
    /// `marked` (the unprocessed-existential marker). A trailing newline closes
    /// the block (`writer.println()` after the loop).
    ///
    /// The Java loop, faithfully: for the element at index `number`,
    ///   - if `number != 0`, print ", ";
    ///   - if `number % numberInRow == 0`, print newline then "    ";
    ///   - print the concept; if marked, print " (*)".
    /// then a final newline. (Note the order: the ", " separator is emitted
    /// *before* the row-wrap newline, exactly as HermiT does.)
    pub fn print_concepts(set: &[String], marked: &[String], number_in_row: usize) -> String {
        let mut out = String::new();
        for (number, concept) in set.iter().enumerate() {
            if number != 0 {
                out.push_str(", ");
            }
            if number % number_in_row == 0 {
                out.push('\n');
                out.push_str("    ");
            }
            out.push_str(concept);
            if marked.contains(concept) {
                out.push_str(" (*)");
            }
        }
        out.push('\n');
        out
    }

    /// `printCollection`: one indented line per element.
    pub fn print_collection<I, T>(collection: I) -> String
    where
        I: IntoIterator<Item = T>,
        T: std::fmt::Display,
    {
        let mut out = String::new();
        for object in collection {
            out.push_str("    ");
            out.push_str(&object.to_string());
            out.push('\n');
        }
        out
    }

    /// `diffCollections`: the elements of `c1` not in `c2` (under `in1_not_in2`)
    /// then those of `c2` not in `c1` (under `in2_not_in1`), in HermiT's windowed
    /// layout with the dashed separators.
    pub fn diff_collections<T>(
        in1_not_in2: &str,
        in2_not_in1: &str,
        c1: &[T],
        c2: &[T],
    ) -> String
    where
        T: PartialEq + std::fmt::Display,
    {
        let sep = "--------------------------------------------";
        let mut out = String::new();
        let mut window1 = false;
        for object in c1 {
            if !c2.contains(object) {
                if !window1 {
                    out.push_str(&format!("<<<  {in1_not_in2}:\n"));
                    window1 = true;
                }
                out.push_str(&format!("    {object}\n"));
            }
        }
        if window1 {
            out.push_str(sep);
            out.push('\n');
        }
        let mut window2 = false;
        for object in c2 {
            if !c1.contains(object) {
                if !window2 {
                    out.push_str(&format!(">>>  {in2_not_in1}:\n"));
                    window2 = true;
                }
                out.push_str(&format!("    {object}\n"));
            }
        }
        if window1 {
            out.push_str(sep);
            out.push('\n');
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn print_padded_matches_java_loop() {
        use super::printing::print_padded;
        // len <= size: Java prints size - len + 1 spaces.
        // width 5, "ab" (len 2) -> 5-2+1 = 4 spaces then "ab".
        assert_eq!(print_padded("ab", 5), "    ab");
        // len == size: 5-5+1 = 1 leading space.
        assert_eq!(print_padded("abcde", 5), " abcde");
        // len == size + ... boundary: width 2, "ab" -> 2-2+1 = 1 space.
        assert_eq!(print_padded("ab", 2), " ab");
        // len > size: Java's loop body never runs -> ZERO leading spaces.
        assert_eq!(print_padded("abcdef", 3), "abcdef");
        assert_eq!(print_padded("abc", 2), "abc");
    }

    #[test]
    fn printing_helpers_format_faithfully() {
        use super::printing::*;
        let coll = print_collection(["x", "y"]);
        assert_eq!(coll, "    x\n    y\n");

        let diff = diff_collections("only in 1", "only in 2", &["a", "b"], &["b", "c"]);
        assert!(diff.contains("<<<  only in 1:"));
        assert!(diff.contains("    a"));
        assert!(diff.contains(">>>  only in 2:"));
        assert!(diff.contains("    c"));
        // 'b' is in both -> not listed.
        assert!(!diff.contains("    b\n"));
    }

    #[test]
    fn parse_splits_like_java() {
        // Command name plus arguments, collapsing runs of spaces.
        assert_eq!(Debugger::parse("waitFor +clash -merge"), vec!["waitFor", "+clash", "-merge"]);
        // Multiple spaces collapse but a leading space is retained on the next
        // token's slice start exactly as Java's index arithmetic does; trimming
        // the whole line first means the command name has no leading space.
        assert_eq!(Debugger::parse("  showNode   3  "), vec!["showNode", "3"]);
        assert_eq!(Debugger::parse("help"), vec!["help"]);
    }

    #[test]
    fn derivation_tree_renders_provenance() {
        let mut history = DerivationHistory::new();
        history.record("A(a)", Derivation::BaseFact, vec![]);
        history.record("r(a,b)", Derivation::BaseFact, vec![]);
        history.record(
            "B(b)",
            Derivation::DLClauseApplication { dl_clause: "B(Y) :- A(X), r(X,Y)".into() },
            vec!["A(a)".into(), "r(a,b)".into()],
        );
        let tree = history.derivation_tree("B(b)");
        assert!(tree.contains("B(b)"));
        // The DLClauseApplication label is the fixed "  <--  "+clause string.
        assert!(tree.contains("  <--  B(Y) :- A(X), r(X,Y)"));
        assert!(tree.contains("A(a)"));
        assert!(tree.contains("r(a,b)"));
        // Base facts render with the "." label.
        assert!(tree.contains("A(a)."));
    }

    #[test]
    fn registers_full_non_gui_command_set() {
        let debugger = Debugger::new();
        // All 25 non-GUI commands, by their HermiT command names.
        for name in [
            "activeNodes",
            "a",
            "bpTime",
            "clear",
            "c",
            "dertree",
            "exit",
            "forever",
            "help",
            "history",
            "isAncOf",
            "modelStats",
            "nodesFor",
            "originStats",
            "query",
            "reuseNodeFor",
            "showDGraph",
            "showDLClauses",
            "showExists",
            "showModel",
            "showNode",
            "showSubtree",
            "singleStep",
            "uDisjunctions",
            "waitFor",
        ] {
            assert!(debugger.command(name).is_some(), "missing command {name}");
        }
        // Lookup is case-insensitive (Java lowercases the key).
        assert!(debugger.command("WAITFOR").is_some());
    }

    #[test]
    fn help_lists_commands_in_two_columns() {
        let debugger = Debugger::new();
        let help = debugger.execute_command("help", &[]);
        assert!(help.starts_with("Available commands are:\n"));
        assert!(help.contains("  :  "));
        // The predicate legend is included verbatim.
        assert!(help.contains("    +uri    atomic concept with the URI uri"));
        assert!(help.contains("    $uri    description graph with the URI uri"));
        // Per-command help.
        let waitfor_help = debugger.execute_command("help", &["waitFor".to_string()]);
        assert!(waitfor_help.starts_with("usage: waitFor"));
        // Unknown command help.
        assert!(debugger.execute_command("help", &["nope".to_string()]).contains("Unknown command 'nope'."));
    }

    #[test]
    fn continue_forever_singlestep_update_state() {
        let debugger = Debugger::new();
        debugger.state.borrow_mut().in_main_loop = true;
        assert_eq!(debugger.execute_command("c", &[]), "");
        assert!(!debugger.state.borrow().in_main_loop);

        debugger.state.borrow_mut().in_main_loop = true;
        debugger.execute_command("forever", &[]);
        {
            let state = debugger.state.borrow();
            assert!(!state.in_main_loop);
            assert!(state.forever);
            assert!(!state.singlestep);
        }

        assert_eq!(debugger.execute_command("singleStep", &["on".to_string()]), "Single step mode on.\n");
        assert!(debugger.state.borrow().singlestep);
        assert_eq!(debugger.execute_command("singleStep", &["off".to_string()]), "Single step mode off.\n");
        assert!(!debugger.state.borrow().singlestep);
        assert_eq!(debugger.execute_command("singleStep", &[]), "The status is missing.\n");
        assert!(debugger.execute_command("singleStep", &["maybe".to_string()]).contains("Incorrect single step mode 'maybe'."));
    }

    #[test]
    fn history_and_bptime_and_exit() {
        let debugger = Debugger::new();
        assert_eq!(debugger.execute_command("history", &["off".to_string()]), "Derivation history off.\n");
        assert!(!debugger.state.borrow().history_on);
        assert_eq!(debugger.execute_command("history", &["on".to_string()]), "Derivation history on.\n");
        assert!(debugger.state.borrow().history_on);

        assert_eq!(debugger.execute_command("bpTime", &["5".to_string()]), "Breakpoint time is 5 seconds.\n");
        assert_eq!(debugger.state.borrow().breakpoint_time, 5000);
        assert_eq!(debugger.execute_command("bpTime", &[]), "Time is missing.\n");
        assert_eq!(debugger.execute_command("bpTime", &["x".to_string()]), "Invalid time.\n");

        debugger.execute_command("exit", &[]);
        assert!(debugger.state.borrow().exit_requested);
        assert!(!debugger.state.borrow().in_main_loop);
    }

    #[test]
    fn waitfor_adds_and_removes_options() {
        let debugger = Debugger::new();
        let out = debugger.execute_command("waitFor", &["+clash".to_string(), "-merge".to_string()]);
        assert!(out.contains("Will wait for CLASH."));
        assert!(out.contains("Will not wait for MERGE."));
        assert!(debugger.state.borrow().wait_options.contains(&WaitOption::Clash));
        // Bare option defaults to add.
        debugger.execute_command("waitFor", &["gexists".to_string()]);
        assert!(debugger.state.borrow().wait_options.contains(&WaitOption::GraphExpansion));
        // Invalid option reports and stops.
        let bad = debugger.execute_command("waitFor", &["bogus".to_string()]);
        assert_eq!(bad, "Invalid wait option 'bogus'.\n");
    }

    #[test]
    fn again_replays_last_command() {
        let debugger = Debugger::new();
        // Run a state-changing command via the full command-line path so it is
        // recorded as the last command.
        debugger.process_command_line("singleStep on");
        assert!(debugger.state.borrow().singlestep);
        debugger.process_command_line("singleStep off");
        assert!(!debugger.state.borrow().singlestep);
        // `again` re-runs "singleStep off" and echoes it.
        let out = debugger.execute_command("a", &[]);
        assert!(out.starts_with("# singleStep off\n"));
        assert!(out.contains("Single step mode off."));
        // `again` itself must not become the last command.
        assert_eq!(debugger.state.borrow().last_command.as_deref(), Some("singleStep off"));
    }

    #[test]
    fn argument_validation_messages_match_java() {
        let debugger = Debugger::new();
        assert_eq!(debugger.execute_command("isAncOf", &["1".to_string()]), "Node IDs are missing.\n");
        assert_eq!(
            debugger.execute_command("isAncOf", &["x".to_string(), "2".to_string()]),
            "Invalid ID of the first node.\n"
        );
        assert_eq!(
            debugger.execute_command("isAncOf", &["1".to_string(), "y".to_string()]),
            "Invalid ID of the second node.\n"
        );
        assert_eq!(debugger.execute_command("showNode", &[]), "Node ID is missing.\n");
        assert_eq!(debugger.execute_command("showNode", &["z".to_string()]), "Invalid ID of the first node.\n");
        assert_eq!(debugger.execute_command("nodesFor", &[]), "Concept name is missing.\n");
        assert_eq!(debugger.execute_command("reuseNodeFor", &["q".to_string()]), "Invalid ID of the node.\n");
        assert_eq!(debugger.execute_command("showDGraph", &[]), "Graph name is missing.\n");
    }

    #[test]
    fn dertree_renders_recorded_atom() {
        let debugger = Debugger::new();
        debugger.history.borrow_mut().record("X(x)", Derivation::BaseFact, vec![]);
        let out = debugger.execute_command("dertree", &["X(x)".to_string()]);
        // A base fact renders as the fact text followed by the "." label.
        assert!(out.contains("X(x)."));
        assert_eq!(debugger.execute_command("dertree", &[]), "The specification of the predicate is missing.\n");
        assert_eq!(debugger.execute_command("dertree", &["Y(y)".to_string()]), "Atom not found.\n");
        // `dertree clash` looks up the empty tuple, keyed as "[ ]".
        debugger.history.borrow_mut().record(EMPTY_TUPLE_KEY, Derivation::ClashDetection, vec![]);
        let clash = debugger.execute_command("dertree", &["clash".to_string()]);
        assert!(clash.contains("   << CLASH"), "got: {clash}");
    }

    #[test]
    fn unknown_command_reports() {
        let debugger = Debugger::new();
        assert_eq!(debugger.process_command_line("nonexistent foo"), "Unknown command 'nonexistent'.\n");
    }

    #[test]
    fn tableau_dependent_commands_frame_output_with_residual() {
        let debugger = Debugger::new();
        let active = debugger.execute_command("activeNodes", &[]);
        assert!(active.contains("      ID"));
        assert!(active.contains("not wired to Tableau"));
        let stats = debugger.execute_command("modelStats", &[]);
        assert!(stats.contains("  Model statistics"));
        let exists = debugger.execute_command("showExists", &[]);
        assert!(exists.contains("Nodes with existentials"));
    }

    // ---- Tableau-wired data commands -----

    use crate::model::{Atom, AtomicConcept, Concept, DLClause, DLPredicate, Term, Variable};
    use crate::prefixes::Prefixes;
    use crate::tableau::{DependencySet, Tableau};

    /// Builds a tiny tableau with two named nodes (1, 2) and a tree child (3)
    /// under node 1, asserting `A` on node 1, then attaches it to a fresh
    /// `Debugger`. Returns the prefixes too so the caller can keep them borrowed.
    fn build_tableau() -> Tableau {
        let mut tableau = Tableau::new();
        let empty = DependencySet::Permanent(tableau.dependency_set_factory().empty_set());
        let a = tableau.create_new_named_node(&empty); // node id 1
        let _b = tableau.create_new_named_node(&empty); // node id 2
        let _child = tableau.create_new_tree_node(&empty, a); // node id 3, parent 1
        // Assert the atomic concept A on node 1.
        let concept_a = Concept::AtomicConcept(AtomicConcept::create("http://example.org/A"));
        tableau.add_concept_assertion(concept_a, a, &empty, true);
        tableau
    }

    #[test]
    fn show_node_prints_real_node_data() {
        let tableau = build_tableau();
        let prefixes = Prefixes::new();
        let mut debugger = Debugger::new();
        debugger.attach_tableau(&tableau, &prefixes, Vec::new());

        let out = debugger.execute_command("showNode", &["1".to_string()]);
        assert!(out.contains("Node ID:    1"), "got: {out}");
        assert!(out.contains("Parent ID:  (root node)"), "got: {out}");
        assert!(out.contains("Depth:      0"), "got: {out}");
        assert!(out.contains("Status:     active"), "got: {out}");
        assert!(out.contains("Blocked:    no"), "got: {out}");
        // The real positive concept label A is printed (not the placeholder).
        assert!(out.contains("http://example.org/A"), "got: {out}");
        assert!(!out.contains("getNode/printNodeData"), "got: {out}");

        // A child tree node reports its parent id and depth.
        let child = debugger.execute_command("showNode", &["3".to_string()]);
        assert!(child.contains("Parent ID:  1"), "got: {child}");
        assert!(child.contains("Depth:      1"), "got: {child}");

        // A missing node id reports the not-found message, like HermiT.
        let missing = debugger.execute_command("showNode", &["99".to_string()]);
        assert_eq!(missing, "Node with ID '99' not found.\n");
    }

    #[test]
    fn active_nodes_lists_real_node_ids() {
        let tableau = build_tableau();
        let prefixes = Prefixes::new();
        let mut debugger = Debugger::new();
        debugger.attach_tableau(&tableau, &prefixes, Vec::new());

        let out = debugger.execute_command("activeNodes", &[]);
        // Three unblocked nodes; their ids are listed (not the placeholder).
        assert!(out.contains("Active nodes (3):"), "got: {out}");
        assert!(out.contains("  1\n"), "got: {out}");
        assert!(out.contains("  2\n"), "got: {out}");
        assert!(out.contains("  3\n"), "got: {out}");
        assert!(!out.contains("not wired to Tableau"), "got: {out}");
    }

    #[test]
    fn model_stats_counts_real_nodes() {
        let tableau = build_tableau();
        let prefixes = Prefixes::new();
        let mut debugger = Debugger::new();
        debugger.attach_tableau(&tableau, &prefixes, Vec::new());

        let out = debugger.execute_command("modelStats", &[]);
        assert!(out.contains("Number of nodes:                    3"), "got: {out}");
        assert!(out.contains("Number of unblocked nodes:          3"), "got: {out}");
        assert!(out.contains("Number of directly blocked nodes:   0"), "got: {out}");
        assert!(!out.contains("not wired to Tableau"), "got: {out}");
    }

    #[test]
    fn is_anc_of_uses_real_ancestor_relation() {
        let tableau = build_tableau();
        let prefixes = Prefixes::new();
        let mut debugger = Debugger::new();
        debugger.attach_tableau(&tableau, &prefixes, Vec::new());

        // Node 1 is the parent of the tree node 3, hence an ancestor.
        let yes = debugger.execute_command("isAncOf", &["1".to_string(), "3".to_string()]);
        assert_eq!(yes, "Node 1 is an ancestor of node 3.");
        // Node 2 is unrelated to node 3.
        let no = debugger.execute_command("isAncOf", &["2".to_string(), "3".to_string()]);
        assert_eq!(no, "Node 2 is not an ancestor of node 3.");
        assert!(!yes.contains("not wired to Tableau"));
    }

    #[test]
    fn show_model_prints_real_tuples() {
        let tableau = build_tableau();
        let prefixes = Prefixes::new();
        let mut debugger = Debugger::new();
        debugger.attach_tableau(&tableau, &prefixes, Vec::new());

        let out = debugger.execute_command("showModel", &[]);
        // The asserted A(node 1) tuple is printed as label[id].
        assert!(out.contains("http://example.org/A"), "got: {out}");
        assert!(out.contains("[1]"), "got: {out}");
        assert!(!out.contains("not wired to Tableau"), "got: {out}");
    }

    #[test]
    fn show_dl_clauses_prints_real_clauses() {
        let tableau = build_tableau();
        let prefixes = Prefixes::new();
        // B(X) :- A(X)
        let x = Term::Variable(Variable::create("X"));
        let a = AtomicConcept::create("http://example.org/A");
        let b = AtomicConcept::create("http://example.org/B");
        let body = Atom::create(DLPredicate::AtomicConcept(a), vec![x.clone()]);
        let head = Atom::create(DLPredicate::AtomicConcept(b), vec![x]);
        let clause = DLClause::create(vec![head], vec![body]);
        let expected = clause.to_string_prefixes(&prefixes);

        let mut debugger = Debugger::new();
        debugger.attach_tableau(&tableau, &prefixes, vec![clause]);

        let out = debugger.execute_command("showDLClauses", &[]);
        assert!(out.contains("Permanent DL-clauses:"), "got: {out}");
        assert!(out.contains(&expected), "got: {out} expected: {expected}");
        assert!(!out.contains("not wired to Tableau"), "got: {out}");
    }

    #[test]
    fn query_reports_real_clash_state() {
        let tableau = build_tableau();
        let prefixes = Prefixes::new();
        let mut debugger = Debugger::new();
        debugger.attach_tableau(&tableau, &prefixes, Vec::new());

        // The fresh tableau has no clash.
        let out = debugger.execute_command("query", &[]);
        assert_eq!(out, "The modelcurrently does not contain a clash.\n");
        assert!(!out.contains("not wired to Tableau"));
    }

    #[test]
    fn detached_debugger_still_emits_residual() {
        // With no tableau attached the data commands fall back to the residual,
        // so the standalone command framework remains usable.
        let debugger = Debugger::new();
        assert!(debugger
            .execute_command("showNode", &["1".to_string()])
            .contains("not wired to Tableau"));
        assert!(debugger
            .execute_command("showDLClauses", &[])
            .contains("not wired to Tableau"));
    }
}
