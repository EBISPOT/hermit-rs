// Port of org.semanticweb.HermiT.cli.CommandLine: the command-line front-end.
//
// Loads an ontology (OWL functional `.ofn`, OWL/XML `.owx`/`.owl`, or RDF) and
// runs reasoning tasks (consistency, classification of classes / object
// properties / data properties, sub/super/equivalent classes, unsatisfiable
// classes, entailment checking, prefix dumping, DL-clause dumping), printing the
// results -- mirroring HermiT's `CommandLine` option table and Action classes.

use std::fs::File;
use std::io::{BufReader, Write};

use horned_owl::curie::PrefixMapping;
use horned_owl::model::{ArcStr, Build, Component};
use horned_owl::ontology::set::SetOntology;

use crate::configuration::{
    BlockingSignatureCacheType, BlockingStrategyType, Configuration, DirectBlockingType,
    ExistentialStrategyType, TableauMonitorType,
};
use crate::prefixes::Prefixes;
use crate::reasoner;

/// The reasoning task requested on the command line.
///
/// For `Subs`/`Supers`, `direct` mirrors Java's `-d/--direct` modifier:
/// HermiT's `SubsAction` honours it (see `CommandLine.java` lines 247-253:
/// `getSubClasses(owlClass, !getAll)`) but `SupersAction` **ignores** it —
/// `getSuperClasses` is called with `false` in **both** branches of
/// `CommandLine.java` lines 205-211, so `--direct` only changes the printed
/// header, not the returned set. The `direct` boolean stored in `Supers` is
/// retained for round-trip / future use but is **not** forwarded to the
/// reasoner.
///
/// `Classify` bundles the three hierarchy flags (`-c`, `-O`, `-D`) and the
/// `-P/--prettyPrint` flag exactly as Java's `ClassifyAction` does: the option
/// loop sets the booleans and a single `ClassifyAction` is appended (see
/// `CommandLine.java` lines 732-733).
#[derive(Debug, PartialEq, Clone)]
enum Task {
    /// `ClassifyAction`: classify classes / object properties / data properties.
    /// The fourth field is `pretty_print` (`-P`).
    Classify {
        classes: bool,
        object_properties: bool,
        data_properties: bool,
        pretty_print: bool,
        /// Absolute path of the `-o` results file, if any (for the "Writing
        /// results to ..." status line, CommandLine.java:152-153).
        results_file_location: Option<String>,
    },
    Unsatisfiable,
    Subs(String, bool),
    Supers(String, bool),
    Equivalents(String),
    /// `DumpPrefixesAction` (`--print-prefixes`).
    PrintPrefixes,
    /// `EntailsAction` (`-E/--checkEntailment`): the conclusion ontology IRI is
    /// carried here; the premise is the loaded ontology.
    CheckEntailment(String),
    /// `DumpClausesAction` (`--dump-clauses [FILE]`): the optional argument
    /// selects the destination sink (`DumpClausesAction.run`, CommandLine.java
    /// 100-118): no argument uses the global output writer (`-o` if present, else
    /// stdout); `-` forces stdout even when `-o` is set; a path opens its own file.
    DumpClauses(DumpClausesSink),
    /// `SatisfiabilityAction` (`-k [CLASS]`): check satisfiability of CLASS
    /// (CommandLine.java 577-584, 165-184). Default arg is `owl:Thing`.
    Satisfiability(String),
}

/// The destination of a `--dump-clauses` action (`DumpClausesAction.run`).
#[derive(Debug, PartialEq, Clone)]
enum DumpClausesSink {
    /// No argument: use the global output writer (`-o` if set, else stdout).
    GlobalOutput,
    /// Explicit `-`: force stdout, overriding any `-o` writer.
    Stdout,
    /// A file path: open it directly, overriding any `-o` writer.
    File(String),
}

/// `StatusOutput` (CommandLine.java:65-78): emits status/progress lines to stderr
/// gated on the verbosity `level`.  `log(in_level, msg)` prints `msg` only when
/// `in_level <= level`.  Levels mirror Java's constants: ALWAYS=0, STATUS=1,
/// DETAIL=2, DEBUG=3.
struct StatusOutput {
    level: i32,
}

impl StatusOutput {
    fn new(level: i32) -> Self {
        StatusOutput { level }
    }
    fn log(&self, in_level: i32, message: &str) {
        if in_level <= self.level {
            eprintln!("{message}");
        }
    }
}

/// The destination the global `-o`/stdout writer targets, mirroring Java's
/// `PrintWriter output` (CommandLine.java:436, 511-536).  Java creates/truncates
/// the `-o` file during argument parsing and uses a per-action autoflush writer;
/// we reproduce both: `File` opens (creating/truncating) the file immediately and
/// flushes after every action's write, while `Stdout` accumulates the text so the
/// binary can print it once.
enum Output {
    /// Accumulate output for the caller to print to stdout.
    Stdout(String),
    /// Write+flush each action's output to the open file (autoflush).
    File { file: File, path: String },
}

impl Output {
    /// `output.println(text)` followed by `output.flush()`: append a trailing
    /// newline and (for the file sink) flush immediately.
    fn println(&mut self, text: &str) -> Result<(), String> {
        match self {
            Output::Stdout(buf) => {
                buf.push_str(text);
                buf.push('\n');
                Ok(())
            }
            Output::File { file, path } => {
                file.write_all(text.as_bytes())
                    .and_then(|_| file.write_all(b"\n"))
                    .and_then(|_| file.flush())
                    .map_err(|e| format!("unable to write to {path}: {e}"))
            }
        }
    }

    /// Writes `text` verbatim (no added newline) and flushes the file sink. Used
    /// for the classify dump, which already carries its own trailing newlines
    /// (HierarchyDumperFSS writes directly to the PrintWriter).
    fn write_raw(&mut self, text: &str) -> Result<(), String> {
        match self {
            Output::Stdout(buf) => {
                buf.push_str(text);
                Ok(())
            }
            Output::File { file, path } => file
                .write_all(text.as_bytes())
                .and_then(|_| file.flush())
                .map_err(|e| format!("unable to write to {path}: {e}")),
        }
    }
}

/// Parses arguments, loads the ontology and runs the requested task, returning
/// the printable output. Mirrors `CommandLine.main`'s dispatch.
pub fn run(args: &[String]) -> Result<String, String> {
    // `ontologies` holds premise IRIs (added verbatim, CommandLine.java:543);
    // `positionals` holds non-option ontology args that are resolved against the
    // base URI after the option loop (CommandLine.java:720-727).
    let mut ontologies: Vec<String> = Vec::new();
    let mut positionals: Vec<String> = Vec::new();
    // Java uses LinkedList<Action> and appends each action as it is parsed
    // (CommandLine.java:444, 582-613); run() iterates and executes them all
    // (CommandLine.java:781-787). Mirror that with an ordered Vec<Task>.
    let mut tasks: Vec<Task> = Vec::new();
    // Java's `doAll` defaults to `true` (full/transitive). `-d/--direct` sets it
    // to `false` for the *next* subs/supers action, then it is reset to `true`
    // (CommandLine.java lines 585-599). `direct == !doAll`.
    let mut direct = false;

    // Classification flags accumulate across the option loop (Java sets the
    // `classifyClasses`/`classifyOPs`/`classifyDPs`/`prettyPrint` locals and
    // appends a single ClassifyAction afterwards, CommandLine.java 732-733).
    let mut classify_classes = false;
    let mut classify_ops = false;
    let mut classify_dps = false;
    let mut pretty_print = false;

    // `-N/--no-prefixes` (ignoreOntologyPrefixes), `-o/--output FILE`,
    // `-p PN=IRI` / default-prefix declarations, and `--conclusion IRI`.
    let mut no_prefixes = false;
    // Java opens/creates the `-o` file during argument parsing (CommandLine.java
    // 519-524) into an autoflush PrintWriter; track the open sink and the
    // absolute results-file location for the ClassifyAction status line.
    let mut output: Output = Output::Stdout(String::new());
    let mut results_file_location: Option<String> = None;
    let mut prefix_mappings: Vec<(String, String)> = Vec::new();
    let mut conclusion: Option<String> = None;
    // CommandLine.java:632-635 -- `--prefix=IRI` (kDefaultPrefix) sets the default
    // prefix, applied to the reasoner prefixes after the ontology is loaded.
    // Never reassigned: the long option `--prefix` (kDefaultPrefix) is shadowed
    // by `-p` in Java's getopt table, so this default-prefix path is unreachable
    // there too (CommandLine.java:417-418, 632-635).
    let default_prefix: Option<String> = None;
    // CommandLine.java:445-454 -- the base URI relative ontology args are resolved
    // against. Always `file:<cwd>/` (Java's `--base` override is unreachable).
    let base: String = default_base_uri();

    // Tableau-tuning options (CommandLine.java's `kAlgorithm` group). Each writes
    // a field of the `crate::configuration::Configuration` we hand to
    // `Reasoner::with_configuration`. We mutate a single Configuration that
    // starts from `Configuration::default()` (== HermiT's defaults), so when no
    // tuning flag is given the reasoner behaviour is unchanged.
    let mut config = Configuration::default();
    // CommandLine.java:434 -- verbosity starts at 1; `-v`/`-q` adjust it, and
    // `verbosity > 3` installs the `Timer` tableau monitor (CommandLine.java:730).
    let mut verbosity: i32 = 1;

    // Expand GNU-getopt short-option clusters and attached values before the
    // main parse loop (e.g. `-dsowl:Thing` -> `-d`, `-s`, `owl:Thing`).
    // Long options (`--foo`, `--foo=bar`) pass through unchanged.
    let args = expand_short_opts(args)?;
    let args: &[String] = &args;
    let mut i = 0;
    while i < args.len() {
        let arg = args[i].as_str();
        match arg {
            // CommandLine.java:464-473: print usageString, helpHeader, the
            // generated option help and the footer (Java exits 0 and prints to
            // stdout).
            "--help" | "-h" => return Ok(help_text()),
            // CommandLine.java:475-481: print versionString then each footer line
            // (each via System.out.println, so the text ends with a newline).
            "--version" | "-V" => {
                let mut lines = vec![version_string()];
                lines.extend(FOOTER.iter().map(|s| s.to_string()));
                return Ok(format!("{}\n", lines.join("\n")));
            }
            // CommandLine.java:484-505: `-v`/`-q` adjust the verbosity counter (by 1
            // by default, or by an attached numeric AMOUNT). A non-numeric amount is
            // a usage error. At `verbosity > 3` a `Timer` monitor is installed below.
            "--verbose" | "-v" => verbosity += 1,
            "--quiet" | "-q" => verbosity -= 1,
            value if value.starts_with("--verbose=") || value.starts_with("-v=") => {
                let amount = value.split_once('=').unwrap().1;
                verbosity += amount
                    .parse::<i32>()
                    .map_err(|_| "argument to --verbose must be a number".to_string())?;
            }
            value if value.starts_with("--quiet=") || value.starts_with("-q=") => {
                let amount = value.split_once('=').unwrap().1;
                verbosity -= amount
                    .parse::<i32>()
                    .map_err(|_| "argument to --quiet must be a number".to_string())?;
            }
            // `-l/--load`: load is the default action and otherwise a no-op
            // (CommandLine.java 557-559).
            "--load" | "-l" => {}
            // `-k [CLASS]`: SatisfiabilityAction (CommandLine.java 577-584).
            // OPTIONAL_ARGUMENT semantics: gnu.getopt takes CLASS only in attached
            // form (`-kFoo` / `--consistency=Foo`), never from a following separate
            // token. A bare `-k`/`--consistency` defaults to owl:Thing (Java:
            // `if (arg==null) arg="http://…owl#Thing"`). The attached short form is
            // normalised to `-k=Foo` by `expand_short_opts`.
            "--consistency" | "-k" => {
                tasks.push(Task::Satisfiability(
                    "http://www.w3.org/2002/07/owl#Thing".to_string(),
                ));
            }
            value if value.starts_with("--consistency=") || value.starts_with("-k=") => {
                let class_name = value.split_once('=').unwrap().1.to_string();
                tasks.push(Task::Satisfiability(class_name));
            }
            // Classification flags: set the accumulator, the ClassifyAction is
            // assembled after the loop.
            "--classify" | "-c" => classify_classes = true,
            "--classifyOPs" | "-O" => classify_ops = true,
            "--classifyDPs" | "-D" => classify_dps = true,
            "--prettyPrint" | "-P" => pretty_print = true,
            "--unsatisfiable" | "-U" => tasks.push(Task::Unsatisfiable),
            "--print-prefixes" => tasks.push(Task::PrintPrefixes),
            "--checkEntailment" | "-E" => {
                // EntailsAction is only added when a conclusion IRI has already
                // been given (CommandLine.java 610-613): with `-E` appearing
                // before `--conclusion`, the flag is silently a no-op.
                if let Some(c) = &conclusion {
                    tasks.push(Task::CheckEntailment(c.clone()));
                }
            }
            "--dump-clauses" => {
                // OPTIONAL_ARGUMENT (gnu.getopt): a value is taken only in the
                // attached form `--dump-clauses=FILE` (handled below). A following
                // separate token -- including `-` -- is never consumed, so the bare
                // form (file==null) uses the global output writer (`-o` if set).
                tasks.push(Task::DumpClauses(DumpClausesSink::GlobalOutput));
            }
            // `--no-prefixes` / `-N`.
            "--no-prefixes" | "-N" => no_prefixes = true,
            // `-o/--output FILE`: write output to FILE instead of stdout.
            // CommandLine.java:511-536 -- `-` keeps stdout; otherwise the file is
            // created/truncated NOW (during parsing) into an autoflush writer, so
            // an empty file survives a later error.  `resultsFileLocation` records
            // the absolute path for the ClassifyAction status line.
            "--output" | "-o" => {
                i += 1;
                let value = arg_value(args, i, "--output")?;
                if value == "-" {
                    output = Output::Stdout(String::new());
                } else {
                    let file = File::create(&value)
                        .map_err(|_| format!("unable to open {value} for writing"))?;
                    let abs = std::fs::canonicalize(&value)
                        .map(|p| p.to_string_lossy().to_string())
                        .unwrap_or_else(|_| value.clone());
                    results_file_location = Some(abs);
                    output = Output::File { file, path: value };
                }
            }
            "--premise" => {
                // The premise ontology is just another input ontology
                // (CommandLine.java 538-545: added to the `ontologies` list).
                i += 1;
                ontologies.push(arg_value(args, i, "--premise")?);
            }
            "--conclusion" => {
                i += 1;
                conclusion = Some(arg_value(args, i, "--conclusion")?);
            }
            // Note: Java defines a `kBase` switch case (CommandLine.java:637-646)
            // but does NOT register `--base` in its options[] table, so getopt
            // rejects `--base` as an invalid option before that case is reached.
            // To stay faithful we do NOT recognise `--base`; it falls through to
            // the unknown-option handler. The base URI is always the default
            // `file:<cwd>/` used to resolve relative ontology arguments.
            // `-p PN=IRI`: Java's case 'p' requires '='; no '=' is an error
            // (CommandLine.java:625-628: eqIndex==-1 -> IllegalArgumentException).
            "--prefix" | "-p" => {
                i += 1;
                let value = arg_value(args, i, "--prefix")?;
                match value.split_once('=') {
                    Some((name, iri)) => {
                        // The prefix name is stored verbatim (Java's
                        // `prefixMappings.put(name, iri)`); `declarePrefixRaw`
                        // later rejects a name not ending in a colon
                        // (Prefixes.java:163-164), which CommandLine logs and
                        // skips. So `-p ex=IRI` (no colon) is dropped, only
                        // `-p ex:=IRI` registers.
                        prefix_mappings.push((name.to_string(), iri.to_string()));
                    }
                    // Java: "the prefix declaration 'X' is not of the form PN=IRI."
                    None => {
                        return Err(format!(
                            "the prefix declaration '{value}' is not of the form PN=IRI."
                        ));
                    }
                }
            }
            // `-d/--direct`: restrict the next subs/supers call to direct only.
            "--direct" | "-d" => {
                direct = true;
                i += 1;
                continue;
            }
            "--subs" | "-s" => {
                i += 1;
                tasks.push(Task::Subs(arg_value(args, i, "--subs")?, direct));
                direct = false;
            }
            "--supers" | "-S" => {
                i += 1;
                tasks.push(Task::Supers(arg_value(args, i, "--supers")?, direct));
                direct = false;
            }
            "--equivalents" | "-e" => {
                i += 1;
                tasks.push(Task::Equivalents(arg_value(args, i, "--equivalents")?));
            }
            // Tableau-tuning options (CommandLine.java's `kAlgorithm` group). All
            // are long-only in Java (no short char). The three TYPE-valued ones
            // reject an unrecognised value with Java's exact UsageException text.
            "--block-strategy" => {
                i += 1;
                config.blocking_strategy_type =
                    parse_block_strategy(&arg_value(args, i, "--block-strategy")?)?;
            }
            "--block-match" => {
                i += 1;
                config.direct_blocking_type =
                    parse_direct_block(&arg_value(args, i, "--block-match")?)?;
            }
            "--expansion-strategy" => {
                i += 1;
                config.existential_strategy_type =
                    parse_expansion_strategy(&arg_value(args, i, "--expansion-strategy")?)?;
            }
            // `--blockersCache` is a NO-ARG flag in Java: it (re)selects CACHED,
            // which is already the default (CommandLine.java 681-683).
            "--blockersCache" => {
                config.blocking_signature_cache_type = BlockingSignatureCacheType::Cached;
            }
            "--ignoreUnsupportedDatatypes" => {
                config.ignore_unsupported_datatypes = true;
            }
            "--noInconsistentException" => {
                config.throw_inconsistent_ontology_exception = false;
            }
            value if value.starts_with("--block-strategy=") => {
                config.blocking_strategy_type =
                    parse_block_strategy(value.trim_start_matches("--block-strategy="))?;
            }
            value if value.starts_with("--block-match=") => {
                config.direct_blocking_type =
                    parse_direct_block(value.trim_start_matches("--block-match="))?;
            }
            value if value.starts_with("--expansion-strategy=") => {
                config.existential_strategy_type =
                    parse_expansion_strategy(value.trim_start_matches("--expansion-strategy="))?;
            }
            value if value.starts_with("--dump-clauses=") => {
                let dest = value.trim_start_matches("--dump-clauses=").to_string();
                tasks.push(Task::DumpClauses(if dest == "-" {
                    DumpClausesSink::Stdout
                } else {
                    DumpClausesSink::File(dest)
                }));
            }
            // CommandLine.java:720-727 -- positional (non-option) ontology args
            // are resolved against the base URI (`base.resolve(argv[i])`); premise
            // args (handled above) are NOT resolved.
            other if !other.starts_with('-') => {
                positionals.push(other.to_string());
            }
            // CommandLine.java:712-717 -- getopt's default case: an unrecognised
            // SHORT option reports the offending char (`invalid option -- x`); an
            // unrecognised LONG option (getOptopt()==0) reports just
            // `invalid option`.
            other => {
                if let Some(c) = short_opt_char(other) {
                    return Err(format!("invalid option -- {c}"));
                }
                return Err("invalid option".to_string());
            }
        }
        i += 1;
    }

    // CommandLine.java:729-731 -- the StatusOutput is created with the final
    // verbosity, and `if (verbosity>3) config.monitor=new Timer(...)`.
    let status = StatusOutput::new(verbosity);
    if verbosity > 3 {
        config.tableau_monitor_type = TableauMonitorType::Timing;
    }

    // Assemble the ClassifyAction from the accumulated flags and push it last,
    // exactly as Java does after the option loop (CommandLine.java:732-733).
    if classify_classes || classify_ops || classify_dps {
        tasks.push(Task::Classify {
            classes: classify_classes,
            object_properties: classify_ops,
            data_properties: classify_dps,
            pretty_print,
            results_file_location: results_file_location.clone(),
        });
    }

    // CommandLine.java:720-727 -- resolve each positional ontology arg against the
    // base URI and append after the premise ontologies.
    for arg in &positionals {
        ontologies.push(resolve_against_base(&base, arg));
    }

    // Java performs NO implicit action when none is requested: each ontology is
    // merely parsed and nothing is printed (CommandLine.java:734-788 loops over
    // zero actions). Only the absence of any ontology is an error
    // (CommandLine.java:794-795: `if (!didSomething) throw "No ontologies given."`).
    if ontologies.is_empty() {
        return Err("No ontologies given.".into());
    }

    // Java accumulates every positional ontology and the `--premise` IRI into a
    // single list and runs ALL actions against EACH ontology in turn
    // (CommandLine.java:734-793). For the common single-ontology / entailment
    // case this loop runs exactly once.  The same `output` writer is reused
    // across all ontologies and actions (CommandLine.java:436, 784).
    for ont in &ontologies {
        // CommandLine.java:736-737 -- progress lines (level DETAIL).
        status.log(2, &format!("Processing {ont}"));
        status.log(2, &format!("{} actions", tasks.len()));
        // CommandLine.java:738-792 -- a per-ontology try/catch that swallows OWL
        // load/processing failures, prints "It all went pear-shaped: <msg>" and
        // continues with the next ontology rather than aborting.
        if let Err(message) = process_ontology(
            ont,
            &tasks,
            &prefix_mappings,
            default_prefix.as_deref(),
            no_prefixes,
            &config,
            &status,
            &mut output,
        ) {
            // CommandLine.java:789-791.
            eprintln!("It all went pear-shaped: {message}");
        }
    }

    // The `-o` file has already received its content (autoflush, per action). For
    // stdout, return the accumulated text verbatim (it already carries the exact
    // trailing newlines Java's PrintWriter emitted); the binary prints it with
    // `print!` and adds nothing.
    match output {
        Output::Stdout(buf) => Ok(buf),
        // Java prints nothing extra to stdout when `-o` redirects output.
        Output::File { .. } => Ok(String::new()),
    }
}

/// Loads one ontology and runs all actions against it, mirroring the body of
/// CommandLine.java's per-ontology `try` block (lines 738-788). Errors are
/// returned to the caller, which prints the "pear-shaped" message and continues
/// (CommandLine.java:789-792).
#[allow(clippy::too_many_arguments)]
fn process_ontology(
    ont: &str,
    tasks: &[Task],
    prefix_mappings: &[(String, String)],
    default_prefix: Option<&str>,
    no_prefixes: bool,
    config: &Configuration,
    status: &StatusOutput,
    output: &mut Output,
) -> Result<(), String> {
    // Convert a `file:` IRI back to a local path for the parser; remote IRIs are
    // not fetchable in this environment (see report).
    let load_target = iri_to_load_path(ont)?;
    let start = std::time::Instant::now();
    let (ontology, prefix_mapping) = load_ontology_with_prefixes(&load_target)?;
    // CommandLine.java:758-759.
    status.log(
        2,
        &format!("Ontology parsed in {} msec.", start.elapsed().as_millis()),
    );

    let start = std::time::Instant::now();
    // Build the reasoner's prefixes exactly as Reasoner.createPrefixes + the
    // CommandLine `-p`/default-prefix override loop (CommandLine.java:761-778).
    let prefixes =
        build_reasoner_prefixes(&ontology, &prefix_mapping, prefix_mappings, default_prefix, status)?;
    // CommandLine.java:779-780.
    status.log(
        2,
        &format!("Reasoner created in {} msec.", start.elapsed().as_millis()),
    );

    // Run each task in order (CommandLine.java:781-787).
    for task in tasks {
        // CommandLine.java:782.
        status.log(2, "Doing action...");
        let start = std::time::Instant::now();
        run_task(
            &ontology,
            &prefixes,
            no_prefixes,
            config.clone(),
            task.clone(),
            status,
            output,
        )?;
        // CommandLine.java:785-786.
        status.log(
            2,
            &format!("...action completed in {} msec.", start.elapsed().as_millis()),
        );
    }
    Ok(())
}

/// Java's default base URI: `new URI("file", user.dir + "/", null)` i.e.
/// `file:<cwd>/` (CommandLine.java:449-454).
fn default_base_uri() -> String {
    let cwd = std::env::current_dir()
        .map(|p| p.to_string_lossy().to_string())
        .unwrap_or_default();
    format!("file:{cwd}/")
}

/// Resolves a (possibly relative) ontology argument against `base`, mirroring
/// `base.resolve(arg)` (CommandLine.java:722). An absolute IRI (one with a
/// scheme such as `http:`, `https:`, `file:`) is returned unchanged; a relative
/// reference is resolved against the base directory.
fn resolve_against_base(base: &str, arg: &str) -> String {
    if has_uri_scheme(arg) {
        arg.to_string()
    } else if arg.starts_with('/') {
        // Absolute local path -> file: IRI.
        format!("file:{arg}")
    } else {
        // Relative reference: append to the directory portion of the base. The
        // default base already ends in `/`.
        if base.ends_with('/') {
            format!("{base}{arg}")
        } else {
            format!("{base}/{arg}")
        }
    }
}

/// True if `s` begins with a URI scheme (`scheme:`), e.g. `http:`, `https:`,
/// `file:`. A bare Windows-style single letter is not relevant here.
fn has_uri_scheme(s: &str) -> bool {
    if let Some(idx) = s.find(':') {
        if idx == 0 {
            return false;
        }
        let scheme = &s[..idx];
        scheme.chars().next().is_some_and(|c| c.is_ascii_alphabetic())
            && scheme
                .chars()
                .all(|c| c.is_ascii_alphanumeric() || c == '+' || c == '-' || c == '.')
    } else {
        false
    }
}

/// Maps a resolved ontology IRI to a target the parser can open. `file:` IRIs are
/// converted back to a local filesystem path; `http(s):` IRIs are not fetchable
/// in this environment and produce an error (caught by the per-ontology handler).
fn iri_to_load_path(iri: &str) -> Result<String, String> {
    if let Some(rest) = iri.strip_prefix("file:") {
        // Strip an authority component if present (`file://host/path` ->
        // `/path`); the common `file:/abs` and `file:rel` forms pass through.
        let path = if let Some(after) = rest.strip_prefix("//") {
            match after.find('/') {
                Some(slash) => after[slash..].to_string(),
                None => after.to_string(),
            }
        } else {
            rest.to_string()
        };
        Ok(path)
    } else if has_uri_scheme(iri) {
        // Remote (http/https/...) loading is not supported in this environment.
        Err(format!(
            "remote ontology loading is not supported in this build: {iri}"
        ))
    } else {
        Ok(iri.to_string())
    }
}

/// If `tok` is a short option (`-x`, single char, not `--...`), returns its
/// char; otherwise `None` (a long `--foo` maps to getopt's `getOptopt()==0`).
/// Used to choose between `invalid option -- x` and `invalid option`
/// (CommandLine.java:712-717).
fn short_opt_char(tok: &str) -> Option<char> {
    if tok.starts_with("--") || !tok.starts_with('-') {
        return None;
    }
    let rest = &tok[1..];
    let mut chars = rest.chars();
    let c = chars.next()?;
    if chars.next().is_none() {
        Some(c)
    } else {
        None
    }
}

fn arg_value(args: &[String], index: usize, option: &str) -> Result<String, String> {
    args.get(index).cloned().ok_or_else(|| match option {
        // Match CommandLine.java's option-specific usage messages exactly.
        "--premise" => "--premise requires a IRI as argument".to_string(),
        "--conclusion" => "--conclusion requires a IRI as argument".to_string(),
        "--output" => "--output requires an argument".to_string(),
        _ => format!("{option} requires an argument"),
    })
}

/// Pre-process `args` to expand GNU-getopt-style short-option clusters and
/// attached values, mirroring `CommandLine.java`'s use of `gnu.getopt.Getopt`
/// with the option string derived from `Option.formatOptionsString`
/// (CommandLine.java lines 458, 887-905).
///
/// Rules (one pass over the original tokens):
/// - A token starting with `--` or not starting with `-` is passed through
///   unchanged.
/// - A single `-` by itself is passed through (stdin convention).
/// - A short-option cluster (`-XY…`) is split left-to-right:
///   - No-arg char: emits `-X`, then continues to the next char.
///   - Required-arg char (`o`, `s`, `S`, `e`, `p`): the remainder of the
///     token (after this char) is its value if non-empty; otherwise the *next*
///     argv token is consumed as the value. Either way scanning stops.
///   - Optional-arg char (`v`, `q`, `k`): the remainder (if non-empty) is the
///     value; if empty the option is emitted alone and no following token is
///     consumed. Either way scanning stops.
///   - Unknown char: returns `Err("Unknown option: -X")`.
fn expand_short_opts(args: &[String]) -> Result<Vec<String>, String> {
    // Chars whose option takes a REQUIRED argument (gnu.getopt optstring `x:`).
    const REQUIRED_ARG: &[char] = &['o', 's', 'S', 'e', 'p'];
    // Chars whose option takes an OPTIONAL argument (gnu.getopt optstring `x::`).
    const OPTIONAL_ARG: &[char] = &['v', 'q', 'k'];
    // All short chars that are valid options (no-arg or one of the above).
    const VALID: &[char] = &[
        'h', 'V', 'v', 'q', 'o', 'l', 'c', 'O', 'D', 'P', 'k', 'd', 's', 'S',
        'e', 'U', 'E', 'N', 'p',
    ];

    let mut out: Vec<String> = Vec::with_capacity(args.len());
    let mut idx = 0usize;
    while idx < args.len() {
        let tok = &args[idx];
        // Long option or plain file / non-option token: pass through unchanged.
        if !tok.starts_with('-') || tok == "-" || tok.starts_with("--") {
            out.push(tok.clone());
            idx += 1;
            continue;
        }
        // Short-option token: scan chars after the leading `-`.
        let mut chars = tok[1..].chars().peekable();
        while let Some(c) = chars.next() {
            if !VALID.contains(&c) {
                // CommandLine.java:713-714 -- getopt reports the offending char.
                return Err(format!("invalid option -- {c}"));
            }
            let flag = format!("-{c}");
            if REQUIRED_ARG.contains(&c) {
                // Remainder of the current token is the value if non-empty;
                // otherwise consume the next argv token.
                let rest: String = chars.collect();
                if !rest.is_empty() {
                    out.push(flag);
                    out.push(rest);
                } else {
                    out.push(flag);
                    idx += 1;
                    if idx < args.len() {
                        out.push(args[idx].clone());
                    }
                    // Missing value will be caught by arg_value in the main loop.
                }
                break; // Stop scanning this cluster.
            } else if OPTIONAL_ARG.contains(&c) {
                // OPTIONAL_ARGUMENT: gnu.getopt takes the value ONLY in attached
                // form (`-kFoo`, `-v3`), never from a following separate token. Keep
                // an attached value joined to the flag (`-k=Foo`, `-v=3`) so the main
                // loop can tell it apart from a separate token.
                let rest: String = chars.collect();
                if !rest.is_empty() {
                    out.push(format!("{flag}={rest}"));
                } else {
                    out.push(flag);
                }
                break;
            } else {
                // No-arg option: emit and continue scanning the cluster.
                out.push(flag);
            }
        }
        idx += 1;
    }
    Ok(out)
}

/// `--block-strategy <TYPE>` (`kBlockStrategy`): parse the accepted value into a
/// [`BlockingStrategyType`], mirroring `CommandLine.java` lines 663-679. Java
/// lower-cases the argument and accepts `anywhere`, `ancestor`, `core` (mapped to
/// `SIMPLE_CORE`) and `optimal`; anything else raises a `UsageException` with the
/// exact message reproduced here. (The Java enum also has `COMPLEX_CORE`/`OPTIMAL`
/// core variants but the CLI never exposes them, so neither do we.)
fn parse_block_strategy(arg: &str) -> Result<BlockingStrategyType, String> {
    match arg.to_ascii_lowercase().as_str() {
        "anywhere" => Ok(BlockingStrategyType::Anywhere),
        "ancestor" => Ok(BlockingStrategyType::Ancestor),
        "core" => Ok(BlockingStrategyType::SimpleCore),
        "optimal" => Ok(BlockingStrategyType::Optimal),
        _ => Err(format!(
            "unknown blocking strategy type '{arg}'; supported values are 'ancestor' and 'anywhere'"
        )),
    }
}

/// `--block-match <TYPE>` (`kDirectBlock`): parse into a [`DirectBlockingType`],
/// mirroring `CommandLine.java` lines 648-660. Accepts `pairwise` (→ `PAIR_WISE`),
/// `single` and `optimal`.
fn parse_direct_block(arg: &str) -> Result<DirectBlockingType, String> {
    match arg.to_ascii_lowercase().as_str() {
        "pairwise" => Ok(DirectBlockingType::PairWise),
        "single" => Ok(DirectBlockingType::Single),
        "optimal" => Ok(DirectBlockingType::Optimal),
        _ => Err(format!(
            "unknown direct blocking type '{arg}'; supported values are 'pairwise', 'single', and 'optimal'"
        )),
    }
}

/// `--expansion-strategy <TYPE>` (`kExpansion`): parse into an
/// [`ExistentialStrategyType`], mirroring `CommandLine.java` lines 685-697.
/// Accepts `creation` (→ `CREATION_ORDER`), `el` and `reuse` (→
/// `INDIVIDUAL_REUSE`).
fn parse_expansion_strategy(arg: &str) -> Result<ExistentialStrategyType, String> {
    match arg.to_ascii_lowercase().as_str() {
        "creation" => Ok(ExistentialStrategyType::CreationOrder),
        "el" => Ok(ExistentialStrategyType::El),
        "reuse" => Ok(ExistentialStrategyType::IndividualReuse),
        _ => Err(format!(
            "unknown existential strategy type '{arg}'; supported values are 'creation', 'el', and 'reuse'"
        )),
    }
}

/// Builds the reasoner's prefix map exactly as `Reasoner.createPrefixes`
/// (Reasoner.java:230-255) followed by the CommandLine `-p` override loop
/// (CommandLine.java:771-778):
///
/// 1. the well-known Semantic Web prefixes (`owl:`, `rdf:`, ...),
/// 2. the internal prefixes (`def:`, `nom:`, `anon:`, ...) seeded from the
///    ontology's individual IRIs,
/// 3. the default prefix `:` set to `<ontologyIRI>#`,
/// 4. the ontology-document prefixes, declared only when their IRI is not
///    already bound to a prefix name,
/// 5. the CLI `-p PN=IRI` mappings, applied last via `declarePrefix` so they
///    override an existing name (a colon-less name or an IRI already bound to a
///    different name is rejected, matching `declarePrefixRaw`, and silently
///    skipped as CommandLine swallows the exception).
fn build_reasoner_prefixes(
    ontology: &SetOntology<ArcStr>,
    prefix_mapping: &PrefixMapping,
    cli_mappings: &[(String, String)],
    default_prefix: Option<&str>,
    status: &StatusOutput,
) -> Result<Prefixes, String> {
    let dl_ontology = clausify(ontology)?;
    // addIRI: skip internal: IRIs; take the substring up to and including '#'.
    let add_iri = |iri: &str, set: &mut std::collections::BTreeSet<String>| {
        if !Prefixes::is_internal_iri(iri) {
            if let Some(pos) = iri.rfind('#') {
                set.insert(iri[..pos + 1].to_string());
            }
        }
    };
    let mut named_iris: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    let mut anon_iris: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    for ind in dl_ontology.get_all_individuals() {
        if ind.is_anonymous() {
            add_iri(ind.iri(), &mut anon_iris);
        } else {
            add_iri(ind.iri(), &mut named_iris);
        }
    }
    let mut p = Prefixes::new();
    p.declare_semantic_web_prefixes();
    p.declare_internal_prefixes(
        named_iris.iter().map(|s| s.as_str()),
        anon_iris.iter().map(|s| s.as_str()),
    );
    let ontology_iri = ontology
        .i()
        .the_ontology_id()
        .and_then(|id| id.iri)
        .map(|iri| iri.as_ref().to_string())
        .unwrap_or_default();
    let _ = p.declare_default_prefix(&format!("{ontology_iri}#"));
    // Ontology-document prefixes, only when the IRI is not already mapped.
    for (name, iri) in prefix_mapping.mappings() {
        let name_colon = format!("{name}:");
        if p.get_prefix_name(&iri.to_string()).is_none() {
            let _ = p.declare_prefix(&name_colon, &iri.to_string());
        }
    }
    // CommandLine.java:763-769 -- `--prefix=IRI` (kDefaultPrefix) sets the default
    // prefix; on failure Java logs at level DETAIL and continues. (In practice the
    // long option `--prefix` collides with `-p`, so this path is unreachable from
    // normal getopt parsing, mirrored by `default_prefix` staying `None`.)
    if let Some(dp) = default_prefix {
        if p.declare_default_prefix(dp).is_err() {
            status.log(
                2,
                &format!(
                    "Default prefix {dp} could not be registered because there is already a registered default prefix. "
                ),
            );
        }
    }
    // CLI `-p` declarations applied last (override semantics). On a clash Java
    // logs at level DETAIL and continues (CommandLine.java:771-778).
    for (name, iri) in cli_mappings {
        if p.declare_prefix(name, iri).is_err() {
            status.log(
                2,
                &format!(
                    "Prefixname {name} could not be set to {iri} because there is already a registered prefix name for the IRI. "
                ),
            );
        }
    }
    Ok(p)
}

/// Resolves a class-name argument to a full IRI exactly as `CommandLine.java`'s
/// sub/super/equivalents/satisfiability actions do (e.g. lines 173-175):
///
/// ```java
/// String conceptUri = prefixes.canBeExpanded(name)
///         ? prefixes.expandAbbreviatedIRI(name) : name;
/// if (conceptUri.startsWith("<") && conceptUri.endsWith(">"))
///     conceptUri = conceptUri.substring(1, conceptUri.length() - 1);
/// ```
fn resolve_class_iri(prefixes: &Prefixes, name: &str) -> Result<String, String> {
    let resolved = if prefixes.can_be_expanded(name) {
        prefixes.expand_abbreviated_iri(name)?
    } else {
        name.to_string()
    };
    if resolved.starts_with('<') && resolved.ends_with('>') && resolved.len() >= 2 {
        Ok(resolved[1..resolved.len() - 1].to_string())
    } else {
        Ok(resolved)
    }
}

/// Renders an IRI for output, honouring `--no-prefixes` (`ignoreOntologyPrefixes`):
/// when prefixes are *not* ignored the IRI is abbreviated, otherwise it is left
/// as the full IRI (CommandLine.java's sub/super actions, lines 215-223).
fn render_iri(prefixes: &Prefixes, ignore_prefixes: bool, iri: &str) -> String {
    if ignore_prefixes {
        iri.to_string()
    } else {
        prefixes.abbreviate_iri(iri)
    }
}

/// Loads an ontology, choosing the parser by file extension.
pub fn load_ontology(path: &str) -> Result<SetOntology<ArcStr>, String> {
    load_ontology_with_prefixes(path).map(|(ontology, _)| ontology)
}

/// Like [`load_ontology`] but also returns the prefix declarations parsed from
/// the ontology document (used to resolve abbreviated class-name arguments).
fn load_ontology_with_prefixes(
    path: &str,
) -> Result<(SetOntology<ArcStr>, PrefixMapping), String> {
    use horned_owl::io::ParserConfiguration;
    let file = File::open(path).map_err(|e| format!("Cannot open {path}: {e}"))?;
    let mut reader = BufReader::new(file);
    let lower = path.to_ascii_lowercase();
    let result: Result<(SetOntology<ArcStr>, _), _> = if lower.ends_with(".ofn") {
        horned_owl::io::ofn::reader::read(reader, ParserConfiguration::default())
    } else if lower.ends_with(".owx") || lower.ends_with(".owl") || lower.ends_with(".xml") {
        horned_owl::io::owx::reader::read(&mut reader, ParserConfiguration::default())
    } else {
        return Err(format!(
            "Unsupported ontology format for {path} (use .ofn or .owx/.owl/.xml)."
        ));
    };
    result.map_err(|e| format!("Failed to parse {path}: {e}"))
}

#[allow(clippy::too_many_arguments)]
fn run_task(
    ontology: &SetOntology<ArcStr>,
    prefixes: &Prefixes,
    ignore_prefixes: bool,
    config: Configuration,
    task: Task,
    status: &StatusOutput,
    output: &mut Output,
) -> Result<(), String> {
    let build = Build::new_arc();
    match task {
        // SatisfiabilityAction (CommandLine.java 165-184): resolve the class IRI,
        // warn if undeclared, run isSatisfiable, print Java's exact message.
        Task::Satisfiability(ref concept_name) => {
            // CommandLine.java:171.
            status.log(2, &format!("Checking satisfiability of '{concept_name}'"));
            let iri = resolve_class_iri(prefixes, concept_name)?;
            let class = build.class(iri.clone());
            // isDefined warning (CommandLine.java 177-179): status level ALWAYS(0).
            if let Ok(false) = reasoner::is_defined_class(ontology, &class) {
                status.log(0, &format!("Warning: class '{iri}' was not declared in the ontology."));
            }
            let satisfiable = reasoner::is_concept_satisfiable_with_configuration(
                ontology,
                horned_owl::model::ClassExpression::Class(class),
                &config,
            )?;
            // Output uses the ORIGINAL conceptName as Java does (CommandLine.java 181).
            let suffix = if satisfiable { " is satisfiable." } else { " is not satisfiable." };
            output.println(&format!("{concept_name}{suffix}"))
        }
        Task::Classify {
            classes,
            object_properties,
            data_properties,
            pretty_print,
            results_file_location,
        } => {
            // CommandLine.java:149 -- "Classifying..." at level DETAIL.
            status.log(2, "Classifying...");
            // CommandLine.java:151-155 -- "Writing results..." status lines.
            if let Some(loc) = &results_file_location {
                status.log(2, &format!("Writing results to {loc}"));
            } else {
                status.log(2, "Writing results...");
            }
            let text = classify_hierarchies(
                ontology,
                classes,
                object_properties,
                data_properties,
                pretty_print,
                &config,
            )?;
            // The classify dump already ends with newlines; write it verbatim
            // (no extra trailing newline) to match HierarchyDumperFSS output.
            output.write_raw(&text)
        }
        Task::Unsatisfiable => {
            // Java: EquivalentsAction("http://www.w3.org/2002/07/owl#Nothing")
            // (CommandLine.java:606-607). Reuses the same rendering as Task::Equivalents.
            status.log(2, "Finding equivalents of 'http://www.w3.org/2002/07/owl#Nothing'");
            let hierarchy = reasoner::classify_with_configuration(ontology, &config)?;
            let bottom = hierarchy.bottom_node();
            let nothing_iri = "http://www.w3.org/2002/07/owl#Nothing";
            let header_label = render_iri(prefixes, ignore_prefixes, nothing_iri);
            let names: Vec<String> = hierarchy
                .node(bottom)
                .equivalent_elements()
                .iter()
                .map(|c| c.0.to_string())
                // exclude internal: IRIs (Prefixes.isInternalIRI); owl:Nothing is kept
                .filter(|iri| !iri.starts_with("internal:"))
                .map(|iri| render_iri(prefixes, ignore_prefixes, &iri))
                .collect();
            output.println(&format!("Classes equivalent to '{header_label}':"))?;
            for name in &names {
                output.println(&format!("\t{name}"))?;
            }
            Ok(())
        }
        Task::Subs(name, direct) => {
            // CommandLine.java:237.
            status.log(2, &format!("Finding subs of '{name}'"));
            print_related(ontology, prefixes, ignore_prefixes, &build, &name, true, direct, &config, status, output)
        }
        Task::Supers(name, direct) => {
            // Java's SupersAction passes `false` to getSuperClasses in both
            // branches (CommandLine.java:206,210); --direct only changes the
            // printed header, not the set. Pass `direct` for the header;
            // print_related always forwards `false` to the reasoner for supers.
            // CommandLine.java:195.
            status.log(2, &format!("Finding supers of '{name}'"));
            print_related(ontology, prefixes, ignore_prefixes, &build, &name, false, direct, &config, status, output)
        }
        Task::Equivalents(name) => {
            // Java: EquivalentsAction.run (CommandLine.java:276-302).
            // Header uses abbreviateIRI(conceptName) or conceptName when ignoreOntologyPrefixes.
            status.log(2, &format!("Finding equivalents of '{name}'"));
            let iri = resolve_class_iri(prefixes, &name)?;
            let class = build.class(iri.clone());
            // isDefined warning uses conceptName (not conceptUri) — Java line 284 inconsistency preserved.
            if let Ok(false) = reasoner::is_defined_class(ontology, &class) {
                status.log(0, &format!("Warning: class '{name}' was not declared in the ontology."));
            }
            let equivalents =
                reasoner::equivalent_classes_with_configuration(ontology, &class, &config)?;
            let header_label = render_iri(prefixes, ignore_prefixes, &name);
            output.println(&format!("Classes equivalent to '{header_label}':"))?;
            for c in equivalents.iter() {
                let n = render_iri(prefixes, ignore_prefixes, &c.0.to_string());
                output.println(&format!("\t{n}"))?;
            }
            Ok(())
        }
        Task::PrintPrefixes => {
            // DumpPrefixesAction dumps `hermit.getPrefixes()` (Reasoner.java:229-255)
            // after the CLI has mutated it with the `-p` declarations
            // (CommandLine.java:771-778). `prefixes` is that exact object (built by
            // `build_reasoner_prefixes` before any action runs).
            // CommandLine.java:85-91: "Prefixes:" + tab-indented `name\tIRI` lines.
            output.println("Prefixes:")?;
            for (name, iri) in prefixes.prefix_iris_by_prefix_name() {
                output.println(&format!("\t{name}\t{iri}"))?;
            }
            Ok(())
        }
        Task::CheckEntailment(conclusion_iri) => {
            // EntailsAction (CommandLine.java:305-328): load the conclusion
            // ontology and report whether its logical axioms are entailed by the
            // (loaded) premise ontology. A load failure prints the stack trace and
            // is swallowed (Java catches OWLOntologyCreationException).
            status.log(2, "Checking whether the loaded ontology entails the conclusion ontology");
            let load_target = match iri_to_load_path(&conclusion_iri) {
                Ok(p) => p,
                Err(e) => {
                    // Mirror Java's e.printStackTrace(): report and continue.
                    eprintln!("{e}");
                    return Ok(());
                }
            };
            let (conclusion, _) = match load_ontology_with_prefixes(&load_target) {
                Ok(c) => c,
                Err(e) => {
                    eprintln!("{e}");
                    return Ok(());
                }
            };
            status.log(2, "Conclusion ontology loaded.");
            let axioms: Vec<Component<ArcStr>> =
                conclusion.iter().map(|ac| ac.component.clone()).collect();
            let entailed = reasoner::is_entailed_axioms(ontology, &axioms)?;
            // CommandLine.java:320.
            let not = if entailed { "" } else { "not " };
            status.log(2, &format!("Conclusion ontology is {not}entailed."));
            // Java prints the boolean (`output.println(isEntailed)`).
            output.println(&entailed.to_string())
        }
        Task::DumpClauses(dest) => {
            // DumpClausesAction (CommandLine.java 94-125): build the dump then
            // choose the sink.  When dest==Some(path), Java opens its own
            // FileOutputStream, overriding the global `-o` writer.
            let dl_ontology = clausify(ontology)?;
            let dump = if ignore_prefixes {
                dl_ontology.to_string_prefixes(&Prefixes::new())
            } else {
                dl_ontology.to_string_prefixes(prefixes)
            };
            match dest {
                DumpClausesSink::File(path) => {
                    // Java: new FileOutputStream(file) path (CommandLine.java 108-116).
                    // Java's output.println(dump) appends a trailing newline.
                    let mut f = File::create(&path)
                        .map_err(|_| format!("unable to open {path} for writing"))?;
                    f.write_all(dump.as_bytes())
                        .and_then(|_| f.write_all(b"\n"))
                        .map_err(|_| format!("unable to write to {path}"))?;
                    Ok(())
                }
                DumpClausesSink::Stdout => {
                    // `file.equals("-")`: force stdout, overriding any `-o` writer
                    // (CommandLine.java 102-103). Java's output.println appends a
                    // trailing newline.
                    print!("{dump}");
                    println!();
                    Ok(())
                }
                DumpClausesSink::GlobalOutput => {
                    // file==null: use the global output writer (`-o` if set, else
                    // stdout) via output.println (which appends a newline).
                    output.println(&dump)
                }
            }
        }
    }
}

/// Classifies the requested hierarchies and renders them in OWL functional
/// syntax, mirroring `Reasoner.dumpHierarchies` / `printHierarchies`
/// (`ClassifyAction.run`). The keyword pairs match `HierarchyDumperFSS`:
/// `EquivalentClasses`/`SubClassOf`, `EquivalentObjectProperties`/
/// `SubObjectPropertyOf`, `EquivalentDataProperties`/`SubDataPropertyOf`.
///
/// `pretty_print` selects the prettier `print_functional_syntax` printer (the
/// `HierarchyPrinterFSS` path) for the class hierarchy.
fn classify_hierarchies(
    ontology: &SetOntology<ArcStr>,
    classes: bool,
    object_properties: bool,
    data_properties: bool,
    pretty_print: bool,
    config: &Configuration,
) -> Result<String, String> {
    let mut sections: Vec<String> = Vec::new();
    if classes {
        let hierarchy = reasoner::classify_with_configuration(ontology, config)?;
        let section = if pretty_print {
            hierarchy.print_functional_syntax(|c| format!("<{}>", c.0))
        } else {
            hierarchy.dump_functional_syntax("EquivalentClasses", "SubClassOf", |c| {
                format!("<{}>", c.0)
            })
        };
        sections.push(section);
    }
    if object_properties {
        let hierarchy = reasoner::classify_object_properties_with_configuration(ontology, config)?;
        if pretty_print {
            // RolePrinter (HierarchyPrinterFSS.java:206-209): SubObjectPropertyOf /
            // EquivalentObjectProperties / Declaration( ObjectProperty( ... ) );
            // needsDeclaration (line 259-260) suppresses top/bottom AND inverse roles.
            let top_repr = "<http://www.w3.org/2002/07/owl#topObjectProperty>".to_string();
            let bottom_repr =
                "<http://www.w3.org/2002/07/owl#bottomObjectProperty>".to_string();
            sections.push(hierarchy.print_functional_syntax_with(
                |p| format!("<{}>", p.0),
                "SubObjectPropertyOf",
                "EquivalentObjectProperties",
                "ObjectProperty",
                |m: &str| m != top_repr && m != bottom_repr,
            ));
        } else {
            sections.push(hierarchy.dump_functional_syntax(
                "EquivalentObjectProperties",
                "SubObjectPropertyOf",
                |p| format!("<{}>", p.0),
            ));
        }
    }
    if data_properties {
        let hierarchy = reasoner::classify_data_properties_with_configuration(ontology, config)?;
        if pretty_print {
            // RolePrinter (HierarchyPrinterFSS.java:208-209): SubDataPropertyOf /
            // EquivalentDataProperties / Declaration( DataProperty( ... ) ).
            let top_repr = "<http://www.w3.org/2002/07/owl#topDataProperty>".to_string();
            let bottom_repr = "<http://www.w3.org/2002/07/owl#bottomDataProperty>".to_string();
            sections.push(hierarchy.print_functional_syntax_with(
                |p| format!("<{}>", p.0),
                "SubDataPropertyOf",
                "EquivalentDataProperties",
                "DataProperty",
                |m: &str| m != top_repr && m != bottom_repr,
            ));
        } else {
            // Use the java-data variant to reproduce the Java bug in
            // HierarchyDumperFSS.printDataPropertyHierarchy (line 127): non-first
            // EquivalentDataProperties members are emitted as ">iri>" not "<iri>".
            sections.push(hierarchy.dump_functional_syntax_java_data(
                "EquivalentDataProperties",
                "SubDataPropertyOf",
                |p| format!("<{}>", p.0),
                |p| format!(">{}>", p.0),
            ));
        }
    }
    // Each section already ends with \n\n (axioms + trailing blank line from
    // HierarchyDumperFSS.java:73/110/149), so concatenate verbatim; do NOT
    // filter or join — Java emits a blank line even for an empty section.
    Ok(sections.concat())
}

/// Runs the front-end clausification pipeline (normalize -> built-in property
/// axiomatization -> object-property inclusion rewriting -> clausify) and returns
/// the resulting `DLOntology`, mirroring `Reasoner.getDLOntology()` /
/// `reasoner::clausify_for_query` (which is private). Used by `--dump-clauses`.
fn clausify(ontology: &SetOntology<ArcStr>) -> Result<crate::model::DLOntology, String> {
    use crate::structural::{
        BuiltInPropertyManager, Configuration, ObjectPropertyInclusionManager,
        OWLAxioms, OWLAxiomsExpressivity, OWLClausification, OWLNormalization,
    };
    let mut normalization = OWLNormalization::new(OWLAxioms::new(), 0);
    normalization.process_ontology(ontology)?;
    let definitions_count = normalization.definitions_count();
    let mut axioms = normalization.into_axioms();
    BuiltInPropertyManager::new().axiomatize_built_in_properties_as_needed(&mut axioms);
    // preprocessAndClausify runs the object-property inclusion manager
    // unconditionally (it builds the automata and rewrites in every case).
    let manager = ObjectPropertyInclusionManager::new(&mut axioms)?;
    manager.rewrite_negative_object_property_assertions(&mut axioms, definitions_count);
    manager.rewrite_axioms(&mut axioms, 0)?;
    let expressivity = OWLAxiomsExpressivity::new(&axioms);
    OWLClausification::new(Configuration::default()).clausify(
        "http://hermit-rs/anonymous-ontology",
        &axioms,
        &expressivity,
    )
}

#[allow(clippy::too_many_arguments)]
fn print_related(
    ontology: &SetOntology<ArcStr>,
    prefixes: &Prefixes,
    ignore_prefixes: bool,
    build: &Build<ArcStr>,
    name: &str,
    subs: bool,
    direct: bool,
    config: &Configuration,
    status: &StatusOutput,
    output: &mut Output,
) -> Result<(), String> {
    let iri = resolve_class_iri(prefixes, name)?;
    let class = build.class(iri.clone());
    // isDefined warning (CommandLine.java 201-203 / 243-245): status level ALWAYS(0).
    if let Ok(false) = reasoner::is_defined_class(ontology, &class) {
        status.log(0, &format!("Warning: class '{iri}' was not declared in the ontology."));
    }
    // Java's SupersAction always calls getSuperClasses(owlClass, false) in both
    // the all and direct branches (CommandLine.java:206,210); only the header text
    // changes. SubsAction honours direct (CommandLine.java:248,252).
    let related = if subs {
        reasoner::sub_classes_with_configuration(ontology, &class, direct, config)?
    } else {
        reasoner::super_classes_with_configuration(ontology, &class, false, config)?
    };
    // Header uses raw conceptName (not resolved IRI), matching Java :207/211/249/253.
    let header = match (subs, direct) {
        (true, false) => format!("All sub-classes of '{name}':"),
        (true, true)  => format!("Direct sub-classes of '{name}':"),
        (false, false) => format!("All super-classes of '{name}':"),
        (false, true)  => format!("Direct super-classes of '{name}':"),
    };
    // One tab-indented entry per class in NodeSet order; no sort (CommandLine.java:213-223/255-265).
    output.println(&header)?;
    for c in related.iter() {
        output.println(&format!("\t{}", render_iri(prefixes, ignore_prefixes, &c.0.to_string())))?;
    }
    Ok(())
}

/// Java's `usageString` (CommandLine.java:355). Public for the binary's error
/// banner.
pub const USAGE: &str = "Usage: hermit [OPTION]... IRI...";

/// Java's `helpHeader` (CommandLine.java:356-378): the paragraphs printed between
/// the usage line and the generated option help.
const HELP_HEADER: &[&str] = &[
    "Perform reasoning on each OWL ontology IRI.",
    "Example: java -jar Hermit.jar -dsowl:Thing http://www.co-ode.org/ontologies/pizza/2005/05/16/pizza.owl",
    "    (prints direct subclasses of owl:Thing within the pizza ontology)",
    "Example: java -jar Hermit.jar --premise=http://km.aifb.uni-karlsruhe.de/projects/owltests/index.php/Special:GetOntology/New-Feature-DisjointObjectProperties-002?m=p --conclusion=http://km.aifb.uni-karlsruhe.de/projects/owltests/index.php/Special:GetOntology/New-Feature-DisjointObjectProperties-002?m=c --checkEntailment",
    "    (checks whether the conclusion ontology is entailed by the premise ontology)",
    "",
    "Both relative and absolute ontology IRIs can be used. Relative IRIs",
    "are resolved with respect to the current directory (i.e. local file",
    "names are valid IRIs); this behavior can be changed with the '--base'",
    "option.",
    "",
    "Classes and properties are identified using functional-syntax-style",
    "identifiers: names not containing a colon are resolved against the",
    "ontology's default prefix; otherwise the portion of the name",
    "preceding the colon is treated as a prefix prefix. Use of",
    "prefixes can be controlled using the -p, -N, and --prefix",
    "options. Alternatively, classes and properties can be identified with",
    "full IRIs by enclosing the IRI in <angle brackets>.",
    "",
    "By default, ontologies are simply retrieved and parsed. For more",
    "interesting reasoning, set one of the -c/-k/-s/-S/-e/-U options.",
];

/// Java's `footer` (CommandLine.java:379-382).
const FOOTER: &[&str] = &[
    "HermiT is a product of Oxford University.",
    "Visit <http://hermit-reasoner.org/> for details.",
];

// Java's option-group labels (CommandLine.java:383-389).
const K_MISC: &str = "Miscellaneous";
const K_ACTIONS: &str = "Actions";
const K_PREFIXES: &str = "Prefix name and IRI";
const K_ALGORITHM: &str = "Algorithm settings (expert users only!)";
const K_INTERNALS: &str = "Internals and debugging (unstable)";

/// Whether an option takes no argument, an optional argument or a required one
/// (Java's `enum Arg`, CommandLine.java:805).
#[derive(Clone, Copy, PartialEq)]
enum Arg {
    None,
    Optional,
    Required,
}

/// A single CLI option for help generation, mirroring Java's `Option`
/// (CommandLine.java:807-829). `opt_char` is `Some('x')` for short-charred
/// options and `None` for long-only ones (Java uses `optChar>=256` for those).
struct HelpOption {
    opt_char: Option<char>,
    long_str: &'static str,
    /// Group header printed before this option (Java prints it when `group!=null`;
    /// every entry in our table starts a group only at the boundaries, matching
    /// Java where each option's `group` field is set to repeat the same label).
    group: &'static str,
    arg: Arg,
    metavar: &'static str,
    help: &'static str,
}

impl HelpOption {
    /// Java's `getLongOptExampleStr` (CommandLine.java:838-842).
    fn long_opt_example_str(&self) -> String {
        if self.long_str.is_empty() {
            return String::new();
        }
        match self.arg {
            Arg::None => format!("--{}", self.long_str),
            Arg::Optional => format!("--{}[={}]", self.long_str, self.metavar),
            Arg::Required => format!("--{}={}", self.long_str, self.metavar),
        }
    }
}

/// The option table, mirroring `CommandLine.options` (CommandLine.java:391-430).
/// `group` repeats the same label for every option in a block, exactly as Java's
/// table does (each `new Option(...,kGroup,...)` sets the group field).
const OPTIONS: &[HelpOption] = &[
    // meta:
    HelpOption { opt_char: Some('h'), long_str: "help", group: K_MISC, arg: Arg::None, metavar: "", help: "display this help and exit" },
    HelpOption { opt_char: Some('V'), long_str: "version", group: K_MISC, arg: Arg::None, metavar: "", help: "display version information and exit" },
    HelpOption { opt_char: Some('v'), long_str: "verbose", group: K_MISC, arg: Arg::Optional, metavar: "AMOUNT", help: "increase verbosity by AMOUNT levels (default 1)" },
    HelpOption { opt_char: Some('q'), long_str: "quiet", group: K_MISC, arg: Arg::Optional, metavar: "AMOUNT", help: "decrease verbosity by AMOUNT levels (default 1)" },
    HelpOption { opt_char: Some('o'), long_str: "output", group: K_MISC, arg: Arg::Required, metavar: "FILE", help: "write output to FILE" },
    HelpOption { opt_char: None, long_str: "premise", group: K_MISC, arg: Arg::Required, metavar: "PREMISE", help: "set the premise ontology to PREMISE" },
    HelpOption { opt_char: None, long_str: "conclusion", group: K_MISC, arg: Arg::Required, metavar: "CONCLUSION", help: "set the conclusion ontology to CONCLUSION" },
    // actions:
    HelpOption { opt_char: Some('l'), long_str: "load", group: K_ACTIONS, arg: Arg::None, metavar: "", help: "parse and preprocess ontologies (default action)" },
    HelpOption { opt_char: Some('c'), long_str: "classify", group: K_ACTIONS, arg: Arg::None, metavar: "", help: "classify the classes of the ontology, optionally writing taxonomy to a file if -o (--output) is used" },
    HelpOption { opt_char: Some('O'), long_str: "classifyOPs", group: K_ACTIONS, arg: Arg::None, metavar: "", help: "classify the object properties of the ontology, optionally writing taxonomy to a file if -o (--output) is used" },
    HelpOption { opt_char: Some('D'), long_str: "classifyDPs", group: K_ACTIONS, arg: Arg::None, metavar: "", help: "classify the data properties of the ontology, optionally writing taxonomy to a file if -o (--output) is used" },
    HelpOption { opt_char: Some('P'), long_str: "prettyPrint", group: K_ACTIONS, arg: Arg::None, metavar: "", help: "when writing the classified hierarchy to a file, create a proper ontology and nicely indent the axioms according to their leven in the hierarchy" },
    HelpOption { opt_char: Some('k'), long_str: "consistency", group: K_ACTIONS, arg: Arg::Optional, metavar: "CLASS", help: "check satisfiability of CLASS (default owl:Thing)" },
    HelpOption { opt_char: Some('d'), long_str: "direct", group: K_ACTIONS, arg: Arg::None, metavar: "", help: "restrict next subs/supers call to only direct sub/superclasses" },
    HelpOption { opt_char: Some('s'), long_str: "subs", group: K_ACTIONS, arg: Arg::Required, metavar: "CLASS", help: "output classes subsumed by CLASS (or only direct subs if following --direct)" },
    HelpOption { opt_char: Some('S'), long_str: "supers", group: K_ACTIONS, arg: Arg::Required, metavar: "CLASS", help: "output classes subsuming CLASS (or only direct supers if following --direct)" },
    HelpOption { opt_char: Some('e'), long_str: "equivalents", group: K_ACTIONS, arg: Arg::Required, metavar: "CLASS", help: "output classes equivalent to CLASS" },
    HelpOption { opt_char: Some('U'), long_str: "unsatisfiable", group: K_ACTIONS, arg: Arg::None, metavar: "", help: "output unsatisfiable classes (equivalent to --equivalents=owl:Nothing)" },
    HelpOption { opt_char: None, long_str: "print-prefixes", group: K_ACTIONS, arg: Arg::None, metavar: "", help: "output prefix names available for use in identifiers" },
    HelpOption { opt_char: Some('E'), long_str: "checkEntailment", group: K_ACTIONS, arg: Arg::None, metavar: "", help: "check whether the premise (option premise) ontology entails the conclusion ontology (option conclusion)" },
    // prefixes:
    HelpOption { opt_char: Some('N'), long_str: "no-prefixes", group: K_PREFIXES, arg: Arg::None, metavar: "", help: "do not abbreviate or expand identifiers using prefixes defined in input ontology" },
    HelpOption { opt_char: Some('p'), long_str: "prefix", group: K_PREFIXES, arg: Arg::Required, metavar: "PN=IRI", help: "use PN as an abbreviation for IRI in identifiers" },
    HelpOption { opt_char: None, long_str: "prefix", group: K_PREFIXES, arg: Arg::Required, metavar: "IRI", help: "use IRI as the default identifier prefix" },
    // algorithm tweaks:
    HelpOption { opt_char: None, long_str: "block-match", group: K_ALGORITHM, arg: Arg::Required, metavar: "TYPE", help: "identify blocked nodes with TYPE blocking; supported values are 'single', 'pairwise', and 'optimal' (default 'optimal')" },
    HelpOption { opt_char: None, long_str: "block-strategy", group: K_ALGORITHM, arg: Arg::Required, metavar: "TYPE", help: "use TYPE as blocking strategy; supported values are 'ancestor', 'anywhere', 'core', and 'optimal' (default 'optimal')" },
    HelpOption { opt_char: None, long_str: "blockersCache", group: K_ALGORITHM, arg: Arg::None, metavar: "", help: "cache blocking nodes for use in later tests; not possible with nominals or core blocking" },
    HelpOption { opt_char: None, long_str: "ignoreUnsupportedDatatypes", group: K_ALGORITHM, arg: Arg::None, metavar: "", help: "ignore unsupported datatypes" },
    HelpOption { opt_char: None, long_str: "expansion-strategy", group: K_ALGORITHM, arg: Arg::Required, metavar: "TYPE", help: "use TYPE as existential expansion strategy; supported values are 'el', 'creation', 'reuse', and 'optimal' (default 'optimal')" },
    HelpOption { opt_char: None, long_str: "noInconsistentException", group: K_ALGORITHM, arg: Arg::None, metavar: "", help: "do not throw an exception for an inconsistent ontology" },
    // internals:
    HelpOption { opt_char: None, long_str: "dump-clauses", group: K_INTERNALS, arg: Arg::Optional, metavar: "FILE", help: "output DL-clauses to FILE (default stdout)" },
];

/// Java's `versionString` (CommandLine.java:348-354): the package implementation
/// version, falling back to `"<no version set>"` when unset. A Rust binary has no
/// JAR manifest, so we use the crate version `env!("CARGO_PKG_VERSION")` as the
/// documented analogue, with Java's null-fallback string when it is empty.
fn version_string() -> String {
    let version = env!("CARGO_PKG_VERSION");
    if version.is_empty() {
        "<no version set>".to_string()
    } else {
        version.to_string()
    }
}

/// Java's `formatOptionHelp` (CommandLine.java:844-885): groups, two-space
/// `-x, --long=META` columns padded to the widest long-example, then the help
/// text wrapped via `break_lines`.
fn format_option_help() -> String {
    let mut out = String::new();
    let field_width = OPTIONS
        .iter()
        .map(|o| o.long_opt_example_str().chars().count())
        .max()
        .unwrap_or(0);
    // Java emits a new group header before EVERY option whose group!=null; in the
    // table every option's group is set, so a label prints before each one. To
    // match the visible output (a header once per block) we print it only when it
    // changes -- which is what Java's repeated identical labels also reduce to
    // visually since identical consecutive headers are still emitted. We follow
    // Java literally: print the header before each option (group is always set).
    let line_sep = "\n";
    for o in OPTIONS {
        // Java: `if (o.group!=null) { out += sep + group + ":" + sep; }`.
        out.push_str(line_sep);
        out.push_str(o.group);
        out.push(':');
        out.push_str(line_sep);

        if let Some(c) = o.opt_char {
            out.push_str("  -");
            out.push(c);
            if !o.long_str.is_empty() {
                out.push_str(", ");
            } else {
                out.push_str("  ");
            }
        } else {
            out.push_str("      ");
        }
        let mut field_left: i64 = field_width as i64 + 1;
        if !o.long_str.is_empty() {
            let s = o.long_opt_example_str();
            field_left -= s.chars().count() as i64;
            out.push_str(&s);
        }
        while field_left > 0 {
            out.push(' ');
            field_left -= 1;
        }
        out.push_str(&break_lines(o.help, 80, 6 + field_width + 1));
        out.push_str(line_sep);
    }
    out
}

/// Java's `breakLines` (CommandLine.java:907-928): greedy word wrap at
/// `line_width`, continuation lines indented by `indent` spaces. Mirrors
/// `BreakIterator.getLineInstance()` by breaking after each run of non-space
/// followed by its trailing spaces.
fn break_lines(s: &str, line_width: usize, indent: usize) -> String {
    let mut out = String::new();
    let mut cur_line_pos = indent;
    for span in line_break_spans(s) {
        let span_len = span.chars().count();
        if cur_line_pos + span_len > line_width {
            out.push('\n');
            for _ in 0..indent {
                out.push(' ');
            }
            cur_line_pos = indent;
        }
        out.push_str(&span);
        cur_line_pos += span_len;
    }
    out
}

/// Splits `s` into the spans Java's line `BreakIterator` yields: each span is a
/// "word" together with the whitespace that follows it, so the wrapper can break
/// between words. The final span carries any trailing run.
fn line_break_spans(s: &str) -> Vec<String> {
    let mut spans: Vec<String> = Vec::new();
    let chars: Vec<char> = s.chars().collect();
    let mut i = 0;
    while i < chars.len() {
        let start = i;
        // Consume the word (non-space run).
        while i < chars.len() && chars[i] != ' ' {
            i += 1;
        }
        // Consume trailing spaces, which belong to this span (a break opportunity
        // occurs after the spaces).
        while i < chars.len() && chars[i] == ' ' {
            i += 1;
        }
        spans.push(chars[start..i].iter().collect());
    }
    spans
}

/// Java's `-h` output (CommandLine.java:464-473): usage line, help header
/// paragraphs, the generated option help, and the footer; each printed via
/// `System.out.println` so the whole text ends with a newline.
fn help_text() -> String {
    let mut lines: Vec<String> = Vec::new();
    lines.push(USAGE.to_string());
    for s in HELP_HEADER {
        lines.push((*s).to_string());
    }
    lines.push(format_option_help());
    for s in FOOTER {
        lines.push((*s).to_string());
    }
    format!("{}\n", lines.join("\n"))
}

#[cfg(test)]
mod tests {
    use super::*;

    // Mirrors `build_reasoner_prefixes` for an ontology `<http://example.org/pizza>`
    // whose default prefix `:` is `<http://example.org/pizza#>` (== ontologyIRI#)
    // and which declares `ex:`.
    fn ontology_prefixes() -> Prefixes {
        let mut p = Prefixes::new();
        p.declare_semantic_web_prefixes();
        let _ = p.declare_default_prefix("http://example.org/pizza#");
        let _ = p.declare_prefix("ex:", "http://example.org/ex#");
        p
    }

    #[test]
    fn help_and_version() {
        // Java's `-h` prints the usage line "Usage: hermit [OPTION]... IRI..." and
        // the generated option help; check for the usage banner and a known group.
        assert!(run(&["--help".to_string()]).unwrap().contains("Usage: hermit"));
        assert!(run(&["-h".to_string()]).unwrap().contains("Usage: hermit"));
        assert!(run(&["--help".to_string()]).unwrap().contains("Actions:"));
        // `--version` prints the crate version (the Rust analogue of Java's
        // package implementation version) followed by the Oxford footer.
        let v = env!("CARGO_PKG_VERSION");
        assert!(run(&["--version".to_string()]).unwrap().contains(v));
        assert!(run(&["--version".to_string()]).unwrap().contains("HermiT is a product of Oxford University."));
        assert!(run(&["-V".to_string()]).unwrap().contains(v));
        assert!(run(&["-V".to_string()]).unwrap().contains("HermiT is a product of Oxford University."));
    }

    #[test]
    fn missing_file_errors() {
        // No ontology argument at all -> "No ontologies given." usage error
        // (CommandLine.java:792, didSomething stays false).
        assert!(run(&["--consistency".to_string()]).is_err());
        // A missing ontology FILE is NOT a usage error: Java catches the load
        // failure per ontology ("It all went pear-shaped: ...") and continues,
        // so the overall run succeeds (CommandLine.java:786-791, didSomething true).
        assert!(run(&["does-not-exist.ofn".to_string()]).is_ok());
    }

    // Standard prefixes are available, so `owl:Thing` expands to the full
    // OWL IRI (CommandLine.java resolves every class arg via canBeExpanded /
    // expandAbbreviatedIRI before reasoning).
    #[test]
    fn expands_owl_thing() {
        let prefixes = ontology_prefixes();
        assert_eq!(
            resolve_class_iri(&prefixes, "owl:Thing").unwrap(),
            "http://www.w3.org/2002/07/owl#Thing"
        );
    }

    // A name against the ontology's default prefix (`:Dog`) resolves to the
    // declared default-prefix IRI.
    #[test]
    fn expands_default_prefix_name() {
        let prefixes = ontology_prefixes();
        assert_eq!(
            resolve_class_iri(&prefixes, ":Dog").unwrap(),
            "http://example.org/pizza#Dog"
        );
    }

    // A named ontology prefix (`ex:Foo`) resolves against the declared IRI.
    #[test]
    fn expands_named_ontology_prefix() {
        let prefixes = ontology_prefixes();
        assert_eq!(
            resolve_class_iri(&prefixes, "ex:Foo").unwrap(),
            "http://example.org/ex#Foo"
        );
    }

    // A full IRI wrapped in <> has the angle brackets stripped and is passed
    // through unchanged (it cannot be expanded).
    #[test]
    fn strips_angle_brackets_on_full_iri() {
        let prefixes = ontology_prefixes();
        assert_eq!(
            resolve_class_iri(&prefixes, "<http://example.org/Cat>").unwrap(),
            "http://example.org/Cat"
        );
        // A bare full IRI (no <>) is left untouched.
        assert_eq!(
            resolve_class_iri(&prefixes, "http://example.org/Cat").unwrap(),
            "http://example.org/Cat"
        );
    }

    // A CLI `-p PN=IRI` mapping is registered and used for expansion (mirrors
    // CommandLine.java 623-630 declarePrefix).
    #[test]
    fn cli_prefix_mapping() {
        // A CLI `-p cli:=IRI` mapping is applied last via declarePrefix.
        let mut prefixes = Prefixes::new();
        prefixes.declare_semantic_web_prefixes();
        let _ = prefixes.declare_prefix("cli:", "http://cli.example/#");
        assert_eq!(
            resolve_class_iri(&prefixes, "cli:Foo").unwrap(),
            "http://cli.example/#Foo"
        );
    }

    // `--print-prefixes` must include CLI `-p` declarations, because Java mutates
    // the very `getPrefixes()` object that DumpPrefixesAction dumps with each `-p`
    // mapping (CommandLine.java:771-778 + 84-91).
    #[test]
    fn print_prefixes_includes_cli_prefix() {
        let dir = std::env::temp_dir();
        let path = dir.join(format!(
            "hermit_print_prefixes_{}_{}.ofn",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::write(
            &path,
            "Prefix(:=<http://example.org/#>)\nOntology(<http://example.org/test>)\n",
        )
        .unwrap();
        let out = run(&[
            "--print-prefixes".to_string(),
            "-p".to_string(),
            "cli:=http://cli.example/#".to_string(),
            path.to_string_lossy().to_string(),
        ])
        .unwrap();
        let _ = std::fs::remove_file(&path);
        assert!(
            out.contains("cli:\thttp://cli.example/#"),
            "CLI -p declaration missing from --print-prefixes output:\n{out}"
        );
    }

    // -p without '=' is a usage error (Java case 'p', CommandLine.java:626-628).
    #[test]
    fn prefix_without_eq_is_error() {
        let raw: Vec<String> = vec!["-p".to_string(), "noequalssign".to_string()];
        // expand_short_opts passes -p through; the main loop must reject it.
        let args = expand_short_opts(&raw).unwrap();
        // Drive a minimal parse that hits the -p arm.
        let mut prefix_mappings: Vec<(String, String)> = Vec::new();
        let mut i = 0;
        let mut result: Result<(), String> = Ok(());
        while i < args.len() {
            if args[i] == "-p" {
                i += 1;
                let value = arg_value(&args, i, "--prefix").unwrap();
                match value.split_once('=') {
                    Some((name, iri)) => {
                        let name = if name.ends_with(':') { name.to_string() } else { format!("{name}:") };
                        prefix_mappings.push((name, iri.to_string()));
                    }
                    None => {
                        result = Err(format!("the prefix declaration '{value}' is not of the form PN=IRI."));
                        break;
                    }
                }
            }
            i += 1;
        }
        assert!(result.is_err(), "expected error for -p without '='");
        let msg = result.unwrap_err();
        assert!(msg.contains("not of the form PN=IRI"), "got: {msg}");
    }

    // `--no-prefixes` renders full IRIs; default abbreviates.
    #[test]
    fn render_iri_honours_no_prefixes() {
        let prefixes = ontology_prefixes();
        let thing = "http://www.w3.org/2002/07/owl#Thing";
        assert_eq!(render_iri(&prefixes, true, thing), thing);
        assert_eq!(render_iri(&prefixes, false, thing), "owl:Thing");
    }

    // `--subs` honours `--direct` (Java SubsAction, CommandLine.java:247-253).
    // `--supers` **ignores** `--direct` at the reasoner level (Java
    // SupersAction always passes false, CommandLine.java:205-211); the
    // parsed Task::Supers still stores the flag for fidelity, but dispatch
    // hardcodes `false`.
    #[test]
    fn direct_flag_parsing_matches_java_doall_semantics() {
        // No --direct: both default to transitive (direct == false).
        match parse_task(&["--subs", "A"]) {
            Some(Task::Subs(_, direct)) => assert!(!direct, "subs default must be transitive"),
            other => panic!("expected Subs task, got {other:?}"),
        }
        match parse_task(&["--supers", "A"]) {
            Some(Task::Supers(_, direct)) => assert!(!direct, "supers default must be transitive"),
            other => panic!("expected Supers task, got {other:?}"),
        }
        // --direct before --subs restricts to direct (SubsAction honours it).
        match parse_task(&["--direct", "--subs", "A"]) {
            Some(Task::Subs(_, direct)) => assert!(direct, "--direct must restrict subs"),
            other => panic!("expected Subs task, got {other:?}"),
        }
        // -d -S A: the flag IS stored in the Task (parse fidelity) even though
        // dispatch ignores it for supers (SupersAction always uses full set).
        match parse_task(&["-d", "-S", "A"]) {
            Some(Task::Supers(_, direct)) => assert!(direct, "-d must be stored in Supers task (even though dispatch ignores it)"),
            other => panic!("expected Supers task, got {other:?}"),
        }
    }

    // Each new action flag parses to the right Task, matching its Java option.
    #[test]
    fn classify_ops_flag_parses() {
        match parse_task(&["-O"]) {
            Some(Task::Classify { object_properties, classes, data_properties, .. }) => {
                assert!(object_properties && !classes && !data_properties);
            }
            other => panic!("expected Classify(OPs), got {other:?}"),
        }
        match parse_task(&["--classifyOPs"]) {
            Some(Task::Classify { object_properties, .. }) => assert!(object_properties),
            other => panic!("expected Classify(OPs), got {other:?}"),
        }
    }

    #[test]
    fn classify_dps_flag_parses() {
        match parse_task(&["-D"]) {
            Some(Task::Classify { data_properties, .. }) => assert!(data_properties),
            other => panic!("expected Classify(DPs), got {other:?}"),
        }
    }

    #[test]
    fn pretty_print_flag_parses() {
        match parse_task(&["-c", "-P"]) {
            Some(Task::Classify { classes, pretty_print, .. }) => {
                assert!(classes && pretty_print);
            }
            other => panic!("expected Classify(pretty), got {other:?}"),
        }
    }

    #[test]
    fn print_prefixes_flag_parses() {
        assert_eq!(parse_task(&["--print-prefixes"]), Some(Task::PrintPrefixes));
    }

    #[test]
    fn dump_clauses_flag_parses() {
        assert_eq!(
            parse_task(&["--dump-clauses"]),
            Some(Task::DumpClauses(DumpClausesSink::GlobalOutput))
        );
        assert_eq!(
            parse_task(&["--dump-clauses=out.txt"]),
            Some(Task::DumpClauses(DumpClausesSink::File("out.txt".to_string())))
        );
        assert_eq!(
            parse_task(&["--dump-clauses=-"]),
            Some(Task::DumpClauses(DumpClausesSink::Stdout))
        );
    }

    #[test]
    fn load_flag_is_noop() {
        // -l alone leaves the task at the default (Consistency); no error.
        assert_eq!(parse_task(&["-l"]), None);
    }

    // --- Short-option clustering / attached-value tests ---
    // Mirrors gnu.getopt behaviour driven by CommandLine.java lines 458, 887-905
    // and the help example `-dsowl:Thing` (line 358).

    // `-dsowl:Thing` clusters `-d` (no-arg) then `-s` (required-arg) with
    // remainder `owl:Thing` as its value. Equivalent to `-d -s owl:Thing`.
    #[test]
    fn cluster_ds_owl_thing() {
        match parse_task(&["-dsowl:Thing"]) {
            Some(Task::Subs(cls, direct)) => {
                assert_eq!(cls, "owl:Thing");
                assert!(direct, "-d prefix must set direct");
            }
            other => panic!("expected Subs task, got {other:?}"),
        }
        // Explicit spaced form must produce the same result.
        match parse_task(&["-d", "-s", "owl:Thing"]) {
            Some(Task::Subs(cls, direct)) => {
                assert_eq!(cls, "owl:Thing");
                assert!(direct);
            }
            other => panic!("expected Subs, got {other:?}"),
        }
    }

    // `-sowl:Thing`: attached value for a single required-arg option.
    #[test]
    fn attached_value_s_owl_thing() {
        match parse_task(&["-sowl:Thing"]) {
            Some(Task::Subs(cls, false)) => assert_eq!(cls, "owl:Thing"),
            other => panic!("expected Subs(owl:Thing, false), got {other:?}"),
        }
    }

    // `-Sowl:Thing`: capital -S (supers) with attached value.
    #[test]
    fn attached_value_capital_s_owl_thing() {
        match parse_task(&["-Sowl:Thing"]) {
            Some(Task::Supers(cls, false)) => assert_eq!(cls, "owl:Thing"),
            other => panic!("expected Supers(owl:Thing, false), got {other:?}"),
        }
    }

    // `-k` is an OPTIONAL_ARGUMENT option: gnu.getopt takes its CLASS value only
    // from the attached form, never from a following separate token. A bare `-k`
    // (or `-k SomeClass`, where `SomeClass` is a positional ontology) defaults to
    // owl:Thing; `-kFoo` / `--consistency=Foo` set the class to `Foo`.
    #[test]
    fn consistency_optional_argument_getopt_semantics() {
        // bare -k → owl:Thing
        assert_eq!(
            parse_task(&["-k"]),
            Some(Task::Satisfiability("http://www.w3.org/2002/07/owl#Thing".to_string()))
        );
        // -k Foo: Foo is NOT consumed as the class (it stays a positional ontology),
        // so the satisfiability target defaults to owl:Thing.
        assert_eq!(
            parse_task(&["-k", "Foo"]),
            Some(Task::Satisfiability("http://www.w3.org/2002/07/owl#Thing".to_string()))
        );
        // attached short form -kFoo
        assert_eq!(
            parse_task(&["-kFoo"]),
            Some(Task::Satisfiability("Foo".to_string()))
        );
        // attached long form --consistency=Foo
        assert_eq!(
            parse_task(&["--consistency=Foo"]),
            Some(Task::Satisfiability("Foo".to_string()))
        );
    }

    // `-eFoo`: equivalents with attached value.
    #[test]
    fn attached_value_e_foo() {
        match parse_task(&["-eFoo"]) {
            Some(Task::Equivalents(cls)) => assert_eq!(cls, "Foo"),
            other => panic!("expected Equivalents(Foo), got {other:?}"),
        }
    }

    // `-ds`: bare cluster of two no-arg/required-arg options where `-s` is the
    // last char and its value comes from the next argv token.
    #[test]
    fn cluster_ds_separate_value() {
        match parse_task(&["-ds", "owl:Thing"]) {
            Some(Task::Subs(cls, direct)) => {
                assert_eq!(cls, "owl:Thing");
                assert!(direct);
            }
            other => panic!("expected Subs, got {other:?}"),
        }
    }

    // `-cOP` clusters -c, -O, -P (all no-arg).
    #[test]
    fn cluster_no_arg_cop() {
        match parse_task(&["-cOP"]) {
            Some(Task::Classify { classes, object_properties, pretty_print, .. }) => {
                assert!(classes, "-c not set");
                assert!(object_properties, "-O not set");
                assert!(pretty_print, "-P not set");
            }
            other => panic!("expected Classify, got {other:?}"),
        }
    }

    // An unknown short char inside a cluster is an error.
    #[test]
    fn unknown_short_char_in_cluster_errors() {
        let raw: Vec<String> = vec!["-dX".to_string()];
        assert!(expand_short_opts(&raw).is_err());
    }

    // -E with --conclusion produces a CheckEntailment task carrying the IRI.
    // Order-sensitive, matching Java (CommandLine.java:610-613): the conclusion
    // must already have been parsed when -E is seen, otherwise -E is a no-op.
    #[test]
    fn check_entailment_premise_conclusion_pair() {
        let task = parse_task(&["--conclusion", "concl.ofn", "--checkEntailment"]);
        assert_eq!(task, Some(Task::CheckEntailment("concl.ofn".to_string())));
        let task = parse_task(&["--conclusion", "c.ofn", "-E"]);
        assert_eq!(task, Some(Task::CheckEntailment("c.ofn".to_string())));
        // -E before --conclusion is silently a no-op (Java does not add the action).
        let task = parse_task(&["--checkEntailment", "--conclusion", "concl.ofn"]);
        assert_eq!(task, None);
    }

    // `-E`/--checkEntailment WITHOUT --conclusion adds no action (CommandLine.java
    // `case 'E'` only adds EntailsAction when conclusionIRI!=null) -- a silent
    // no-op, not a usage error. The premise file failing to load is swallowed and
    // continues, so the run completes successfully.
    #[test]
    fn check_entailment_without_conclusion_is_noop() {
        assert!(run(&["-E".to_string(), "x.ofn".to_string()]).is_ok());
    }

    // -o/--output records the output path (and -o - is stdout / no file).
    #[test]
    fn output_path_parses() {
        assert_eq!(parse_output(&["-o", "result.txt"]), Some("result.txt".to_string()));
        assert_eq!(parse_output(&["--output", "r.txt"]), Some("r.txt".to_string()));
        assert_eq!(parse_output(&["-o", "-"]), None);
    }

    // --- Tableau-tuning options (CommandLine.java's kAlgorithm group) ---

    // --block-strategy maps each Java-accepted value to the right
    // BlockingStrategyType (Configuration.blocking_strategy_type), incl. Java's
    // `core` -> SIMPLE_CORE mapping; an unknown value errors with Java's text.
    #[test]
    fn block_strategy_maps_to_configuration() {
        assert_eq!(parse_block_strategy("anywhere").unwrap(), BlockingStrategyType::Anywhere);
        assert_eq!(parse_block_strategy("ancestor").unwrap(), BlockingStrategyType::Ancestor);
        assert_eq!(parse_block_strategy("core").unwrap(), BlockingStrategyType::SimpleCore);
        assert_eq!(parse_block_strategy("optimal").unwrap(), BlockingStrategyType::Optimal);
        // Case-insensitive, as Java lower-cases the argument.
        assert_eq!(parse_block_strategy("ANYWHERE").unwrap(), BlockingStrategyType::Anywhere);
        let err = parse_block_strategy("bogus").unwrap_err();
        assert!(err.contains("unknown blocking strategy type 'bogus'"), "got: {err}");
    }

    // --block-match -> Configuration.direct_blocking_type (incl. pairwise ->
    // PairWise); unknown value errors.
    #[test]
    fn block_match_maps_to_configuration() {
        assert_eq!(parse_direct_block("single").unwrap(), DirectBlockingType::Single);
        assert_eq!(parse_direct_block("pairwise").unwrap(), DirectBlockingType::PairWise);
        assert_eq!(parse_direct_block("optimal").unwrap(), DirectBlockingType::Optimal);
        let err = parse_direct_block("nope").unwrap_err();
        assert!(err.contains("unknown direct blocking type 'nope'"), "got: {err}");
    }

    // --expansion-strategy -> Configuration.existential_strategy_type (incl. reuse
    // -> IndividualReuse); unknown value errors.
    #[test]
    fn expansion_strategy_maps_to_configuration() {
        assert_eq!(
            parse_expansion_strategy("creation").unwrap(),
            ExistentialStrategyType::CreationOrder
        );
        assert_eq!(parse_expansion_strategy("el").unwrap(), ExistentialStrategyType::El);
        assert_eq!(
            parse_expansion_strategy("reuse").unwrap(),
            ExistentialStrategyType::IndividualReuse
        );
        let err = parse_expansion_strategy("xyz").unwrap_err();
        assert!(err.contains("unknown existential strategy type 'xyz'"), "got: {err}");
    }

    // Full option-loop dispatch: each tuning flag writes the right Configuration
    // field, starting from Configuration::default().
    #[test]
    fn tuning_flags_dispatch_to_config_fields() {
        let c = parse_config(&["--block-strategy", "ancestor"]).unwrap();
        assert_eq!(c.blocking_strategy_type, BlockingStrategyType::Ancestor);

        let c = parse_config(&["--block-match", "single"]).unwrap();
        assert_eq!(c.direct_blocking_type, DirectBlockingType::Single);

        let c = parse_config(&["--expansion-strategy", "el"]).unwrap();
        assert_eq!(c.existential_strategy_type, ExistentialStrategyType::El);

        let c = parse_config(&["--blockersCache"]).unwrap();
        assert_eq!(c.blocking_signature_cache_type, BlockingSignatureCacheType::Cached);

        let c = parse_config(&["--ignoreUnsupportedDatatypes"]).unwrap();
        assert!(c.ignore_unsupported_datatypes);

        let c = parse_config(&["--noInconsistentException"]).unwrap();
        assert!(!c.throw_inconsistent_ontology_exception);

        // Attached `=VALUE` form works too.
        let c = parse_config(&["--block-strategy=anywhere"]).unwrap();
        assert_eq!(c.blocking_strategy_type, BlockingStrategyType::Anywhere);
    }

    // CRITICAL: with no tuning flag the constructed Configuration equals
    // Configuration::default(), so default reasoner behaviour is unchanged.
    #[test]
    fn no_tuning_flag_yields_default_config() {
        let c = parse_config(&["-k"]).unwrap();
        let d = Configuration::default();
        assert_eq!(c.blocking_strategy_type, d.blocking_strategy_type);
        assert_eq!(c.direct_blocking_type, d.direct_blocking_type);
        assert_eq!(c.blocking_signature_cache_type, d.blocking_signature_cache_type);
        assert_eq!(c.existential_strategy_type, d.existential_strategy_type);
        assert_eq!(c.ignore_unsupported_datatypes, d.ignore_unsupported_datatypes);
        assert_eq!(
            c.throw_inconsistent_ontology_exception,
            d.throw_inconsistent_ontology_exception
        );
    }

    // An invalid value is rejected end-to-end (the error surfaces from `run`
    // before any file is loaded), matching Java's UsageException.
    #[test]
    fn invalid_tuning_value_errors_in_run() {
        let err = run(&["--block-strategy".to_string(), "bogus".to_string()]).unwrap_err();
        assert!(err.contains("unknown blocking strategy type 'bogus'"), "got: {err}");
    }

    // Mirror of `run`'s option loop, returning the first Task without loading an
    // ontology. Used to assert each new flag parses to the right action.
    // Returns the first task in the Vec (sufficient for all single-action tests).
    fn parse_task(args: &[&str]) -> Option<Task> {
        parse(args).0.into_iter().next()
    }

    // Returns the full ordered task list, for multi-action tests.
    fn parse_tasks(args: &[&str]) -> Vec<Task> {
        parse(args).0
    }

    // Re-runs the real config arms of `run`'s option loop (using the production
    // mapping functions) to build the Configuration the flags select.
    fn parse_config(args: &[&str]) -> Result<Configuration, String> {
        let args: Vec<String> = args.iter().map(|s| s.to_string()).collect();
        let mut config = Configuration::default();
        let mut i = 0;
        while i < args.len() {
            match args[i].as_str() {
                "--block-strategy" => {
                    i += 1;
                    config.blocking_strategy_type = parse_block_strategy(&args[i])?;
                }
                "--block-match" => {
                    i += 1;
                    config.direct_blocking_type = parse_direct_block(&args[i])?;
                }
                "--expansion-strategy" => {
                    i += 1;
                    config.existential_strategy_type = parse_expansion_strategy(&args[i])?;
                }
                "--blockersCache" => {
                    config.blocking_signature_cache_type = BlockingSignatureCacheType::Cached;
                }
                "--ignoreUnsupportedDatatypes" => config.ignore_unsupported_datatypes = true,
                "--noInconsistentException" => {
                    config.throw_inconsistent_ontology_exception = false;
                }
                v if v.starts_with("--block-strategy=") => {
                    config.blocking_strategy_type =
                        parse_block_strategy(v.trim_start_matches("--block-strategy="))?;
                }
                v if v.starts_with("--block-match=") => {
                    config.direct_blocking_type =
                        parse_direct_block(v.trim_start_matches("--block-match="))?;
                }
                v if v.starts_with("--expansion-strategy=") => {
                    config.existential_strategy_type =
                        parse_expansion_strategy(v.trim_start_matches("--expansion-strategy="))?;
                }
                _ => {}
            }
            i += 1;
        }
        Ok(config)
    }

    fn parse_output(args: &[&str]) -> Option<String> {
        parse(args).1
    }

    // Multiple actions run in order (Java LinkedList<Action>, CommandLine.java:444, 781-787).
    // -s A -S B must produce BOTH Subclasses and Superclasses sections.
    #[test]
    fn multiple_actions_subs_then_supers() {
        let tasks = parse_tasks(&["-s", "A", "-S", "B"]);
        assert_eq!(tasks.len(), 2, "expected 2 tasks, got {}", tasks.len());
        assert!(matches!(tasks[0], Task::Subs(ref cls, _) if cls == "A"),
            "first task must be Subs(A), got {:?}", tasks[0]);
        assert!(matches!(tasks[1], Task::Supers(ref cls, _) if cls == "B"),
            "second task must be Supers(B), got {:?}", tasks[1]);
    }

    // -c -s A: Subs(A) is pushed first (during loop), Classify is appended last
    // after the loop (Java CommandLine.java:732-733), so classify runs after subs.
    #[test]
    fn classify_appended_after_subs_in_order() {
        let tasks = parse_tasks(&["-c", "-s", "A"]);
        assert_eq!(tasks.len(), 2, "expected 2 tasks, got {}", tasks.len());
        assert!(matches!(tasks[0], Task::Subs(ref cls, _) if cls == "A"),
            "first task must be Subs(A), got {:?}", tasks[0]);
        assert!(matches!(tasks[1], Task::Classify { classes: true, .. }),
            "second task must be Classify{{classes:true}}, got {:?}", tasks[1]);
    }

    // A faithful re-implementation of `run`'s argument loop (without the I/O), so
    // the new argument parsing can be exercised in isolation.
    fn parse(args: &[&str]) -> (Vec<Task>, Option<String>) {
        let raw: Vec<String> = args.iter().map(|s| s.to_string()).collect();
        let args = expand_short_opts(&raw).expect("expand_short_opts failed in test");
        let mut tasks: Vec<Task> = Vec::new();
        let mut direct = false;
        let mut classify_classes = false;
        let mut classify_ops = false;
        let mut classify_dps = false;
        let mut pretty_print = false;
        let mut output_file: Option<String> = None;
        let mut conclusion: Option<String> = None;
        let mut i = 0;
        while i < args.len() {
            match args[i].as_str() {
                "--load" | "-l" | "--verbose" | "-v" | "--quiet" | "-q" => {}
                "--consistency" | "-k" => {
                    tasks.push(Task::Satisfiability(
                        "http://www.w3.org/2002/07/owl#Thing".to_string(),
                    ));
                }
                v if v.starts_with("--consistency=") || v.starts_with("-k=") => {
                    tasks.push(Task::Satisfiability(v.split_once('=').unwrap().1.to_string()));
                }
                "--classify" | "-c" => classify_classes = true,
                "--classifyOPs" | "-O" => classify_ops = true,
                "--classifyDPs" | "-D" => classify_dps = true,
                "--prettyPrint" | "-P" => pretty_print = true,
                "--unsatisfiable" | "-U" => tasks.push(Task::Unsatisfiable),
                "--print-prefixes" => tasks.push(Task::PrintPrefixes),
                "--checkEntailment" | "-E" => {
                    if let Some(c) = &conclusion {
                        tasks.push(Task::CheckEntailment(c.clone()));
                    }
                }
                "--dump-clauses" => tasks.push(Task::DumpClauses(DumpClausesSink::GlobalOutput)),
                "--no-prefixes" | "-N" => {}
                "--output" | "-o" => {
                    i += 1;
                    if args[i] != "-" {
                        output_file = Some(args[i].clone());
                    }
                }
                "--conclusion" => {
                    i += 1;
                    conclusion = Some(args[i].clone());
                }
                "--direct" | "-d" => {
                    direct = true;
                    i += 1;
                    continue;
                }
                "--subs" | "-s" => {
                    i += 1;
                    tasks.push(Task::Subs(args[i].clone(), direct));
                    direct = false;
                }
                "--supers" | "-S" => {
                    i += 1;
                    tasks.push(Task::Supers(args[i].clone(), direct));
                    direct = false;
                }
                "--equivalents" | "-e" => {
                    i += 1;
                    tasks.push(Task::Equivalents(args[i].clone()));
                }
                value if value.starts_with("--dump-clauses=") => {
                    let dest = value.trim_start_matches("--dump-clauses=").to_string();
                    tasks.push(Task::DumpClauses(if dest == "-" {
                        DumpClausesSink::Stdout
                    } else {
                        DumpClausesSink::File(dest)
                    }));
                }
                _ => {}
            }
            i += 1;
        }
        if classify_classes || classify_ops || classify_dps {
            tasks.push(Task::Classify {
                classes: classify_classes,
                object_properties: classify_ops,
                data_properties: classify_dps,
                pretty_print,
                results_file_location: None,
            });
        }
        (tasks, output_file)
    }
}
