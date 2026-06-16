//! # hermit-rs
//!
//! A Rust port of the [HermiT](http://www.hermit-reasoner.com/) OWL 2 DL
//! reasoner, built on [`horned_owl`]. The logic is translated faithfully,
//! class-by-class, from HermiT's original Java sources (LGPL-3.0).
//!
//! The modules mirror the corresponding HermiT Java packages:
//!
//! - [`model`]      -- `org.semanticweb.HermiT.model` (the DL data model)
//! - [`structural`] -- normalization and clausification of OWL axioms
//! - [`tableau`]    -- the hypertableau engine (hyperresolution, merging,
//!   blocking integration, dependency-directed backtracking)
//! - [`blocking`]   -- the blocking strategies that ensure termination
//! - [`existentials`] -- existential-expansion strategies
//! - [`hierarchy`] / [`quasi_order`] -- classification and the class hierarchy
//! - [`datatype_value`] -- datatype value-space reasoning
//! - [`reasoner`]   -- the public reasoning API (consistency, classification,
//!   entailment, instance retrieval)
//! - [`datalog`], [`prefixes`], [`intern`], [`graph`], [`configuration`],
//!   [`monitor`], [`cli`] -- supporting infrastructure

pub mod graph;
pub mod configuration;
pub mod datatype_value;
pub mod existentials;
pub mod hierarchy;
pub mod instance_manager;
pub mod intern;
pub mod model;
pub mod monitor;
pub mod node_set;
pub mod prefixes;
pub mod quasi_order;
pub mod reasoner;
pub mod blocking;
pub mod cli;
pub mod datalog;
pub mod debugger;
pub mod string_automaton;
pub mod structural;
pub mod tableau;
