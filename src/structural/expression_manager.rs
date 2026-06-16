// Port of org.semanticweb.HermiT.structural.ExpressionManager.
//
// Computes negation normal form (NNF), the NNF of a complement, and structural
// simplification for class expressions and data ranges. The OWL-API
// `...VisitorEx` visitors become recursive methods here; the OWL-API data
// factory is replaced by direct horned-owl enum construction.
//
// OWL-API stores n-ary operands as canonical (sorted, duplicate-free) sets;
// `canonical` reproduces that, relying on horned-owl's `Ord`/`Eq` on
// `ClassExpression` and `DataRange`.

use horned_owl::model::{Build, ClassExpression as CE, DataRange as DR, Datatype};

use super::{ClassExpr, DataRangeExpr};

const OWL_THING: &str = "http://www.w3.org/2002/07/owl#Thing";
const OWL_NOTHING: &str = "http://www.w3.org/2002/07/owl#Nothing";
const RDFS_LITERAL: &str = "http://www.w3.org/2000/01/rdf-schema#Literal";

pub struct ExpressionManager {
    build: Build<super::A>,
    top_datatype: Datatype<super::A>,
}

fn canonical<T: Ord>(mut v: Vec<T>) -> Vec<T> {
    v.sort();
    v.dedup();
    v
}

impl ExpressionManager {
    pub fn new() -> ExpressionManager {
        let build = Build::new_arc();
        let top_datatype = build.datatype(RDFS_LITERAL);
        ExpressionManager { build, top_datatype }
    }

    fn owl_thing(&self) -> ClassExpr {
        CE::Class(self.build.class(OWL_THING))
    }
    fn owl_nothing(&self) -> ClassExpr {
        CE::Class(self.build.class(OWL_NOTHING))
    }
    fn top_datatype(&self) -> DataRangeExpr {
        DR::Datatype(self.top_datatype.clone())
    }

    fn is_owl_thing(ce: &ClassExpr) -> bool {
        matches!(ce, CE::Class(c) if c.is_thing())
    }
    fn is_owl_nothing(ce: &ClassExpr) -> bool {
        matches!(ce, CE::Class(c) if c.is_nothing())
    }
    fn is_top_datatype(&self, dr: &DataRangeExpr) -> bool {
        matches!(dr, DR::Datatype(dt) if dt == &self.top_datatype)
    }

    // -----------------------------------------------------------------------
    // NNF
    // -----------------------------------------------------------------------

    pub fn get_nnf(&self, description: &ClassExpr) -> ClassExpr {
        match description {
            CE::Class(_) | CE::ObjectOneOf(_) | CE::DataHasValue { .. } => description.clone(),
            CE::ObjectIntersectionOf(operands) => {
                CE::ObjectIntersectionOf(canonical(operands.iter().map(|d| self.get_nnf(d)).collect()))
            }
            CE::ObjectUnionOf(operands) => {
                CE::ObjectUnionOf(canonical(operands.iter().map(|d| self.get_nnf(d)).collect()))
            }
            CE::ObjectComplementOf(operand) => self.get_complement_nnf(operand),
            CE::ObjectSomeValuesFrom { ope, bce } => CE::ObjectSomeValuesFrom {
                ope: ope.clone(),
                bce: Box::new(self.get_nnf(bce)),
            },
            CE::ObjectAllValuesFrom { ope, bce } => CE::ObjectAllValuesFrom {
                ope: ope.clone(),
                bce: Box::new(self.get_nnf(bce)),
            },
            CE::ObjectHasValue { .. } | CE::ObjectHasSelf(_) => description.clone(),
            CE::ObjectMinCardinality { n, ope, bce } => CE::ObjectMinCardinality {
                n: *n,
                ope: ope.clone(),
                bce: Box::new(self.get_nnf(bce)),
            },
            CE::ObjectMaxCardinality { n, ope, bce } => CE::ObjectMaxCardinality {
                n: *n,
                ope: ope.clone(),
                bce: Box::new(self.get_nnf(bce)),
            },
            CE::ObjectExactCardinality { n, ope, bce } => CE::ObjectExactCardinality {
                n: *n,
                ope: ope.clone(),
                bce: Box::new(self.get_nnf(bce)),
            },
            CE::DataSomeValuesFrom { dp, dr } => CE::DataSomeValuesFrom {
                dp: dp.clone(),
                dr: self.get_nnf_data(dr),
            },
            CE::DataAllValuesFrom { dp, dr } => CE::DataAllValuesFrom {
                dp: dp.clone(),
                dr: self.get_nnf_data(dr),
            },
            CE::DataMinCardinality { n, dp, dr } => CE::DataMinCardinality {
                n: *n,
                dp: dp.clone(),
                dr: self.get_nnf_data(dr),
            },
            CE::DataMaxCardinality { n, dp, dr } => CE::DataMaxCardinality {
                n: *n,
                dp: dp.clone(),
                dr: self.get_nnf_data(dr),
            },
            CE::DataExactCardinality { n, dp, dr } => CE::DataExactCardinality {
                n: *n,
                dp: dp.clone(),
                dr: self.get_nnf_data(dr),
            },
        }
    }

    pub fn get_nnf_data(&self, data_range: &DataRangeExpr) -> DataRangeExpr {
        match data_range {
            DR::Datatype(_) | DR::DataOneOf(_) | DR::DatatypeRestriction(..) => data_range.clone(),
            DR::DataComplementOf(operand) => self.get_complement_nnf_data(operand),
            DR::DataIntersectionOf(operands) => {
                DR::DataIntersectionOf(canonical(operands.iter().map(|d| self.get_nnf_data(d)).collect()))
            }
            DR::DataUnionOf(operands) => {
                DR::DataUnionOf(canonical(operands.iter().map(|d| self.get_nnf_data(d)).collect()))
            }
        }
    }

    // -----------------------------------------------------------------------
    // Complement NNF
    // -----------------------------------------------------------------------

    pub fn get_complement_nnf(&self, description: &ClassExpr) -> ClassExpr {
        match description {
            CE::Class(c) => {
                if c.is_thing() {
                    self.owl_nothing()
                } else if c.is_nothing() {
                    self.owl_thing()
                } else {
                    CE::ObjectComplementOf(Box::new(description.clone()))
                }
            }
            CE::ObjectIntersectionOf(operands) => CE::ObjectUnionOf(canonical(
                operands.iter().map(|d| self.get_complement_nnf(d)).collect(),
            )),
            CE::ObjectUnionOf(operands) => CE::ObjectIntersectionOf(canonical(
                operands.iter().map(|d| self.get_complement_nnf(d)).collect(),
            )),
            CE::ObjectComplementOf(operand) => self.get_nnf(operand),
            CE::ObjectOneOf(_) => CE::ObjectComplementOf(Box::new(description.clone())),
            CE::ObjectSomeValuesFrom { ope, bce } => CE::ObjectAllValuesFrom {
                ope: ope.clone(),
                bce: Box::new(self.get_complement_nnf(bce)),
            },
            CE::ObjectAllValuesFrom { ope, bce } => CE::ObjectSomeValuesFrom {
                ope: ope.clone(),
                bce: Box::new(self.get_complement_nnf(bce)),
            },
            CE::ObjectHasValue { .. } | CE::ObjectHasSelf(_) => {
                CE::ObjectComplementOf(Box::new(self.get_nnf(description)))
            }
            CE::ObjectMinCardinality { n, ope, bce } => {
                if *n == 0 {
                    self.owl_nothing()
                } else {
                    CE::ObjectMaxCardinality {
                        n: *n - 1,
                        ope: ope.clone(),
                        bce: Box::new(self.get_nnf(bce)),
                    }
                }
            }
            CE::ObjectMaxCardinality { n, ope, bce } => CE::ObjectMinCardinality {
                n: *n + 1,
                ope: ope.clone(),
                bce: Box::new(self.get_nnf(bce)),
            },
            CE::ObjectExactCardinality { n, ope, bce } => {
                let filler = self.get_nnf(bce);
                if *n == 0 {
                    CE::ObjectMinCardinality {
                        n: 1,
                        ope: ope.clone(),
                        bce: Box::new(filler),
                    }
                } else {
                    CE::ObjectUnionOf(canonical(vec![
                        CE::ObjectMaxCardinality {
                            n: *n - 1,
                            ope: ope.clone(),
                            bce: Box::new(filler.clone()),
                        },
                        CE::ObjectMinCardinality {
                            n: *n + 1,
                            ope: ope.clone(),
                            bce: Box::new(filler),
                        },
                    ]))
                }
            }
            CE::DataSomeValuesFrom { dp, dr } => CE::DataAllValuesFrom {
                dp: dp.clone(),
                dr: self.get_complement_nnf_data(dr),
            },
            CE::DataAllValuesFrom { dp, dr } => CE::DataSomeValuesFrom {
                dp: dp.clone(),
                dr: self.get_complement_nnf_data(dr),
            },
            CE::DataHasValue { .. } => CE::ObjectComplementOf(Box::new(description.clone())),
            CE::DataMinCardinality { n, dp, dr } => {
                if *n == 0 {
                    self.owl_nothing()
                } else {
                    CE::DataMaxCardinality {
                        n: *n - 1,
                        dp: dp.clone(),
                        dr: self.get_nnf_data(dr),
                    }
                }
            }
            CE::DataMaxCardinality { n, dp, dr } => CE::DataMinCardinality {
                n: *n + 1,
                dp: dp.clone(),
                dr: self.get_nnf_data(dr),
            },
            CE::DataExactCardinality { n, dp, dr } => {
                let filler = self.get_nnf_data(dr);
                if *n == 0 {
                    CE::DataMinCardinality {
                        n: 1,
                        dp: dp.clone(),
                        dr: filler,
                    }
                } else {
                    CE::ObjectUnionOf(canonical(vec![
                        CE::DataMaxCardinality {
                            n: *n - 1,
                            dp: dp.clone(),
                            dr: filler.clone(),
                        },
                        CE::DataMinCardinality {
                            n: *n + 1,
                            dp: dp.clone(),
                            dr: filler,
                        },
                    ]))
                }
            }
        }
    }

    pub fn get_complement_nnf_data(&self, data_range: &DataRangeExpr) -> DataRangeExpr {
        match data_range {
            DR::Datatype(_) | DR::DataOneOf(_) | DR::DatatypeRestriction(..) => {
                DR::DataComplementOf(Box::new(data_range.clone()))
            }
            DR::DataComplementOf(operand) => self.get_nnf_data(operand),
            DR::DataIntersectionOf(operands) => DR::DataUnionOf(canonical(
                operands.iter().map(|d| self.get_complement_nnf_data(d)).collect(),
            )),
            DR::DataUnionOf(operands) => DR::DataIntersectionOf(canonical(
                operands.iter().map(|d| self.get_complement_nnf_data(d)).collect(),
            )),
        }
    }

    // -----------------------------------------------------------------------
    // Simplification
    // -----------------------------------------------------------------------

    pub fn get_simplified(&self, description: &ClassExpr) -> ClassExpr {
        match description {
            CE::Class(_) | CE::ObjectOneOf(_) => description.clone(),
            CE::ObjectIntersectionOf(operands) => {
                let mut new_conjuncts: Vec<ClassExpr> = Vec::new();
                for description in operands {
                    let simplified = self.get_simplified(description);
                    if Self::is_owl_thing(&simplified) {
                        continue;
                    } else if Self::is_owl_nothing(&simplified) {
                        return self.owl_nothing();
                    } else if let CE::ObjectIntersectionOf(inner) = simplified {
                        new_conjuncts.extend(inner);
                    } else {
                        new_conjuncts.push(simplified);
                    }
                }
                CE::ObjectIntersectionOf(canonical(new_conjuncts))
            }
            CE::ObjectUnionOf(operands) => {
                let mut new_disjuncts: Vec<ClassExpr> = Vec::new();
                for description in operands {
                    let simplified = self.get_simplified(description);
                    if Self::is_owl_thing(&simplified) {
                        return self.owl_thing();
                    } else if Self::is_owl_nothing(&simplified) {
                        continue;
                    } else if let CE::ObjectUnionOf(inner) = simplified {
                        new_disjuncts.extend(inner);
                    } else {
                        new_disjuncts.push(simplified);
                    }
                }
                CE::ObjectUnionOf(canonical(new_disjuncts))
            }
            CE::ObjectComplementOf(operand) => {
                let simplified = self.get_simplified(operand);
                if Self::is_owl_thing(&simplified) {
                    self.owl_nothing()
                } else if Self::is_owl_nothing(&simplified) {
                    self.owl_thing()
                } else if let CE::ObjectComplementOf(inner) = simplified {
                    *inner
                } else {
                    CE::ObjectComplementOf(Box::new(simplified))
                }
            }
            CE::ObjectSomeValuesFrom { ope, bce } => {
                let filler = self.get_simplified(bce);
                if Self::is_owl_nothing(&filler) {
                    self.owl_nothing()
                } else {
                    CE::ObjectSomeValuesFrom { ope: ope.clone(), bce: Box::new(filler) }
                }
            }
            CE::ObjectAllValuesFrom { ope, bce } => {
                let filler = self.get_simplified(bce);
                if Self::is_owl_thing(&filler) {
                    self.owl_thing()
                } else {
                    CE::ObjectAllValuesFrom { ope: ope.clone(), bce: Box::new(filler) }
                }
            }
            CE::ObjectHasValue { ope, i } => CE::ObjectSomeValuesFrom {
                ope: ope.clone(),
                bce: Box::new(CE::ObjectOneOf(vec![i.clone()])),
            },
            CE::ObjectHasSelf(ope) => CE::ObjectHasSelf(ope.clone()),
            CE::ObjectMinCardinality { n, ope, bce } => {
                let filler = self.get_simplified(bce);
                if *n == 0 {
                    self.owl_thing()
                } else if Self::is_owl_nothing(&filler) {
                    self.owl_nothing()
                } else if *n == 1 {
                    CE::ObjectSomeValuesFrom { ope: ope.clone(), bce: Box::new(filler) }
                } else {
                    CE::ObjectMinCardinality { n: *n, ope: ope.clone(), bce: Box::new(filler) }
                }
            }
            CE::ObjectMaxCardinality { n, ope, bce } => {
                let filler = self.get_simplified(bce);
                if Self::is_owl_nothing(&filler) {
                    self.owl_thing()
                } else if *n == 0 {
                    CE::ObjectAllValuesFrom {
                        ope: ope.clone(),
                        bce: Box::new(CE::ObjectComplementOf(Box::new(filler))),
                    }
                } else {
                    CE::ObjectMaxCardinality { n: *n, ope: ope.clone(), bce: Box::new(filler) }
                }
            }
            CE::ObjectExactCardinality { n, ope, bce } => {
                let filler = self.get_simplified(bce);
                if *n == 0 {
                    CE::ObjectAllValuesFrom {
                        ope: ope.clone(),
                        bce: Box::new(CE::ObjectComplementOf(Box::new(filler))),
                    }
                } else if Self::is_owl_nothing(&filler) {
                    self.owl_nothing()
                } else {
                    CE::ObjectIntersectionOf(canonical(vec![
                        CE::ObjectMinCardinality {
                            n: *n,
                            ope: ope.clone(),
                            bce: Box::new(filler.clone()),
                        },
                        CE::ObjectMaxCardinality {
                            n: *n,
                            ope: ope.clone(),
                            bce: Box::new(filler),
                        },
                    ]))
                }
            }
            CE::DataSomeValuesFrom { dp, dr } => {
                let filler = self.get_simplified_data(dr);
                if self.is_bottom_data_range(&filler) {
                    self.owl_nothing()
                } else {
                    CE::DataSomeValuesFrom { dp: dp.clone(), dr: filler }
                }
            }
            CE::DataAllValuesFrom { dp, dr } => {
                let filler = self.get_simplified_data(dr);
                if self.is_top_datatype(&filler) {
                    self.owl_thing()
                } else {
                    CE::DataAllValuesFrom { dp: dp.clone(), dr: filler }
                }
            }
            CE::DataHasValue { dp, l } => CE::DataSomeValuesFrom {
                dp: dp.clone(),
                dr: DR::DataOneOf(vec![l.clone()]),
            },
            CE::DataMinCardinality { n, dp, dr } => {
                let filler = self.get_simplified_data(dr);
                if *n == 0 {
                    self.owl_thing()
                } else if self.is_bottom_data_range(&filler) {
                    self.owl_nothing()
                } else if *n == 1 {
                    CE::DataSomeValuesFrom { dp: dp.clone(), dr: filler }
                } else {
                    CE::DataMinCardinality { n: *n, dp: dp.clone(), dr: filler }
                }
            }
            CE::DataMaxCardinality { n, dp, dr } => {
                let filler = self.get_simplified_data(dr);
                if self.is_bottom_data_range(&filler) {
                    self.owl_thing()
                } else if *n == 0 {
                    CE::DataAllValuesFrom {
                        dp: dp.clone(),
                        dr: DR::DataComplementOf(Box::new(filler)),
                    }
                } else {
                    CE::DataMaxCardinality { n: *n, dp: dp.clone(), dr: filler }
                }
            }
            CE::DataExactCardinality { n, dp, dr } => {
                let filler = self.get_simplified_data(dr);
                if *n == 0 {
                    CE::DataAllValuesFrom {
                        dp: dp.clone(),
                        dr: DR::DataComplementOf(Box::new(filler)),
                    }
                } else if self.is_bottom_data_range(&filler) {
                    self.owl_nothing()
                } else {
                    CE::ObjectIntersectionOf(canonical(vec![
                        CE::DataMinCardinality {
                            n: *n,
                            dp: dp.clone(),
                            dr: filler.clone(),
                        },
                        CE::DataMaxCardinality { n: *n, dp: dp.clone(), dr: filler },
                    ]))
                }
            }
        }
    }

    pub fn get_simplified_data(&self, data_range: &DataRangeExpr) -> DataRangeExpr {
        match data_range {
            DR::Datatype(_) | DR::DataOneOf(_) | DR::DatatypeRestriction(..) => data_range.clone(),
            DR::DataComplementOf(operand) => {
                let simplified = self.get_simplified_data(operand);
                if let DR::DataComplementOf(inner) = simplified {
                    *inner
                } else {
                    DR::DataComplementOf(Box::new(simplified))
                }
            }
            DR::DataIntersectionOf(operands) => {
                let mut new_conjuncts: Vec<DataRangeExpr> = Vec::new();
                for dr in operands {
                    let simplified = self.get_simplified_data(dr);
                    if self.is_top_datatype(&simplified) {
                        continue;
                    } else if let DR::DataIntersectionOf(inner) = simplified {
                        new_conjuncts.extend(inner);
                    } else {
                        new_conjuncts.push(simplified);
                    }
                }
                DR::DataIntersectionOf(canonical(new_conjuncts))
            }
            DR::DataUnionOf(operands) => {
                let mut new_disjuncts: Vec<DataRangeExpr> = Vec::new();
                for dr in operands {
                    let simplified = self.get_simplified_data(dr);
                    if self.is_top_datatype(&simplified) {
                        return self.top_datatype();
                    } else if let DR::DataUnionOf(inner) = simplified {
                        new_disjuncts.extend(inner);
                    } else {
                        new_disjuncts.push(simplified);
                    }
                }
                DR::DataUnionOf(canonical(new_disjuncts))
            }
        }
    }

    fn is_bottom_data_range(&self, data_range: &DataRangeExpr) -> bool {
        matches!(data_range, DR::DataComplementOf(inner) if self.is_top_datatype(inner))
    }
}

impl Default for ExpressionManager {
    fn default() -> Self {
        ExpressionManager::new()
    }
}

#[cfg(test)]
mod tests {
    //! These tests pin the invariant on which the `normalize_class_expression`
    //! and clausifier panic sites rely: HermiT's
    //! `ExpressionManager.getSimplified` PROVABLY eliminates `ObjectHasValue`,
    //! `ObjectExactCardinality`, `DataHasValue` and `DataExactCardinality` before
    //! those expressions ever reach normalization/clausification. They mirror
    //! Java `DescriptionSimplificationVisitor` exactly, so the corresponding
    //! `panic!("Internal error: ... should have been simplified.")` arms are
    //! faithful `IllegalStateException` defensive invariants, never reachable on
    //! valid OWL 2 DL input.

    use super::*;
    use horned_owl::model::{Individual, Literal, ObjectPropertyExpression as OPE};

    fn build() -> Build<super::super::A> {
        Build::new_arc()
    }

    /// `getSimplified(ObjectHasValue(p, a))` ==>
    /// `ObjectSomeValuesFrom(p, ObjectOneOf(a))`. No `ObjectHasValue` remains.
    #[test]
    fn object_has_value_is_rewritten_to_some_values_from_nominal() {
        let b = build();
        let em = ExpressionManager::new();
        let p = OPE::ObjectProperty(b.object_property("http://ex/p"));
        let a = Individual::Named(b.named_individual("http://ex/a"));
        let expr = CE::ObjectHasValue { ope: p.clone(), i: a.clone() };

        let simplified = em.get_simplified(&expr);
        match simplified {
            CE::ObjectSomeValuesFrom { ope, bce } => {
                assert_eq!(ope, p);
                assert_eq!(*bce, CE::ObjectOneOf(vec![a]));
            }
            other => panic!("ObjectHasValue should simplify to SomeValuesFrom(oneOf), got {other:?}"),
        }
    }

    /// `getSimplified(ObjectExactCardinality(2, p, C))` ==>
    /// `ObjectIntersectionOf(Min(2,p,C), Max(2,p,C))`. No `ObjectExactCardinality`
    /// remains.
    #[test]
    fn object_exact_cardinality_is_rewritten_to_min_and_max() {
        let b = build();
        let em = ExpressionManager::new();
        let p = OPE::ObjectProperty(b.object_property("http://ex/p"));
        let c = CE::Class(b.class("http://ex/C"));
        let expr = CE::ObjectExactCardinality { n: 2, ope: p.clone(), bce: Box::new(c.clone()) };

        let simplified = em.get_simplified(&expr);
        match simplified {
            CE::ObjectIntersectionOf(operands) => {
                assert_eq!(operands.len(), 2);
                assert!(operands.iter().any(|o| matches!(
                    o,
                    CE::ObjectMinCardinality { n: 2, ope, bce }
                        if *ope == p && **bce == c
                )));
                assert!(operands.iter().any(|o| matches!(
                    o,
                    CE::ObjectMaxCardinality { n: 2, ope, bce }
                        if *ope == p && **bce == c
                )));
            }
            other => panic!("ObjectExactCardinality should simplify to Min ⊓ Max, got {other:?}"),
        }
    }

    /// Exact-0 is the special case: `getSimplified(ObjectExactCardinality(0,p,C))`
    /// ==> `ObjectAllValuesFrom(p, ¬C)` (Java `visit(OWLObjectExactCardinality)`
    /// `getCardinality()==0` branch). Still no `ObjectExactCardinality` remains.
    #[test]
    fn object_exact_cardinality_zero_is_rewritten_to_all_values_complement() {
        let b = build();
        let em = ExpressionManager::new();
        let p = OPE::ObjectProperty(b.object_property("http://ex/p"));
        let c = CE::Class(b.class("http://ex/C"));
        let expr = CE::ObjectExactCardinality { n: 0, ope: p.clone(), bce: Box::new(c.clone()) };

        let simplified = em.get_simplified(&expr);
        match simplified {
            CE::ObjectAllValuesFrom { ope, bce } => {
                assert_eq!(ope, p);
                assert_eq!(*bce, CE::ObjectComplementOf(Box::new(c)));
            }
            other => panic!("ObjectExactCardinality(0) should simplify to AllValues(¬C), got {other:?}"),
        }
    }

    /// `getSimplified(DataHasValue(dp, l))` ==>
    /// `DataSomeValuesFrom(dp, DataOneOf(l))`. No `DataHasValue` remains.
    #[test]
    fn data_has_value_is_rewritten_to_some_values_from_one_of() {
        let b = build();
        let em = ExpressionManager::new();
        let dp = b.data_property("http://ex/dp");
        let l = Literal::Simple { literal: "v".to_string() };
        let expr = CE::DataHasValue { dp: dp.clone(), l: l.clone() };

        let simplified = em.get_simplified(&expr);
        match simplified {
            CE::DataSomeValuesFrom { dp: out_dp, dr } => {
                assert_eq!(out_dp, dp);
                assert_eq!(dr, DR::DataOneOf(vec![l]));
            }
            other => panic!("DataHasValue should simplify to DataSomeValuesFrom(oneOf), got {other:?}"),
        }
    }

    /// `getSimplified(DataExactCardinality(2, dp, dr))` ==>
    /// `ObjectIntersectionOf(DataMin(2,dp,dr), DataMax(2,dp,dr))`. No
    /// `DataExactCardinality` remains.
    #[test]
    fn data_exact_cardinality_is_rewritten_to_min_and_max() {
        let b = build();
        let em = ExpressionManager::new();
        let dp = b.data_property("http://ex/dp");
        let dr = DR::Datatype(b.datatype("http://www.w3.org/2001/XMLSchema#integer"));
        let expr = CE::DataExactCardinality { n: 2, dp: dp.clone(), dr: dr.clone() };

        let simplified = em.get_simplified(&expr);
        match simplified {
            CE::ObjectIntersectionOf(operands) => {
                assert_eq!(operands.len(), 2);
                assert!(operands
                    .iter()
                    .any(|o| matches!(o, CE::DataMinCardinality { n: 2, .. })));
                assert!(operands
                    .iter()
                    .any(|o| matches!(o, CE::DataMaxCardinality { n: 2, .. })));
            }
            other => panic!("DataExactCardinality should simplify to DataMin ⊓ DataMax, got {other:?}"),
        }
    }

    /// Nested unions: `getSimplified` flattens `Union(a, Union(b, c))` into a
    /// single `Union(a, b, c)` (Java `visit(OWLObjectUnionOf)` flattening
    /// branch). This underpins the `normalize_inclusions` outer-union handling,
    /// so a nested `ObjectUnionOf` never reaches the `panic!("OR should be broken
    /// down")` arm with un-flattened structure.
    #[test]
    fn nested_union_is_flattened() {
        let em = ExpressionManager::new();
        let b = build();
        let a = CE::Class(b.class("http://ex/A"));
        let c = CE::Class(b.class("http://ex/C"));
        let d = CE::Class(b.class("http://ex/D"));
        let nested = CE::ObjectUnionOf(vec![
            a.clone(),
            CE::ObjectUnionOf(vec![c.clone(), d.clone()]),
        ]);

        let simplified = em.get_simplified(&nested);
        match simplified {
            CE::ObjectUnionOf(operands) => {
                assert_eq!(operands.len(), 3, "nested union must be flattened to 3 disjuncts");
                assert!(operands.contains(&a));
                assert!(operands.contains(&c));
                assert!(operands.contains(&d));
                assert!(
                    !operands.iter().any(|o| matches!(o, CE::ObjectUnionOf(_))),
                    "no nested ObjectUnionOf should remain"
                );
            }
            other => panic!("nested union should flatten to one ObjectUnionOf, got {other:?}"),
        }
    }

    /// Double negation: `getSimplified(¬¬C)` ==> `C` (Java
    /// `visit(OWLObjectComplementOf)` `instanceof OWLObjectComplementOf` branch).
    #[test]
    fn double_complement_is_collapsed() {
        let em = ExpressionManager::new();
        let b = build();
        let c = CE::Class(b.class("http://ex/C"));
        let double = CE::ObjectComplementOf(Box::new(CE::ObjectComplementOf(Box::new(c.clone()))));
        assert_eq!(em.get_simplified(&double), c);
    }

    /// Nested data complement collapses too: `getSimplified_data(¬¬dr)` ==> `dr`.
    #[test]
    fn double_data_complement_is_collapsed() {
        let em = ExpressionManager::new();
        let b = build();
        let dr = DR::Datatype(b.datatype("http://www.w3.org/2001/XMLSchema#integer"));
        let double = DR::DataComplementOf(Box::new(DR::DataComplementOf(Box::new(dr.clone()))));
        assert_eq!(em.get_simplified_data(&double), dr);
    }
}
