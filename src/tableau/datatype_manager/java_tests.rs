//! Checked operation traces from the original Java datatype tests.
use super::*;
use serde_json::Value;
fn constant(v: &Value) -> Constant {
    Constant::create(
        v["lexical"].as_str().unwrap(),
        v["datatype"].as_str().unwrap(),
    )
}
fn expected_value(v: &Value) -> DataValue {
    if v["datatype"].as_str().unwrap().ends_with("#PlainLiteral") {
        let (string, lang) = v["lexical"].as_str().unwrap().rsplit_once('@').unwrap();
        return if lang.is_empty() {
            DataValue::Text(string.into())
        } else {
            DataValue::LangString {
                string: string.into(),
                lang: lang.into(),
            }
        };
    }
    parse_value(&constant(v)).expect("valid Java value")
}
// Independently invert the parsed timeline to check Java's original dateTime
// parsing/printing round-trip assertions. Java and Rust use different origins
// and BCE calendars internally, so raw implementation timestamps are not an oracle.
fn date_lexical(value: &DataValue) -> String {
    let DataValue::DateTime {
        instant,
        has_tz,
        tz_offset,
    } = value
    else {
        panic!("dateTime")
    };
    let fraction = format!("{:0<3}", instant.fraction);
    assert_eq!(fraction.len(), 3, "millisecond instant");
    let millis = i64::try_from(&instant.seconds).unwrap() * 1000 + fraction.parse::<i64>().unwrap();
    let local = millis + i64::from(*tz_offset) * 60_000;
    let days = local.div_euclid(86_400_000);
    let day_ms = local.rem_euclid(86_400_000);
    let z = days + 719468;
    let era = z.div_euclid(146097);
    let doe = z - era * 146097;
    let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365;
    let mut year = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let day = doy - (153 * mp + 2) / 5 + 1;
    let month = mp + if mp < 10 { 3 } else { -9 };
    year += i64::from(month <= 2);
    let year = if year < 0 {
        format!("-{:04}", -year)
    } else {
        format!("{year:04}")
    };
    let mut out = format!(
        "{year}-{month:02}-{day:02}T{:02}:{:02}:{:02}",
        day_ms / 3_600_000,
        (day_ms / 60_000) % 60,
        (day_ms / 1000) % 60
    );
    if day_ms % 1000 != 0 {
        out.push_str(&format!(".{:03}", day_ms % 1000));
    }
    if *has_tz {
        if *tz_offset == 0 {
            out.push('Z');
        } else {
            out.push_str(&format!(
                "{}{:02}:{:02}",
                if *tz_offset < 0 { '-' } else { '+' },
                tz_offset.abs() / 60,
                tz_offset.abs() % 60
            ));
        }
    }
    out
}
fn run(name: &str) {
    if crate::java_test_support::isolated(&format!(
        "tableau::datatype_manager::java_tests::{}",
        name.replace('.', "_")
    )) {
        return;
    }
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/java/cases")
        .join(format!("{name}.json"));
    let case: Value = serde_json::from_str(&std::fs::read_to_string(path).unwrap()).unwrap();
    assert_eq!(case["java_errors"], serde_json::json!([]));
    let mut rows = case["operations"].as_array().unwrap().clone();
    crate::java_test_support::corrections::correct(name, &mut rows);
    for (index, row) in rows.iter().enumerate() {
        let ranges: Vec<_> = row["ranges"]
            .as_array()
            .unwrap()
            .iter()
            .map(|r| {
                let facets = r["facets"].as_array().unwrap();
                let dr = DatatypeRestriction::create(
                    r["datatype"].as_str().unwrap(),
                    facets
                        .iter()
                        .map(|f| f[0].as_str().unwrap().to_string())
                        .collect(),
                    facets.iter().map(|f| constant(&f[1])).collect(),
                );
                (
                    if r["negated"].as_bool().unwrap() {
                        dr.get_negation()
                    } else {
                        LiteralDataRange::DatatypeRestriction(dr)
                    },
                    (),
                )
            })
            .collect();
        let expected = &row["expected"];
        let argument = &row["argument"];
        let context = format!("{name} operation {index}: {}", row["operation"]);
        match row["operation"].as_str().unwrap() {
            "parse" => {
                let actual = parse_value(&constant(argument));
                if expected["datatype"]
                    .as_str()
                    .is_some_and(|s| s.ends_with("#dateTime"))
                {
                    assert_eq!(
                        date_lexical(actual.as_ref().expect("valid dateTime")),
                        expected["lexical"].as_str().unwrap(),
                        "{context}"
                    );
                }
                if expected.is_null() {
                    assert!(actual.is_none(), "{context}: {actual:?}");
                } else {
                    assert!(
                        actual
                            .as_ref()
                            .is_some_and(|v| values_equal(v, &expected_value(expected))),
                        "{context}: {actual:?} != {expected}"
                    );
                }
            }
            "contains" => {
                let value = expected_value(argument);
                assert_eq!(
                    ranges
                        .iter()
                        .all(|(r, _)| value_in_range(&value, r) == Some(true)),
                    expected.as_bool().unwrap(),
                    "{context}"
                );
            }
            "cardinality" | "subtract" | "infinite" | "enumerate" => {
                let space = node_value_space(None, &ranges);
                let count = match &space {
                    NodeValueSpace::Infinite => u128::MAX,
                    NodeValueSpace::Finite { count, .. } => *count,
                };
                match row["operation"].as_str().unwrap() {
                    "cardinality" => assert_eq!(
                        count >= u128::from(argument.as_u64().unwrap()),
                        expected.as_bool().unwrap(),
                        "{context}: {count}"
                    ),
                    "subtract" => assert_eq!(
                        u128::from(argument.as_u64().unwrap()).saturating_sub(count),
                        u128::from(expected.as_u64().unwrap()),
                        "{context}"
                    ),
                    "infinite" => assert!(matches!(space, NodeValueSpace::Infinite), "{context}"),
                    "enumerate" => {
                        let values = match space {
                            NodeValueSpace::Finite {
                                values: Some(v), ..
                            } => v,
                            NodeValueSpace::Finite { count, .. } => materialize_finite_value_space(
                                &ranges,
                                usize::try_from(count).unwrap() + 1,
                            )
                            .expect("finite space is enumerable"),
                            _ => panic!("{context}: unexpectedly infinite"),
                        };
                        let expected: Vec<_> = expected
                            .as_array()
                            .unwrap()
                            .iter()
                            .map(expected_value)
                            .collect();
                        assert_eq!(values.len(), expected.len(), "{context}");
                        for v in expected {
                            assert!(
                                values.iter().any(|a| values_equal(a, &v)),
                                "{context}: missing {v:?}"
                            );
                        }
                    }
                    _ => unreachable!(),
                }
            }
            other => panic!("unhandled datatype operation {other}"),
        }
    }
}
#[test]
#[allow(non_snake_case)]
fn reasoner_AnyURITest_testComplement2() {
    run("reasoner.AnyURITest.testComplement2");
}
#[test]
#[allow(non_snake_case)]
fn reasoner_AnyURITest_testComplement3() {
    run("reasoner.AnyURITest.testComplement3");
}
#[test]
#[allow(non_snake_case)]
fn reasoner_AnyURITest_testComplement4() {
    run("reasoner.AnyURITest.testComplement4");
}
#[test]
#[allow(non_snake_case)]
fn reasoner_AnyURITest_testInvalidAnyURILiterals() {
    run("reasoner.AnyURITest.testInvalidAnyURILiterals");
}
#[test]
#[allow(non_snake_case)]
fn reasoner_AnyURITest_testPatternAndLength2() {
    run("reasoner.AnyURITest.testPatternAndLength2");
}
#[test]
#[allow(non_snake_case)]
fn reasoner_AnyURITest_testPatternAndLength3() {
    run("reasoner.AnyURITest.testPatternAndLength3");
}
#[test]
#[allow(non_snake_case)]
fn reasoner_BinaryDataTest_testBase64Parsing() {
    run("reasoner.BinaryDataTest.testBase64Parsing");
}
#[test]
#[allow(non_snake_case)]
fn reasoner_BinaryDataTest_testEnumerate1() {
    run("reasoner.BinaryDataTest.testEnumerate1");
}
#[test]
#[allow(non_snake_case)]
fn reasoner_BinaryDataTest_testEnumerate2() {
    run("reasoner.BinaryDataTest.testEnumerate2");
}
#[test]
#[allow(non_snake_case)]
fn reasoner_BinaryDataTest_testExplicitSize() {
    run("reasoner.BinaryDataTest.testExplicitSize");
}
#[test]
#[allow(non_snake_case)]
fn reasoner_DateTimeTest_testExactIntervalsWithTZ1() {
    run("reasoner.DateTimeTest.testExactIntervalsWithTZ1");
}
#[test]
#[allow(non_snake_case)]
fn reasoner_DateTimeTest_testExactIntervalsWithTZ2() {
    run("reasoner.DateTimeTest.testExactIntervalsWithTZ2");
}
#[test]
#[allow(non_snake_case)]
fn reasoner_DateTimeTest_testExactIntervalsWithTZ3() {
    run("reasoner.DateTimeTest.testExactIntervalsWithTZ3");
}
#[test]
#[allow(non_snake_case)]
fn reasoner_DateTimeTest_testExactIntervalsWithoutTZ1() {
    run("reasoner.DateTimeTest.testExactIntervalsWithoutTZ1");
}
#[test]
#[allow(non_snake_case)]
fn reasoner_DateTimeTest_testExactIntervalsWithoutTZ2() {
    run("reasoner.DateTimeTest.testExactIntervalsWithoutTZ2");
}
#[test]
#[allow(non_snake_case)]
fn reasoner_DateTimeTest_testParsing() {
    run("reasoner.DateTimeTest.testParsing");
}
#[test]
#[allow(non_snake_case)]
fn reasoner_RDFPlainLiteralTest_testComplement2() {
    run("reasoner.RDFPlainLiteralTest.testComplement2");
}
#[test]
#[allow(non_snake_case)]
fn reasoner_RDFPlainLiteralTest_testComplement3() {
    run("reasoner.RDFPlainLiteralTest.testComplement3");
}
#[test]
#[allow(non_snake_case)]
fn reasoner_RDFPlainLiteralTest_testComplement4() {
    run("reasoner.RDFPlainLiteralTest.testComplement4");
}
#[test]
#[allow(non_snake_case)]
fn reasoner_RDFPlainLiteralTest_testEnumerate() {
    run("reasoner.RDFPlainLiteralTest.testEnumerate");
}
#[test]
#[allow(non_snake_case)]
fn reasoner_RDFPlainLiteralTest_testExplicitSize() {
    run("reasoner.RDFPlainLiteralTest.testExplicitSize");
}
#[test]
#[allow(non_snake_case)]
fn reasoner_RDFPlainLiteralTest_testInvalidStringLiterals() {
    run("reasoner.RDFPlainLiteralTest.testInvalidStringLiterals");
}
#[test]
#[allow(non_snake_case)]
fn reasoner_RDFPlainLiteralTest_testLangRange1() {
    run("reasoner.RDFPlainLiteralTest.testLangRange1");
}
#[test]
#[allow(non_snake_case)]
fn reasoner_RDFPlainLiteralTest_testLangRange2() {
    run("reasoner.RDFPlainLiteralTest.testLangRange2");
}
#[test]
#[allow(non_snake_case)]
fn reasoner_RDFPlainLiteralTest_testPatternAndLength2() {
    run("reasoner.RDFPlainLiteralTest.testPatternAndLength2");
}
#[test]
#[allow(non_snake_case)]
fn reasoner_RDFPlainLiteralTest_testPatternAndLength3() {
    run("reasoner.RDFPlainLiteralTest.testPatternAndLength3");
}
