//! serde support, checked against serde_json.
#![cfg(feature = "serde")]
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, HashMap};

#[derive(Serialize, Deserialize, Debug, PartialEq, Clone)]
enum Shape {
    Empty,
    Circle(f64),
    Point(i32, i32),
    Rect { w: u32, h: u32 },
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Clone)]
struct Wrapper(String);

#[derive(Serialize, Deserialize, Debug, PartialEq, Clone)]
struct Record {
    id: u64,
    neg: i64,
    name: String,
    tags: Vec<String>,
    score: Option<f64>,
    missing: Option<u8>,
    flags: (bool, char),
    shapes: Vec<Shape>,
    by_id: BTreeMap<u32, Wrapper>,
    nested: Vec<Vec<i8>>,
    unit: (),
    big: u128,
}

fn sample() -> Record {
    let mut by_id = BTreeMap::new();
    by_id.insert(7, Wrapper("seven \"quoted\"".into()));
    by_id.insert(1, Wrapper("tab\there\n\u{1}\u{e9}\u{1F600}".into()));
    Record {
        id: u64::MAX,
        neg: i64::MIN,
        name: "back\\slash / slash".into(),
        tags: vec!["a".into(), "".into()],
        score: Some(-0.1),
        missing: None,
        flags: (true, '\u{20ac}'),
        shapes: vec![Shape::Empty, Shape::Circle(1e300), Shape::Point(-1, 2), Shape::Rect { w: 3, h: 4 }],
        by_id,
        nested: vec![vec![], vec![-128, 127]],
        unit: (),
        big: u128::MAX,
    }
}

#[test]
fn same_output_as_serde_json() {
    let r = sample();
    assert_eq!(verilith_json::to_string(&r).unwrap(), serde_json::to_string(&r).unwrap());
    assert_eq!(verilith_json::to_vec_pretty(&r).unwrap(), serde_json::to_vec_pretty(&r).unwrap());
    for x in [0.0f64, -0.0, 0.1, 1.0, 1e16, 1.5e-7, 123456.789, f64::MAX, 5e-324, f64::NAN] {
        assert_eq!(verilith_json::to_string(&x).unwrap(), serde_json::to_string(&x).unwrap(), "{x}");
    }
    for x in [0.1f32, 1e30, f32::MAX, 16777216.0] {
        assert_eq!(verilith_json::to_string(&x).unwrap(), serde_json::to_string(&x).unwrap(), "{x}");
    }
    let m: HashMap<bool, i8> = [(true, 1)].into();
    assert_eq!(verilith_json::to_string(&m).unwrap(), serde_json::to_string(&m).unwrap());
}

#[test]
fn round_trip() {
    let r = sample();
    let text = verilith_json::to_vec(&r).unwrap();
    let back: Record = verilith_json::from_slice(&text).unwrap();
    assert_eq!(back, r);
    let pretty = verilith_json::to_vec_pretty(&r).unwrap();
    assert_eq!(verilith_json::from_slice::<Record>(&pretty).unwrap(), r);
}

#[test]
fn reads_what_serde_json_reads() {
    let text = serde_json::to_string(&sample()).unwrap();
    let a: Record = verilith_json::from_str(&text).unwrap();
    let b: Record = serde_json::from_str(&text).unwrap();
    assert_eq!(a, b);
    let v: serde_json::Value = verilith_json::from_str(&text).unwrap();
    assert_eq!(v, serde_json::from_str::<serde_json::Value>(&text).unwrap());
}

#[test]
fn borrows_strings() {
    #[derive(Deserialize)]
    struct B<'a> {
        #[serde(borrow)]
        s: &'a str,
    }
    let text = br#"{"s": "zero copy"}"#;
    let b: B = verilith_json::from_slice(text).unwrap();
    assert_eq!(b.s, "zero copy");
    assert!(text.as_ptr_range().contains(&b.s.as_ptr()));
}

#[test]
fn errors() {
    assert!(matches!(verilith_json::from_str::<u8>("[1"), Err(verilith_json::SerdeError::Parse(_))));
    assert!(verilith_json::from_str::<u8>("300").is_err());
    assert!(verilith_json::from_str::<String>("1").is_err());
    assert!(verilith_json::from_str::<(u8,)>("[1, 2]").is_err());
    assert!(verilith_json::from_str::<Shape>("{}").is_err());
    let e = verilith_json::from_str::<Record>("{}").unwrap_err().to_string();
    assert!(e.contains("missing field"), "{e}");
}

/// Every JSONTestSuite file that serde_json and vjson both accept reads to
/// the same `serde_json::Value`.
#[test]
fn json_test_suite_values() {
    let Ok(dir) = std::env::var("JSON_TEST_SUITE") else { return };
    let mut n = 0;
    for entry in std::fs::read_dir(dir).unwrap() {
        let data = std::fs::read(entry.unwrap().path()).unwrap();
        let (Ok(a), Ok(b)) = (
            verilith_json::from_slice::<serde_json::Value>(&data),
            serde_json::from_slice::<serde_json::Value>(&data),
        ) else {
            continue;
        };
        assert_eq!(a, b);
        assert_eq!(verilith_json::to_vec(&a).unwrap(), serde_json::to_vec(&b).unwrap());
        n += 1;
    }
    assert!(n > 90, "only {n} files compared");
}
