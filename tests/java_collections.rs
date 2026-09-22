//! Direct ports of the Java dependency-set and tuple-index tests.
use hermit_rs::tableau::{
    dependency_set::*,
    tuple_index::{TupleIndex, TupleIndexRetrieval},
    tuple_table::TupleTable,
};
fn ds(f: &mut DependencySetFactory, points: &[i32]) -> PermanentDependencySet {
    let mut s = f.empty_set();
    for &p in points {
        s = f.add_branching_point(&s.into(), p);
    }
    s
}
fn equal_ds(s: &PermanentDependencySet, points: &[i32]) {
    let actual: Vec<_> = (0..=s.get_maximum_branching_point())
        .filter(|point| s.contains_branching_point(*point))
        .collect();
    let mut expected = points.to_vec();
    expected.sort_unstable();
    assert_eq!(actual, expected);
}
#[test]
fn dependency_set_1() {
    let mut f = DependencySetFactory::new();
    let mut s = f.empty_set();
    equal_ds(&s, &[]);
    assert!(s.is_empty());
    s = f.add_branching_point(&s.into(), 32);
    assert!(!s.is_empty());
    equal_ds(&s, &[32]);
    s = f.add_branching_point(&s.into(), 0);
    equal_ds(&s, &[0, 32]);
    let s2 = ds(&mut f, &[0]);
    assert!(!s.ptr_eq(&s2));
    assert!(s.ptr_eq(&f.add_branching_point(&s2.clone().into(), 32)));
    let rhs = ds(&mut f, &[0, 15, 17]);
    s = f.union_with(&s.into(), &rhs.into());
    equal_ds(&s, &[0, 15, 17, 32]);
    let empty = f.empty_set();
    let union = f.union_with(&s.clone().into(), &empty.into());
    assert!(s.ptr_eq(&union));
    assert!(s.ptr_eq(&f.add_branching_point(&union.into(), 17)));
    assert!(s.ptr_eq(&f.remove_branching_point(&s.clone().into(), 13)));
    for (p, want) in [(17, vec![0, 15, 32]), (15, vec![0, 32]), (32, vec![0])] {
        s = f.remove_branching_point(&s.into(), p);
        equal_ds(&s, &want);
    }
}
#[test]
fn dependency_set_2() {
    let mut f = DependencySetFactory::new();
    let a = ds(&mut f, &[10, 3, 1, 14]);
    equal_ds(&a, &[1, 3, 10, 14]);
    let b = ds(&mut f, &[15, 10, 1, 17]);
    equal_ds(&b, &[1, 10, 15, 17]);
    let c = f.union_with(&a.into(), &b.into());
    equal_ds(&c, &[1, 3, 10, 14, 15, 17]);
}
#[test]
fn dependency_set_3() {
    let mut f = DependencySetFactory::new();
    let mut u = UnionDependencySet::new(3);
    for points in [vec![10, 3, 1], vec![14, 3, 1, 17], vec![14, 3, 2, 18]] {
        let s = ds(&mut f, &points);
        equal_ds(&s, &points);
        // Rust's constructor reserves capacity; constituents are appended.
        u.add_constituent(s.into());
    }
    let s = f.get_permanent(&DependencySet::Union(u));
    equal_ds(&s, &[1, 2, 3, 10, 14, 17, 18]);
}
fn retrieve(index: &TupleIndex<i32>, selection: &[i32], expected: &[i32]) {
    let bindings: Vec<_> = selection.iter().copied().map(Some).collect();
    let indices: Vec<_> = (0..selection.len()).collect();
    let mut r = TupleIndexRetrieval::new(index, &bindings, &indices);
    r.open();
    let mut actual = Vec::new();
    while !r.after_last() {
        actual.push(r.get_current_tuple_index());
        r.next();
    }
    actual.sort();
    let mut expected = expected.to_vec();
    expected.sort();
    assert_eq!(actual, expected);
}
#[test]
fn tuple_index_1() {
    let mut i = TupleIndex::new(vec![0, 1, 2]);
    retrieve(&i, &[], &[]);
    i.add_tuple(&[1, 2, 3], 1);
    retrieve(&i, &[1], &[1]);
    retrieve(&i, &[1, 2], &[1]);
    i.add_tuple(&[1, 2, 4], 2);
    retrieve(&i, &[1], &[1, 2]);
    retrieve(&i, &[1, 2], &[1, 2]);
    i.add_tuple(&[1, 2, 3], 3);
    retrieve(&i, &[1], &[2, 1]);
    retrieve(&i, &[1, 2], &[2, 1]);
    retrieve(&i, &[1, 2, 3], &[1]);
    i.add_tuple(&[3, 2, 4], 4);
    retrieve(&i, &[], &[2, 1, 4]);
    retrieve(&i, &[1], &[2, 1]);
    retrieve(&i, &[1, 2], &[2, 1]);
    retrieve(&i, &[1, 2, 3], &[1]);
    retrieve(&i, &[6], &[]);
    i.remove_tuple(&[1, 2, 4]);
    retrieve(&i, &[], &[1, 4]);
    i.remove_tuple(&[1, 2, 3]);
    retrieve(&i, &[], &[4]);
    i.remove_tuple(&[3, 2, 4]);
    retrieve(&i, &[], &[]);
}
#[test]
fn tuple_index_2() {
    let mut i = TupleIndex::new(vec![0, 1, 2]);
    let tuples: Vec<_> = (0..10000).map(|n| [n % 300, n % 3000, n]).collect();
    for (n, t) in tuples.iter().enumerate() {
        i.add_tuple(t, n as i32);
    }
    retrieve(&i, &[], &(0..10000).collect::<Vec<_>>());
    for (n, t) in tuples.iter().enumerate() {
        assert_eq!(i.remove_tuple(t), n as i32);
    }
    retrieve(&i, &[], &[]);
}
// Rust uses TupleIndex for full-tuple lookup too; keep the original TupleTable
// allocation and duplicate/removal assertions rather than inventing a second index.
fn add(table: &mut TupleTable<i32>, index: &mut TupleIndex<i32>, tuple: &[i32]) -> i32 {
    let tentative = table.get_first_free_tuple_index() as i32;
    let result = index.add_tuple(tuple, tentative);
    if result == tentative {
        table.add_tuple(tuple);
    }
    result
}
#[test]
fn tuple_table_full_index() {
    let mut t = TupleTable::new(2);
    let mut i = TupleIndex::new(vec![0, 1]);
    for (want, pair) in [(0, [1, 2]), (1, [2, 3]), (2, [3, 4]), (0, [1, 2])] {
        assert_eq!(add(&mut t, &mut i, &pair), want);
    }
    for (want, pair) in [(0, [1, 2]), (1, [2, 3]), (2, [3, 4])] {
        assert_eq!(i.get_tuple_index(&pair), want);
    }
    assert_eq!(i.remove_tuple(&[2, 3]), 1);
    for (want, pair) in [(0, [1, 2]), (-1, [2, 3]), (2, [3, 4])] {
        assert_eq!(i.get_tuple_index(&pair), want);
    }
    assert_eq!(add(&mut t, &mut i, &[5, 6]), 3);
    for (want, pair) in [(0, [1, 2]), (-1, [2, 3]), (2, [3, 4]), (3, [5, 6])] {
        assert_eq!(i.get_tuple_index(&pair), want);
    }
    assert_eq!(add(&mut t, &mut i, &[7, 8]), 4);
    for (want, pair) in [
        (0, [1, 2]),
        (-1, [2, 3]),
        (2, [3, 4]),
        (3, [5, 6]),
        (4, [7, 8]),
    ] {
        assert_eq!(i.get_tuple_index(&pair), want);
    }
}
#[test]
fn tuple_table_full_index_lots_of_data() {
    let mut t = TupleTable::new(2);
    let mut i = TupleIndex::new(vec![0, 1]);
    for n in 0..40000 {
        assert_eq!(add(&mut t, &mut i, &[2 * n, 2 * n + 1]), n);
    }
    for n in 0..40000 {
        assert_eq!(i.get_tuple_index(&[2 * n, 2 * n + 1]), n);
    }
    assert_eq!(i.get_tuple_index(&[-1, -2]), -1);
}
