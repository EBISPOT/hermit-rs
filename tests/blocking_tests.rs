// Tests for the blocking SetFactory label interner.

use hermit_rs::blocking::SetFactory;

#[test]
fn interns_sets_by_content_order_independently() {
    let mut factory: SetFactory<i32> = SetFactory::new();
    let s1 = factory.get_set(&[1, 2, 3]);
    let s2 = factory.get_set(&[3, 2, 1]); // same set, different order
    let s3 = factory.get_set(&[1, 2]);
    // Identity equality for equal sets (the HermiT `==` label comparison).
    assert!(s1 == s2);
    assert!(s1 != s3);
    assert_eq!(s1.len(), 3);
    assert!(s1.contains(&2));
    assert!(!s3.contains(&3));
}

#[test]
fn reference_counting_and_permanence() {
    let mut factory: SetFactory<i32> = SetFactory::new();
    let s = factory.get_set(&[7, 8]);
    factory.add_reference(&s);
    factory.add_reference(&s);
    factory.remove_reference(&s);
    // Still referenced: the same canonical set is returned.
    let s_again = factory.get_set(&[8, 7]);
    assert!(s == s_again);

    // Make permanent, then clear non-permanent: it survives.
    factory.make_permanent(&s);
    factory.clear_nonpermanent();
    let s_perm = factory.get_set(&[7, 8]);
    assert!(s == s_perm);

    // A fresh non-permanent set is dropped by clear_nonpermanent (a new
    // canonical instance is created afterwards).
    let t = factory.get_set(&[9]);
    factory.clear_nonpermanent();
    let t2 = factory.get_set(&[9]);
    assert!(t != t2);
}
