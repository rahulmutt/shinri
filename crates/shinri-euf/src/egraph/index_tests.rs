//! Slice 49: the congruence index across backtracking (spec §4.2).

use super::test_rig::Rig;

/// Spec §4.2 case 8 / §1.3. An app registered above level 0, while its
/// argument's class is the product of a merge at that level, must keep its
/// congruence after the level is popped and the classes merge again.
///
/// Pre-slice, `add_term` filed `f(b)` under `a`'s use-list (the level-1
/// representative) with no undo record; after the pop `b` is its own
/// representative again but `f(b)` is still on `a`'s list, so the re-merge
/// (same winner, `a`) walks `b`'s empty list and never re-detects
/// `f(a) = f(b)`.
#[test]
fn midsearch_registration_keeps_congruence_across_backtrack() {
    let mut r = Rig::new();
    let a = r.konst("a");
    let b = r.konst("b");
    let f = r.fun("f", 1);
    let fa = r.app(f, &[a]);
    let fb = r.app(f, &[b]);
    r.add(a);
    r.add(b);

    // Level 1: a = b, then register f(a) and f(b) over the merged class.
    r.push();
    assert!(r.merge(a, b).is_none());
    r.add(fa);
    r.add(fb);
    assert!(
        r.merge(a, a).is_none(),
        "a no-op merge drains the registration-time collision"
    );
    assert!(r.equal(fa, fb), "level 1: congruence must hold");
    r.assert_index();

    // Backtrack: a = b and f(a) = f(b) are both undone.
    r.pop(0);
    assert!(!r.equal(fa, fb));
    r.assert_index();

    // Re-derive a = b: the congruence must be re-detected.
    r.push();
    assert!(r.merge(a, b).is_none());
    assert!(
        r.equal(fa, fb),
        "congruence lost after mid-search add_term + backtrack"
    );
    r.assert_index();
}
