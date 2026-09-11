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

/// Spec §4.2 case 1: duplicate arguments. `g(a, a)` is pushed twice onto one
/// use-list; undo must pop both, LIFO. Pre-slice, `UseSplice`'s undo moves the
/// wrong tail block back and strands `g(b, b)` on `a`'s list.
#[test]
fn duplicate_argument_app_survives_backtrack() {
    let mut r = Rig::new();
    let a = r.konst("a");
    let b = r.konst("b");
    let g = r.fun("g", 2);
    let gaa = r.app(g, &[a, a]);
    let gbb = r.app(g, &[b, b]);
    r.add(a);
    r.add(b);
    r.add(gbb);

    r.push();
    assert!(r.merge(a, b).is_none());
    r.add(gaa);
    assert!(r.drain(a).is_none());
    assert!(r.equal(gaa, gbb));
    r.assert_index();

    r.pop(0);
    assert!(!r.equal(gaa, gbb));
    r.assert_index();

    r.push();
    assert!(r.merge(a, b).is_none());
    assert!(r.equal(gaa, gbb), "g(a,a) = g(b,b) must be re-derived");
    r.assert_index();
}

/// Spec §4.2 case 2: nested registration. `f(f(a))` registers `f(a)` first;
/// each gets its own `AppIndexed`, undone outer-first and re-indexed
/// inner-first.
#[test]
fn nested_midsearch_registration_survives_backtrack() {
    let mut r = Rig::new();
    let a = r.konst("a");
    let b = r.konst("b");
    let f = r.fun("f", 1);
    let fa = r.app(f, &[a]);
    let fb = r.app(f, &[b]);
    let ffa = r.app(f, &[fa]);
    let ffb = r.app(f, &[fb]);
    r.add(a);
    r.add(b);
    r.add(ffb);

    r.push();
    assert!(r.merge(a, b).is_none());
    r.add(ffa);
    assert!(r.drain(a).is_none());
    assert!(r.equal(ffa, ffb));
    r.assert_index();

    r.pop(0);
    assert!(!r.equal(ffa, ffb));
    r.assert_index();

    r.push();
    assert!(r.merge(a, b).is_none());
    assert!(r.equal(fa, fb), "f(a) = f(b) must be re-derived");
    assert!(r.equal(ffa, ffb), "f(f(a)) = f(f(b)) must be re-derived");
    r.assert_index();
}

/// Spec §4.2 case 3: the indexed-onto representative loses a later merge at
/// the same level. Undo reverses the splice first, which returns the app to
/// the loser's tail for `AppIndexed`'s pop. Already correct pre-slice (the app
/// is keyed on its own argument); pins the LIFO order the new debug checks
/// rely on.
#[test]
fn app_on_a_later_merge_loser_is_restored_before_its_index_is_undone() {
    let mut r = Rig::new();
    let a = r.konst("a");
    let c = r.konst("c");
    let d = r.konst("d");
    let f = r.fun("f", 1);
    let fa = r.app(f, &[a]);
    let fc = r.app(f, &[c]);
    r.add(a);
    r.add(c);
    r.add(d);
    r.add(fc);
    assert!(r.merge(c, d).is_none()); // level 0: c's class has size 2

    r.push();
    r.add(fa); // indexed onto a
    assert!(r.merge(a, c).is_none()); // a (size 1) loses to c (size 2)
    assert!(r.equal(fa, fc));
    r.assert_index();

    r.pop(0);
    assert!(!r.equal(fa, fc));
    r.assert_index();

    r.push();
    assert!(r.merge(a, c).is_none());
    assert!(r.equal(fa, fc));
    r.assert_index();
}

/// Spec §4.2 case 4: a `LookupOverwrite` on the app's own signature, recorded
/// after its insert, is undone first, so `AppIndexed`'s undo finds its own
/// entry. Already correct pre-slice; pins the `lookup[sig] == app` debug check.
#[test]
fn lookup_overwrite_after_insert_is_undone_before_the_index() {
    let mut r = Rig::new();
    let a = r.konst("a");
    let b = r.konst("b");
    let f = r.fun("f", 1);
    let fa = r.app(f, &[a]);
    let fb = r.app(f, &[b]);
    r.add(a);
    r.add(b);
    r.add(fb);

    r.push();
    r.add(fa); // inserts lookup[(f,[a])] = f(a)
    assert!(r.merge(a, b).is_none()); // f(b) re-signs to (f,[a]): overwrite
    assert!(r.equal(fa, fb));
    r.assert_index();

    r.pop(0);
    assert!(!r.equal(fa, fb));
    r.assert_index();

    r.push();
    assert!(r.merge(a, b).is_none());
    assert!(r.equal(fa, fb));
    r.assert_index();
}

/// Spec §4.2 case 5: pop several levels, push again, and flush at the higher
/// level. The flush records `AppIndexed` at that level, so popping below it
/// re-queues the apps; once indexed at level 0 they stay.
#[test]
fn reindex_at_a_higher_level_is_requeued_by_a_lower_pop() {
    let mut r = Rig::new();
    let a = r.konst("a");
    let b = r.konst("b");
    let c = r.konst("c");
    let f = r.fun("f", 1);
    let fa = r.app(f, &[a]);
    let fb = r.app(f, &[b]);
    r.add(a);
    r.add(b);
    r.add(c);

    r.push(); // level 1
    assert!(r.merge(a, b).is_none());
    r.push(); // level 2
    r.add(fb);
    r.add(fa);
    assert!(r.drain(a).is_none());
    assert!(r.equal(fa, fb));
    r.assert_index();

    r.pop(0);
    assert_eq!(r.g.reindex.len(), 2, "both level-2 apps are queued");
    r.assert_index();

    r.push(); // level 1
    r.push(); // level 2
    r.add(c); // already registered: only flushes
    assert!(r.g.reindex.is_empty());
    assert!(!r.equal(fa, fb));
    r.assert_index();

    r.pop(1);
    assert_eq!(
        r.g.reindex.len(),
        2,
        "indexed at level 2, so popping to 1 re-queues"
    );
    r.assert_index();

    assert!(r.merge(a, b).is_none()); // level 1
    assert!(r.equal(fa, fb));
    r.assert_index();

    r.pop(0);
    assert!(r.merge(a, b).is_none()); // level 0: indexed for good
    assert!(r.equal(fa, fb));
    assert!(r.g.reindex.is_empty());
    r.assert_index();
}

/// Spec §4.2 case 6: `add_term` on an already-registered term whose index is
/// queued. The `seen_terms` guard returns early, but the flush must run first.
#[test]
fn seen_terms_early_return_still_flushes_the_queue() {
    let mut r = Rig::new();
    let a = r.konst("a");
    let b = r.konst("b");
    let f = r.fun("f", 1);
    let fa = r.app(f, &[a]);
    let fb = r.app(f, &[b]);
    r.add(a);
    r.add(b);
    r.add(fa);

    r.push();
    assert!(r.merge(a, b).is_none());
    r.add(fb); // keyed on a, the level-1 representative

    r.pop(0);
    r.add(fb); // registered: the guard returns early, after the flush
    assert!(
        r.g.reindex.is_empty(),
        "the flush must run before the seen_terms early return"
    );
    r.assert_index();

    r.push();
    assert!(r.merge(a, b).is_none());
    assert!(r.equal(fa, fb));
    r.assert_index();
}

/// Spec §4.2 case 7a: a flush that discovers a congruence only enqueues it;
/// the next drain closes it.
#[test]
fn congruence_found_by_a_flush_is_closed_by_the_next_drain() {
    let mut r = Rig::new();
    let a = r.konst("a");
    let b = r.konst("b");
    let f = r.fun("f", 1);
    let fa = r.app(f, &[a]);
    let fb = r.app(f, &[b]);
    r.add(a);
    r.add(b);
    r.add(fa);

    r.push(); // level 1
    assert!(r.merge(a, b).is_none());
    r.push(); // level 2
    r.add(fb);
    assert!(r.drain(a).is_none());
    assert!(r.equal(fa, fb));

    r.pop(1); // a = b still holds; f(a) = f(b) was undone with level 2
    assert!(!r.equal(fa, fb));
    r.assert_index();

    r.add(a); // registered: flushes only
    assert!(
        !r.g.pending.is_empty(),
        "the flush enqueues the f(a)/f(b) collision"
    );
    assert!(!r.equal(fa, fb), "enqueued, not yet merged");
    r.assert_index();

    assert!(r.drain(a).is_none());
    assert!(r.equal(fa, fb));
    r.assert_index();
}

/// Spec §4.2 case 7b: the same enqueue, then a pop below the level where the
/// arguments were equal. The entry is stale; the guard skips it.
#[test]
fn congruence_found_by_a_flush_goes_stale_across_a_pop() {
    let mut r = Rig::new();
    let a = r.konst("a");
    let b = r.konst("b");
    let f = r.fun("f", 1);
    let fa = r.app(f, &[a]);
    let fb = r.app(f, &[b]);
    r.add(a);
    r.add(b);
    r.add(fa);

    r.push(); // level 1
    assert!(r.merge(a, b).is_none());
    r.push(); // level 2
    r.add(fb);
    assert!(r.drain(a).is_none());

    r.pop(1);
    r.add(a); // flush at level 1: enqueues f(a)/f(b)
    assert!(!r.g.pending.is_empty());

    r.pop(0); // a != b now: the entry is stale
    assert!(r.drain(a).is_none());
    assert!(!r.equal(fa, fb), "a stale congruence must not merge");
    r.assert_index();
}
