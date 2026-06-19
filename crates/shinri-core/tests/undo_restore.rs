use proptest::prelude::*;
use shinri_core::UndoLog;

// Model a backtrackable Vec<u8> whose mutations are recorded as undo entries.
// Property: snapshot -> mutate -> pop_to(snapshot level) -> bit-identical state.
proptest! {
    #[test]
    fn snapshot_mutate_pop_restores_state(
        initial in proptest::collection::vec(any::<u8>(), 0..16),
        ops in proptest::collection::vec(0u8..=2, 0..64),
    ) {
        // Undo entry: restore index `idx` to old value `old`, or pop the last push.
        enum U { Set { idx: usize, old: u8 }, Pop }

        let mut state = initial.clone();
        let mut log: UndoLog<U> = UndoLog::default();

        log.push_level();
        let snapshot = state.clone();

        // counter to vary mutations deterministically without rand
        let mut k: u8 = 0;
        for op in ops {
            k = k.wrapping_add(1);
            match op {
                0 => {
                    // push
                    state.push(k);
                    log.record(U::Pop);
                }
                1 if !state.is_empty() => {
                    // set element 0
                    let idx = 0usize;
                    log.record(U::Set { idx, old: state[idx] });
                    state[idx] = k;
                }
                _ => { /* no-op to keep lengths varied */ }
            }
        }

        log.pop_to(0, |u| match u {
            U::Set { idx, old } => state[idx] = old,
            U::Pop => { state.pop(); }
        });

        prop_assert_eq!(state, snapshot);
    }
}
