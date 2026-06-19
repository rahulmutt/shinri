use crate::config::RestartKind;

/// The Luby sequence value at 1-based index `i` (Luby–Sinclair–Zuckerman).
pub fn luby(i: u64) -> u64 {
    // Find the subsequence: for the largest k with 2^k - 1 <= i.
    let mut size = 1u64; // 2^k - 1
    let mut seq = 0u64; // k
    while size < i {
        size = 2 * size + 1;
        seq += 1;
    }
    while size != i {
        size = (size - 1) / 2;
        seq -= 1;
        if i > size {
            // move into the right half (recurse on i - size offset)
            return luby(i - size);
        }
    }
    1u64 << seq
}

/// Restart scheduler. Luby is a fixed multiplicative schedule; Glucose-EMA
/// restarts when the fast LBD average exceeds the slow average by a margin.
pub struct RestartPolicy {
    kind: RestartKind,
    base: u64,
    conflicts_since: u64,
    luby_index: u64,
    limit: u64,
    ema_fast: f64,
    ema_slow: f64,
    seen: u64,
}

impl RestartPolicy {
    pub fn new(kind: RestartKind, base: u64) -> RestartPolicy {
        RestartPolicy {
            kind,
            base,
            conflicts_since: 0,
            luby_index: 1,
            limit: base * luby(1),
            ema_fast: 0.0,
            ema_slow: 0.0,
            seen: 0,
        }
    }

    pub fn on_conflict(&mut self, lbd: u32) {
        self.conflicts_since += 1;
        self.seen += 1;
        let x = lbd as f64;
        // Glucose EMA coefficients: fast 1/32, slow 1/2^14.
        self.ema_fast += (x - self.ema_fast) / 32.0;
        self.ema_slow += (x - self.ema_slow) / 16384.0;
    }

    pub fn should_restart(&self) -> bool {
        match self.kind {
            RestartKind::Luby => self.conflicts_since >= self.limit,
            RestartKind::EmaGlucose => {
                // Warm up before trusting the averages.
                self.seen >= 50 && self.ema_fast > 1.25 * self.ema_slow
            }
        }
    }

    pub fn on_restart(&mut self) {
        self.conflicts_since = 0;
        self.luby_index += 1;
        self.limit = self.base * luby(self.luby_index);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn luby_sequence_prefix() {
        // Classic Luby: 1,1,2,1,1,2,4,1,1,2,1,1,2,4,8,...
        let got: Vec<u64> = (1..=15).map(luby).collect();
        assert_eq!(got, vec![1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8]);
    }

    #[test]
    fn luby_policy_fires_after_base_times_unit() {
        let mut p = RestartPolicy::new(RestartKind::Luby, 4);
        // First limit = base * luby(1) = 4 conflicts.
        for _ in 0..3 {
            p.on_conflict(3);
            assert!(!p.should_restart());
        }
        p.on_conflict(3);
        assert!(p.should_restart());
        p.on_restart();
        assert!(!p.should_restart());
    }
}
