#[derive(Clone, Copy)]
pub struct Fuel {
    pub remaining: u32,
}

impl Default for Fuel {
    fn default() -> Self {
        // The string theory's fuel bounds the number of length-axiom / word-equation
        // split emissions per solve. Each emission mints fresh `str.len(skolem)`
        // terms that enter the shared String↔Arith set; that set growing without
        // bound is the engine's core divergence (the substr / multi-variable word-
        // equation seam), and its per-step cost grows SUPER-LINEARLY (the N-O
        // entailed-equality probing is quadratic in the shared-set size). So fuel is
        // deliberately SMALL: the soundly-decidable core (constant folding,
        // prefix/length contradictions caught lemma-free in `resolve_equation`,
        // bounded word equations, in-range substr) finishes within it, while a
        // divergent instance bails to a SOUND `Unknown` in well under a second rather
        // than spending minutes. (Empirically the QF_S differential corpus's hardest
        // genuinely-divergent seeds need only a few dozen emissions before the shared
        // set explodes; legitimately-decidable instances resolve in far fewer.)
        Fuel { remaining: 40 }
    }
}

impl Fuel {
    /// Returns false when exhausted (caller must then signal `unknown`).
    pub fn spend(&mut self) -> bool {
        if self.remaining == 0 {
            return false;
        }
        self.remaining -= 1;
        true
    }
}
