#[derive(Clone, Copy)]
pub struct Fuel {
    pub remaining: u32,
}

impl Default for Fuel {
    fn default() -> Self {
        Fuel { remaining: 2000 }
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
