//! Asserted arithmetic disequalities; repaired lemma-free in check (Task 12).
use crate::vars::ArithVar;
use shinri_core::Lit;
use shinri_num::DeltaRational;

#[derive(Default)]
pub struct DiseqStore {
    items: Vec<(ArithVar, DeltaRational, Lit)>,
    marks: Vec<usize>,
}

impl DiseqStore {
    pub fn push(&mut self, v: ArithVar, rhs: DeltaRational, lit: Lit) {
        self.items.push((v, rhs, lit));
    }
    pub fn mark(&mut self) {
        self.marks.push(self.items.len());
    }
    pub fn undo_to(&mut self, level: usize) {
        while self.marks.len() > level {
            let t = self.marks.pop().unwrap();
            self.items.truncate(t);
        }
    }
    pub fn iter(&self) -> impl Iterator<Item = &(ArithVar, DeltaRational, Lit)> {
        self.items.iter()
    }
}
