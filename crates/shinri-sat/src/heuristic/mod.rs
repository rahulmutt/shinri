use crate::assignment::Assignment;
use shinri_core::Var;

pub mod evsids;
pub use evsids::Evsids;

pub mod vmtf;
pub use vmtf::Vmtf;

/// The branching heuristic seam. Fixed at construction as the generic `H` of
/// `Solver`, so `next`/`bump` monomorphize with zero dispatch (spec §8.4).
pub trait BranchHeuristic: Default {
    /// A new variable was allocated.
    fn new_var(&mut self, v: Var);
    /// Raise `v`'s priority (called during conflict analysis).
    fn bump(&mut self, v: Var);
    /// Age all priorities one step (called once per conflict).
    fn decay(&mut self);
    /// `v` was un-assigned on backtrack and is a branching candidate again.
    fn on_unassign(&mut self, v: Var);
    /// The highest-priority *unassigned* variable, or `None` if all assigned.
    fn next(&mut self, assign: &Assignment) -> Option<Var>;
}
