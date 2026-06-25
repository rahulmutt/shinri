//! FP model reconstruction. Slice 1 reuses the BV bit-packer: an FP value is
//! the W=eb+sb unsigned bit pattern read from the SAT assignment (LSB→MSB).

pub use shinri_bv::model::pack;
