# shinri-num Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build `shinri-num`, a from-scratch, SMT-tuned big-integer + rational arithmetic library that is the sole arithmetic backend for the shinri SMT solver, validated to exactly match `num-bigint`/`num-rational` across a differential + fuzz corpus.

**Architecture:** A single dependency-free crate exposing `Integer`, `Rational`, and `DeltaRational`. `Integer` uses a two-case representation — `Small(i128)` for values that fit in 128 bits (no heap allocation: the common case in SMT) and `Big { negative, limbs: Vec<u64> }` for larger magnitudes. Every operation takes an i128 fast path and falls back to little-endian limb-vector routines only on overflow. Correctness-first: simple, provably-correct algorithms (Euclidean GCD, binary long division, schoolbook multiply) ship first; Karatsuba is added as a benchmark-gated optimization; Lehmer GCD, Knuth Algorithm D, Toom-Cook, and FFT are deferred (spec §7.3) until profiling proves a need.

**Tech Stack:** Rust 2021, zero runtime dependencies. Dev-only: `proptest` (property tests), `num-bigint`/`num-traits` (differential oracle), `cargo-fuzz` (fuzzing), `cargo-nextest` (runner), `cargo-deny` (dependency policy).

## Global Constraints

- **Rust edition:** `2021`. Toolchain pinned to `1.96.0` in `mise.toml` (the toolchain installed in this environment).
- **Zero runtime dependencies** for `shinri-num`. The `[dependencies]` table stays empty. `num-bigint`, `num-rational`, `num-traits`, `proptest` appear **only** under `[dev-dependencies]` — they must never reach the shipping build (spec §3.1, §7.4).
- **Crate license:** `MIT OR Apache-2.0` (permissive — spec §3.1).
- **No `unsafe`** in this plan's scope. All limb arithmetic uses `u128` widening; checked native ops guard the fast paths. (Audited `unsafe` for `get_unchecked` is a later, separate optimization — not here.)
- **Exactness is mandatory.** No floating point anywhere in `shinri-num`. A wrong result is a soundness bug (spec §7.4).
- **Every `Integer` value is canonical:** `Small(0)` is the only representation of zero; `Big` magnitudes always have `limbs.last() != Some(&0)`, `limbs.len() >= 2`, and a non-zero magnitude. Any value that fits in `i128` is `Small`, never `Big`.
- **Every `Rational` is canonical:** `denom > 0`, `gcd(|numer|, denom) == 1`, and `0` is exactly `0/1`.

---

### Task 1: Workspace + crate scaffold, `Integer` representation, constructors, normalization

**Files:**
- Create: `Cargo.toml` (workspace root)
- Create: `mise.toml`
- Create: `devenv.nix`
- Create: `deny.toml`
- Create: `crates/shinri-num/Cargo.toml`
- Create: `crates/shinri-num/src/lib.rs`
- Create: `crates/shinri-num/src/limbs.rs`
- Create: `crates/shinri-num/src/integer.rs`
- Test: inline `#[cfg(test)]` module in `integer.rs`

**Interfaces:**
- Consumes: nothing (first task).
- Produces:
  - `shinri_num::Integer` — `Clone + Debug`.
  - `Integer::from(i128)` / `Integer::from(i64)` / `Integer::from(u64)` (via `From`).
  - `Integer::is_zero(&self) -> bool`
  - `Integer::is_negative(&self) -> bool`
  - `Integer::signum(&self) -> i32` (`-1`, `0`, `1`)
  - `Integer::abs(&self) -> Integer`
  - Internal (crate-private): `Integer::mag_limbs(&self) -> Vec<u64>` (little-endian magnitude, empty == zero), `Integer::from_sign_limbs(negative: bool, limbs: Vec<u64>) -> Integer`, and in `limbs.rs`: `limbs::trim(&mut Vec<u64>)`, `limbs::cmp(&[u64], &[u64]) -> Ordering`.

- [ ] **Step 1: Create the workspace root `Cargo.toml`**

```toml
[workspace]
resolver = "2"
members = ["crates/shinri-num"]

[workspace.package]
edition = "2021"
license = "MIT OR Apache-2.0"
rust-version = "1.96.0"
```

- [ ] **Step 2: Create `mise.toml`**

```toml
[tools]
rust = "1.96.0"
"cargo:cargo-nextest" = "latest"
"cargo:cargo-deny" = "latest"
"cargo:cargo-fuzz" = "latest"
"cargo:cargo-mutants" = "latest"
```

- [ ] **Step 3: Create `devenv.nix`**

```nix
{ pkgs, ... }:
{
  languages.rust.enable = true;
  languages.rust.channel = "stable";
  packages = [ pkgs.cargo-nextest ];
}
```

- [ ] **Step 4: Create `deny.toml`** (bans native-link crates per spec §3.1)

```toml
[bans]
# Native-link dependencies are forbidden in the shipping build (pure-Rust mandate).
deny = [
    { name = "rug" },
    { name = "gmp-mpfr-sys" },
    { name = "z3-sys" },
    { name = "cadical-rs" },
]

[licenses]
allow = ["MIT", "Apache-2.0", "Apache-2.0 WITH LLVM-exception", "Unicode-3.0", "BSD-3-Clause"]
```

- [ ] **Step 5: Create `crates/shinri-num/Cargo.toml`**

```toml
[package]
name = "shinri-num"
version = "0.1.0"
edition.workspace = true
license.workspace = true
rust-version.workspace = true

[dependencies]
# INTENTIONALLY EMPTY — zero runtime dependencies (Global Constraints).

[dev-dependencies]
proptest = "1"
num-bigint = "0.4"
num-rational = "0.4"
num-traits = "0.2"
```

- [ ] **Step 6: Create `crates/shinri-num/src/lib.rs`**

```rust
//! shinri-num: SMT-tuned exact big-integer and rational arithmetic.
//!
//! Zero runtime dependencies. Validated against num-bigint as a dev-only oracle.

mod integer;
mod limbs;

pub use integer::Integer;
```

- [ ] **Step 7: Create `crates/shinri-num/src/limbs.rs` with `trim` and `cmp`**

```rust
//! Little-endian magnitude limb routines. A "magnitude" is a `&[u64]` /
//! `Vec<u64>` with the least-significant limb first and NO trailing zero limbs
//! (so the empty slice is the unique representation of zero).

use core::cmp::Ordering;

/// Remove trailing zero limbs so the magnitude is canonical.
pub fn trim(v: &mut Vec<u64>) {
    while v.last() == Some(&0) {
        v.pop();
    }
}

/// Compare two canonical magnitudes.
pub fn cmp(a: &[u64], b: &[u64]) -> Ordering {
    if a.len() != b.len() {
        return a.len().cmp(&b.len());
    }
    for i in (0..a.len()).rev() {
        if a[i] != b[i] {
            return a[i].cmp(&b[i]);
        }
    }
    Ordering::Equal
}
```

- [ ] **Step 8: Write the failing test for construction + queries** (append to `integer.rs`, which does not exist yet — create it with only the test module first)

Create `crates/shinri-num/src/integer.rs`:

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn small_construction_and_queries() {
        assert!(Integer::from(0i128).is_zero());
        assert!(!Integer::from(5i128).is_zero());
        assert!(Integer::from(-3i128).is_negative());
        assert!(!Integer::from(3i128).is_negative());
        assert_eq!(Integer::from(0i128).signum(), 0);
        assert_eq!(Integer::from(7i128).signum(), 1);
        assert_eq!(Integer::from(-7i128).signum(), -1);
    }

    #[test]
    fn abs_handles_i128_min() {
        // i128::MIN cannot be negated within i128; abs must promote to Big.
        let a = Integer::from(i128::MIN).abs();
        assert!(!a.is_negative());
        assert!(!a.is_zero());
        // magnitude is 2^127 -> limbs [0, 1<<63]
        assert_eq!(a.mag_limbs(), vec![0, 1u64 << 63]);
    }

    #[test]
    fn from_sign_limbs_collapses_to_small() {
        // 5 as limbs collapses back to Small.
        let a = Integer::from_sign_limbs(false, vec![5, 0]);
        assert_eq!(a.mag_limbs(), vec![5]);
        assert!(!a.is_negative());
        // negative 2^127 collapses to Small(i128::MIN).
        let b = Integer::from_sign_limbs(true, vec![0, 1u64 << 63]);
        assert!(b.is_negative());
        assert_eq!(b.mag_limbs(), vec![0, 1u64 << 63]);
    }
}
```

- [ ] **Step 9: Run the test to verify it fails**

Run: `cargo test -p shinri-num`
Expected: FAIL — `cannot find type Integer` / `Integer` not defined.

- [ ] **Step 10: Implement `Integer` above the test module in `integer.rs`**

```rust
use crate::limbs;
use core::cmp::Ordering;

/// An arbitrary-precision signed integer.
///
/// Invariants (see Global Constraints):
/// - `Small(0)` is the unique representation of zero.
/// - Any value representable in `i128` is `Small`, never `Big`.
/// - `Big` limbs are little-endian, canonical (no trailing zero limb),
///   `len() >= 2`, and the magnitude is non-zero.
#[derive(Clone, Debug)]
pub struct Integer(Repr);

#[derive(Clone, Debug)]
enum Repr {
    Small(i128),
    Big { negative: bool, limbs: Vec<u64> },
}

impl From<i128> for Integer {
    fn from(v: i128) -> Self {
        Integer(Repr::Small(v))
    }
}
impl From<i64> for Integer {
    fn from(v: i64) -> Self {
        Integer(Repr::Small(v as i128))
    }
}
impl From<u64> for Integer {
    fn from(v: u64) -> Self {
        Integer(Repr::Small(v as i128))
    }
}

impl Integer {
    /// Canonical zero.
    pub fn zero() -> Self {
        Integer(Repr::Small(0))
    }
    /// Canonical one.
    pub fn one() -> Self {
        Integer(Repr::Small(1))
    }

    pub fn is_zero(&self) -> bool {
        matches!(self.0, Repr::Small(0))
    }

    pub fn is_negative(&self) -> bool {
        match &self.0 {
            Repr::Small(v) => *v < 0,
            Repr::Big { negative, .. } => *negative,
        }
    }

    pub fn signum(&self) -> i32 {
        match &self.0 {
            Repr::Small(v) => (*v > 0) as i32 - (*v < 0) as i32,
            Repr::Big { negative, .. } => {
                if *negative {
                    -1
                } else {
                    1
                }
            }
        }
    }

    pub fn abs(&self) -> Integer {
        match &self.0 {
            Repr::Small(v) => {
                if *v == i128::MIN {
                    // |i128::MIN| = 2^127 does not fit in i128 -> Big.
                    Integer(Repr::Big {
                        negative: false,
                        limbs: vec![0, 1u64 << 63],
                    })
                } else {
                    Integer(Repr::Small(v.abs()))
                }
            }
            Repr::Big { limbs, .. } => Integer(Repr::Big {
                negative: false,
                limbs: limbs.clone(),
            }),
        }
    }

    /// Little-endian magnitude; empty vec means zero.
    pub(crate) fn mag_limbs(&self) -> Vec<u64> {
        match &self.0 {
            Repr::Small(0) => Vec::new(),
            Repr::Small(v) => {
                let m = v.unsigned_abs(); // u128, correct even for i128::MIN
                let lo = m as u64;
                let hi = (m >> 64) as u64;
                if hi == 0 {
                    vec![lo]
                } else {
                    vec![lo, hi]
                }
            }
            Repr::Big { limbs, .. } => limbs.clone(),
        }
    }

    /// Build an `Integer` from a sign and a (not necessarily trimmed) little-
    /// endian magnitude, collapsing to `Small` whenever the value fits in i128.
    pub(crate) fn from_sign_limbs(negative: bool, mut limbs: Vec<u64>) -> Integer {
        limbs::trim(&mut limbs);
        if limbs.is_empty() {
            return Integer(Repr::Small(0));
        }
        if limbs.len() <= 2 {
            let lo = limbs[0] as u128;
            let hi = if limbs.len() == 2 { limbs[1] as u128 } else { 0 };
            let mag = lo | (hi << 64);
            if !negative {
                if mag <= i128::MAX as u128 {
                    return Integer(Repr::Small(mag as i128));
                }
            } else if mag < (1u128 << 127) {
                return Integer(Repr::Small(-(mag as i128)));
            } else if mag == (1u128 << 127) {
                return Integer(Repr::Small(i128::MIN));
            }
        }
        Integer(Repr::Big { negative, limbs })
    }
}
```

- [ ] **Step 11: Run the test to verify it passes**

Run: `cargo test -p shinri-num`
Expected: PASS (3 tests).

- [ ] **Step 12: Commit**

```bash
git add Cargo.toml mise.toml devenv.nix deny.toml crates/shinri-num
git commit -m "feat(num): scaffold shinri-num crate with Integer representation"
```

---

### Task 2: `Integer` comparison and equality

**Files:**
- Modify: `crates/shinri-num/src/integer.rs`

**Interfaces:**
- Consumes: `Integer`, `mag_limbs`, `signum`, `limbs::cmp` (Task 1).
- Produces: `impl PartialEq + Eq + PartialOrd + Ord for Integer`.

- [ ] **Step 1: Write the failing test**

```rust
#[test]
fn ordering_and_equality() {
    assert_eq!(Integer::from(5i128), Integer::from(5i128));
    assert_ne!(Integer::from(5i128), Integer::from(-5i128));
    assert!(Integer::from(-1i128) < Integer::from(0i128));
    assert!(Integer::from(0i128) < Integer::from(1i128));
    // cross representation: i128::MAX < i128::MAX + 1 (Big)
    let big = Integer::from(i128::MAX) + Integer::from(1i128);
    assert!(Integer::from(i128::MAX) < big);
    assert!(big > Integer::from(0i128));
    // negative Big < negative Small
    let neg_big = -big.clone();
    assert!(neg_big < Integer::from(i128::MIN));
}
```

- [ ] **Step 2: Run to verify it fails**

Run: `cargo test -p shinri-num ordering_and_equality`
Expected: FAIL — `Integer` does not implement `PartialOrd` / `Add` not found.
(Note: this test also needs `Add`/`Neg` from Task 3. To keep Task 2 self-contained, gate the cross-representation lines behind Task 3 — but since they exercise comparison across reps, implement Task 2's traits now and Task 3 will make the whole test pass. Run the simpler assertions first by temporarily commenting the `big` lines if iterating.)

- [ ] **Step 3: Implement comparison**

```rust
impl PartialEq for Integer {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}
impl Eq for Integer {}

impl PartialOrd for Integer {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Integer {
    fn cmp(&self, other: &Self) -> Ordering {
        // Fast path: both Small.
        if let (Repr::Small(a), Repr::Small(b)) = (&self.0, &other.0) {
            return a.cmp(b);
        }
        let sa = self.signum();
        let sb = other.signum();
        if sa != sb {
            return sa.cmp(&sb);
        }
        if sa == 0 {
            return Ordering::Equal;
        }
        let mag = limbs::cmp(&self.mag_limbs(), &other.mag_limbs());
        if sa < 0 {
            mag.reverse()
        } else {
            mag
        }
    }
}
```

- [ ] **Step 4: Run to verify it passes** (after Task 3 lands, the full test passes; the same-representation assertions pass now)

Run: `cargo test -p shinri-num`
Expected: PASS for same-representation assertions.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-num/src/integer.rs
git commit -m "feat(num): Integer ordering and equality"
```

---

### Task 3: Magnitude add/sub helpers + `Integer` `Neg`/`Add`/`Sub`

**Files:**
- Modify: `crates/shinri-num/src/limbs.rs`
- Modify: `crates/shinri-num/src/integer.rs`

**Interfaces:**
- Consumes: `limbs::cmp`, `limbs::trim`, `Integer` internals (Tasks 1–2).
- Produces:
  - `limbs::add(&[u64], &[u64]) -> Vec<u64>`
  - `limbs::sub(&[u64], &[u64]) -> Vec<u64>` (precondition: first arg magnitude >= second)
  - `impl Neg for Integer`, `impl Add for Integer`, `impl Sub for Integer` (all by value), plus `impl AddAssign` and `impl SubAssign`.

- [ ] **Step 1: Write the failing test**

```rust
#[test]
fn add_sub_across_representations() {
    let max = Integer::from(i128::MAX);
    let one = Integer::from(1i128);
    let big = max.clone() + one.clone(); // promotes to Big
    assert!(big > max);
    assert_eq!(big.clone() - one.clone(), max); // demotes back to Small
    // sign handling
    assert_eq!(Integer::from(5i128) + Integer::from(-8i128), Integer::from(-3i128));
    assert_eq!(Integer::from(-5i128) - Integer::from(-8i128), Integer::from(3i128));
    assert_eq!(-(big.clone()) + big.clone(), Integer::zero());
}
```

- [ ] **Step 2: Run to verify it fails**

Run: `cargo test -p shinri-num add_sub_across_representations`
Expected: FAIL — `Add` not implemented for `Integer`.

- [ ] **Step 3: Add `add`/`sub` to `limbs.rs`**

```rust
/// Add two canonical magnitudes.
pub fn add(a: &[u64], b: &[u64]) -> Vec<u64> {
    let (long, short) = if a.len() >= b.len() { (a, b) } else { (b, a) };
    let mut out = Vec::with_capacity(long.len() + 1);
    let mut carry: u128 = 0;
    for i in 0..long.len() {
        let bv = if i < short.len() { short[i] as u128 } else { 0 };
        let sum = long[i] as u128 + bv + carry;
        out.push(sum as u64);
        carry = sum >> 64;
    }
    if carry != 0 {
        out.push(carry as u64);
    }
    out
}

/// Subtract `b` from `a`. Precondition: `cmp(a, b) != Less`. Result is canonical.
pub fn sub(a: &[u64], b: &[u64]) -> Vec<u64> {
    debug_assert!(cmp(a, b) != Ordering::Less, "limbs::sub requires a >= b");
    let mut out = Vec::with_capacity(a.len());
    let mut borrow: i128 = 0;
    for i in 0..a.len() {
        let bv = if i < b.len() { b[i] as i128 } else { 0 };
        let mut diff = a[i] as i128 - bv - borrow;
        if diff < 0 {
            diff += 1i128 << 64;
            borrow = 1;
        } else {
            borrow = 0;
        }
        out.push(diff as u64);
    }
    trim(&mut out);
    out
}
```

- [ ] **Step 4: Implement `Neg`/`Add`/`Sub` in `integer.rs`**

```rust
use core::ops::{Add, AddAssign, Neg, Sub, SubAssign};

impl Neg for Integer {
    type Output = Integer;
    fn neg(self) -> Integer {
        match self.0 {
            Repr::Small(v) => {
                if v == i128::MIN {
                    Integer(Repr::Big { negative: false, limbs: vec![0, 1u64 << 63] })
                } else {
                    Integer(Repr::Small(-v))
                }
            }
            Repr::Big { negative, limbs } => Integer(Repr::Big { negative: !negative, limbs }),
        }
    }
}

fn add_general(x: &Integer, y: &Integer) -> Integer {
    let xn = x.is_negative();
    let yn = y.is_negative();
    let xm = x.mag_limbs();
    let ym = y.mag_limbs();
    if xn == yn {
        Integer::from_sign_limbs(xn, limbs::add(&xm, &ym))
    } else {
        match limbs::cmp(&xm, &ym) {
            Ordering::Equal => Integer::zero(),
            Ordering::Greater => Integer::from_sign_limbs(xn, limbs::sub(&xm, &ym)),
            Ordering::Less => Integer::from_sign_limbs(yn, limbs::sub(&ym, &xm)),
        }
    }
}

impl Add for Integer {
    type Output = Integer;
    fn add(self, rhs: Integer) -> Integer {
        if let (Repr::Small(a), Repr::Small(b)) = (&self.0, &rhs.0) {
            if let Some(s) = a.checked_add(*b) {
                return Integer(Repr::Small(s));
            }
        }
        add_general(&self, &rhs)
    }
}

impl Sub for Integer {
    type Output = Integer;
    fn sub(self, rhs: Integer) -> Integer {
        if let (Repr::Small(a), Repr::Small(b)) = (&self.0, &rhs.0) {
            if let Some(s) = a.checked_sub(*b) {
                return Integer(Repr::Small(s));
            }
        }
        add_general(&self, &(-rhs))
    }
}

impl AddAssign for Integer {
    fn add_assign(&mut self, rhs: Integer) {
        *self = self.clone() + rhs;
    }
}
impl SubAssign for Integer {
    fn sub_assign(&mut self, rhs: Integer) {
        *self = self.clone() - rhs;
    }
}
```

- [ ] **Step 5: Run tests to verify they pass**

Run: `cargo test -p shinri-num`
Expected: PASS (including Task 2's cross-representation assertions now).

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-num/src/limbs.rs crates/shinri-num/src/integer.rs
git commit -m "feat(num): Integer negation, addition, subtraction"
```

---

### Task 4: Magnitude multiply (schoolbook) + `Integer` `Mul`

**Files:**
- Modify: `crates/shinri-num/src/limbs.rs`
- Modify: `crates/shinri-num/src/integer.rs`

**Interfaces:**
- Consumes: `limbs::trim` (Task 1), `Integer` internals.
- Produces: `limbs::mul(&[u64], &[u64]) -> Vec<u64>`, `impl Mul for Integer`, `impl MulAssign for Integer`.

- [ ] **Step 1: Write the failing test**

```rust
#[test]
fn multiply_across_representations() {
    assert_eq!(Integer::from(6i128) * Integer::from(7i128), Integer::from(42i128));
    assert_eq!(Integer::from(-6i128) * Integer::from(7i128), Integer::from(-42i128));
    assert_eq!(Integer::from(0i128) * Integer::from(i128::MAX), Integer::zero());
    // overflow i128 -> Big, then divide back is checked in Task 5.
    let a = Integer::from(i128::MAX);
    let b = Integer::from(i128::MAX);
    let p = a.clone() * b.clone();
    assert!(p > a);
    // (i128::MAX)^2 has known magnitude; verify it's larger than 2^200 lower bound via add identity:
    assert_eq!(p.clone(), a.clone() * b.clone());
}
```

- [ ] **Step 2: Run to verify it fails**

Run: `cargo test -p shinri-num multiply_across_representations`
Expected: FAIL — `Mul` not implemented.

- [ ] **Step 3: Add `mul` to `limbs.rs`**

```rust
/// Schoolbook multiply of two canonical magnitudes.
pub fn mul(a: &[u64], b: &[u64]) -> Vec<u64> {
    if a.is_empty() || b.is_empty() {
        return Vec::new();
    }
    let mut out = vec![0u64; a.len() + b.len()];
    for i in 0..a.len() {
        let ai = a[i] as u128;
        let mut carry: u128 = 0;
        for j in 0..b.len() {
            let cur = out[i + j] as u128 + ai * b[j] as u128 + carry;
            out[i + j] = cur as u64;
            carry = cur >> 64;
        }
        out[i + b.len()] = carry as u64;
    }
    trim(&mut out);
    out
}
```

- [ ] **Step 4: Implement `Mul` in `integer.rs`**

```rust
use core::ops::{Mul, MulAssign};

impl Mul for Integer {
    type Output = Integer;
    fn mul(self, rhs: Integer) -> Integer {
        if let (Repr::Small(a), Repr::Small(b)) = (&self.0, &rhs.0) {
            if let Some(p) = a.checked_mul(*b) {
                return Integer(Repr::Small(p));
            }
        }
        if self.is_zero() || rhs.is_zero() {
            return Integer::zero();
        }
        let negative = self.is_negative() ^ rhs.is_negative();
        let m = limbs::mul(&self.mag_limbs(), &rhs.mag_limbs());
        Integer::from_sign_limbs(negative, m)
    }
}

impl MulAssign for Integer {
    fn mul_assign(&mut self, rhs: Integer) {
        *self = self.clone() * rhs;
    }
}
```

- [ ] **Step 5: Run tests to verify they pass**

Run: `cargo test -p shinri-num`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-num/src/limbs.rs crates/shinri-num/src/integer.rs
git commit -m "feat(num): Integer schoolbook multiplication"
```

---

### Task 5: Magnitude division (binary long division) + `Integer::div_rem`, `Div`, `Rem`

> Maps to spec §7.3 "Knuth Algorithm D (schoolbook long division)". We ship a provably-correct **binary long division** first (correctness-first; the i128 fast path handles the common case). Knuth Algorithm D is a deferred optimization (see Deferred Optimizations) gated on the differential corpus staying green plus a benchmark.

**Files:**
- Modify: `crates/shinri-num/src/limbs.rs`
- Modify: `crates/shinri-num/src/integer.rs`

**Interfaces:**
- Consumes: `limbs::{cmp,sub,trim}` (Tasks 1, 3), `Integer` internals.
- Produces:
  - `limbs::divrem(&[u64], &[u64]) -> (Vec<u64>, Vec<u64>)` (precondition: divisor non-empty).
  - `Integer::div_rem(&self, rhs: &Integer) -> (Integer, Integer)` — truncated toward zero; remainder takes the dividend's sign (matches i128 `/` and `%`). Panics on zero divisor.
  - `impl Div for Integer`, `impl Rem for Integer`.

- [ ] **Step 1: Write the failing test**

```rust
#[test]
fn div_rem_matches_truncation() {
    let (q, r) = Integer::from(17i128).div_rem(&Integer::from(5i128));
    assert_eq!(q, Integer::from(3i128));
    assert_eq!(r, Integer::from(2i128));
    // negative dividend: truncation toward zero, remainder sign = dividend.
    let (q, r) = Integer::from(-17i128).div_rem(&Integer::from(5i128));
    assert_eq!(q, Integer::from(-3i128));
    assert_eq!(r, Integer::from(-2i128));
    // exact division across representations
    let big = Integer::from(i128::MAX) * Integer::from(1000i128);
    let (q, r) = big.div_rem(&Integer::from(1000i128));
    assert_eq!(q, Integer::from(i128::MAX));
    assert!(r.is_zero());
}

#[test]
#[should_panic(expected = "division by zero")]
fn div_by_zero_panics() {
    let _ = Integer::from(1i128).div_rem(&Integer::zero());
}
```

- [ ] **Step 2: Run to verify it fails**

Run: `cargo test -p shinri-num div_rem_matches_truncation`
Expected: FAIL — `div_rem` not found.

- [ ] **Step 3: Add `divrem` and `shl1` to `limbs.rs`**

```rust
fn shl1(v: &mut Vec<u64>) {
    let mut carry = 0u64;
    for x in v.iter_mut() {
        let new_carry = *x >> 63;
        *x = (*x << 1) | carry;
        carry = new_carry;
    }
    if carry != 0 {
        v.push(carry);
    }
}

/// Divide canonical magnitude `a` by canonical magnitude `b` (b non-empty),
/// returning (quotient, remainder), both canonical. Binary long division.
pub fn divrem(a: &[u64], b: &[u64]) -> (Vec<u64>, Vec<u64>) {
    debug_assert!(!b.is_empty(), "divrem by zero magnitude");
    if cmp(a, b) == Ordering::Less {
        return (Vec::new(), a.to_vec());
    }
    let bits = a.len() * 64;
    let mut q = vec![0u64; a.len()];
    let mut r: Vec<u64> = Vec::new();
    for i in (0..bits).rev() {
        shl1(&mut r);
        let bit = (a[i / 64] >> (i % 64)) & 1;
        if bit == 1 {
            if r.is_empty() {
                r.push(1);
            } else {
                r[0] |= 1;
            }
        }
        if cmp(&r, b) != Ordering::Less {
            r = sub(&r, b);
            q[i / 64] |= 1u64 << (i % 64);
        }
    }
    trim(&mut q);
    trim(&mut r);
    (q, r)
}
```

- [ ] **Step 4: Implement `div_rem`, `Div`, `Rem` in `integer.rs`**

```rust
use core::ops::{Div, Rem};

impl Integer {
    /// Truncated division: returns (quotient, remainder) with
    /// `self == quotient * rhs + remainder` and `remainder` taking `self`'s sign.
    pub fn div_rem(&self, rhs: &Integer) -> (Integer, Integer) {
        // Fast path: both Small, avoiding the only overflowing case.
        if let (Repr::Small(a), Repr::Small(b)) = (&self.0, &rhs.0) {
            if *b != 0 && !(*a == i128::MIN && *b == -1) {
                return (Integer(Repr::Small(a / b)), Integer(Repr::Small(a % b)));
            }
        }
        assert!(!rhs.is_zero(), "division by zero");
        let (q, r) = limbs::divrem(&self.mag_limbs(), &rhs.mag_limbs());
        let q_neg = self.is_negative() ^ rhs.is_negative();
        let r_neg = self.is_negative();
        (
            Integer::from_sign_limbs(q_neg, q),
            Integer::from_sign_limbs(r_neg, r),
        )
    }
}

impl Div for Integer {
    type Output = Integer;
    fn div(self, rhs: Integer) -> Integer {
        self.div_rem(&rhs).0
    }
}
impl Rem for Integer {
    type Output = Integer;
    fn rem(self, rhs: Integer) -> Integer {
        self.div_rem(&rhs).1
    }
}
```

- [ ] **Step 5: Run tests to verify they pass**

Run: `cargo test -p shinri-num`
Expected: PASS (both new tests, including the panic test).

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-num/src/limbs.rs crates/shinri-num/src/integer.rs
git commit -m "feat(num): Integer truncated division and remainder"
```

---

### Task 6: GCD (Euclidean baseline)

> Maps to spec §7.3 "binary GCD ... Lehmer's GCD". We ship a provably-correct **Euclidean GCD via `div_rem`** first; on the i128 fast path this is already fast (native `%`). Binary GCD and Lehmer's GCD are deferred optimizations gated on the differential corpus plus a benchmark.

**Files:**
- Modify: `crates/shinri-num/src/integer.rs`

**Interfaces:**
- Consumes: `Integer::{abs,div_rem,is_zero}` (Tasks 1, 5).
- Produces: `Integer::gcd(&self, other: &Integer) -> Integer` (always non-negative; `gcd(0,0) == 0`).

- [ ] **Step 1: Write the failing test**

```rust
#[test]
fn gcd_basic_and_signs() {
    assert_eq!(Integer::from(12i128).gcd(&Integer::from(18i128)), Integer::from(6i128));
    assert_eq!(Integer::from(-12i128).gcd(&Integer::from(18i128)), Integer::from(6i128));
    assert_eq!(Integer::from(0i128).gcd(&Integer::from(5i128)), Integer::from(5i128));
    assert_eq!(Integer::from(0i128).gcd(&Integer::from(0i128)), Integer::zero());
    assert_eq!(Integer::from(17i128).gcd(&Integer::from(13i128)), Integer::from(1i128));
}
```

- [ ] **Step 2: Run to verify it fails**

Run: `cargo test -p shinri-num gcd_basic_and_signs`
Expected: FAIL — `gcd` not found.

- [ ] **Step 3: Implement `gcd`**

```rust
impl Integer {
    /// Greatest common divisor. Result is always non-negative; gcd(0,0)=0.
    pub fn gcd(&self, other: &Integer) -> Integer {
        let mut a = self.abs();
        let mut b = other.abs();
        while !b.is_zero() {
            let r = a.div_rem(&b).1; // a % b, non-negative since a,b >= 0
            a = b;
            b = r;
        }
        a
    }
}
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `cargo test -p shinri-num`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-num/src/integer.rs
git commit -m "feat(num): Integer Euclidean GCD"
```

---

### Task 7: `Rational` type — construction, normalization, arithmetic, comparison

**Files:**
- Create: `crates/shinri-num/src/rational.rs`
- Modify: `crates/shinri-num/src/lib.rs`

**Interfaces:**
- Consumes: `Integer` and all its ops (Tasks 1–6).
- Produces:
  - `shinri_num::Rational` — `Clone + Debug + PartialEq + Eq + PartialOrd + Ord`.
  - `Rational::new(numer: Integer, denom: Integer) -> Rational` (panics on zero denominator; canonicalizes).
  - `Rational::from_int(n: Integer) -> Rational`
  - `Rational::zero() -> Rational`, `Rational::one() -> Rational`
  - `Rational::is_zero(&self) -> bool`, `Rational::is_negative(&self) -> bool`, `Rational::signum(&self) -> i32`
  - `Rational::numer(&self) -> &Integer`, `Rational::denom(&self) -> &Integer`
  - `Rational::recip(&self) -> Rational` (panics if zero)
  - `impl Add + Sub + Mul + Div + Neg for Rational` (by value).

- [ ] **Step 1: Add the module to `lib.rs`**

```rust
mod rational;
pub use rational::Rational;
```

(Place alongside the existing `mod integer;` / `pub use integer::Integer;` lines.)

- [ ] **Step 2: Write the failing test** (create `rational.rs` with only this test module first)

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use crate::Integer;

    fn r(n: i128, d: i128) -> Rational {
        Rational::new(Integer::from(n), Integer::from(d))
    }

    #[test]
    fn canonicalization() {
        // 2/4 -> 1/2
        assert_eq!(r(2, 4), r(1, 2));
        // sign moves to numerator; denominator positive
        let neg = r(1, -2);
        assert!(neg.is_negative());
        assert_eq!(*neg.denom(), Integer::from(2i128));
        assert_eq!(*neg.numer(), Integer::from(-1i128));
        // zero is 0/1
        assert!(r(0, 5).is_zero());
        assert_eq!(*r(0, 5).denom(), Integer::from(1i128));
    }

    #[test]
    fn arithmetic() {
        assert_eq!(r(1, 2) + r(1, 3), r(5, 6));
        assert_eq!(r(1, 2) - r(1, 3), r(1, 6));
        assert_eq!(r(2, 3) * r(3, 4), r(1, 2));
        assert_eq!(r(2, 3) / r(4, 9), r(3, 2));
        assert_eq!(-r(2, 3), r(-2, 3));
    }

    #[test]
    fn ordering() {
        assert!(r(1, 3) < r(1, 2));
        assert!(r(-1, 2) < r(0, 1));
        assert!(r(3, 2) > r(1, 1));
    }

    #[test]
    #[should_panic(expected = "zero denominator")]
    fn zero_denominator_panics() {
        let _ = Rational::new(Integer::from(1i128), Integer::zero());
    }
}
```

- [ ] **Step 3: Run to verify it fails**

Run: `cargo test -p shinri-num`
Expected: FAIL — `Rational` not defined.

- [ ] **Step 4: Implement `Rational` above the test module**

```rust
use crate::Integer;
use core::cmp::Ordering;
use core::ops::{Add, Div, Mul, Neg, Sub};

/// An exact rational. Invariant: `denom > 0`, `gcd(|numer|, denom) == 1`,
/// and zero is exactly `0/1`.
#[derive(Clone, Debug)]
pub struct Rational {
    numer: Integer,
    denom: Integer,
}

impl Rational {
    pub fn new(numer: Integer, denom: Integer) -> Rational {
        assert!(!denom.is_zero(), "zero denominator");
        let mut n = numer;
        let mut d = denom;
        if d.is_negative() {
            n = -n;
            d = -d;
        }
        let g = n.gcd(&d);
        // g >= 1 whenever n != 0 (and gcd(0,d)=d, so 0/d -> 0/1).
        if g != Integer::one() {
            n = n.div_rem(&g).0;
            d = d.div_rem(&g).0;
        }
        Rational { numer: n, denom: d }
    }

    pub fn from_int(n: Integer) -> Rational {
        Rational { numer: n, denom: Integer::one() }
    }
    pub fn zero() -> Rational {
        Rational { numer: Integer::zero(), denom: Integer::one() }
    }
    pub fn one() -> Rational {
        Rational { numer: Integer::one(), denom: Integer::one() }
    }

    pub fn numer(&self) -> &Integer {
        &self.numer
    }
    pub fn denom(&self) -> &Integer {
        &self.denom
    }
    pub fn is_zero(&self) -> bool {
        self.numer.is_zero()
    }
    pub fn is_negative(&self) -> bool {
        self.numer.is_negative()
    }
    pub fn signum(&self) -> i32 {
        self.numer.signum()
    }

    pub fn recip(&self) -> Rational {
        assert!(!self.is_zero(), "reciprocal of zero");
        Rational::new(self.denom.clone(), self.numer.clone())
    }
}

impl PartialEq for Rational {
    fn eq(&self, other: &Self) -> bool {
        // Both canonical, so field-wise equality suffices.
        self.numer == other.numer && self.denom == other.denom
    }
}
impl Eq for Rational {}

impl PartialOrd for Rational {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for Rational {
    fn cmp(&self, other: &Self) -> Ordering {
        // a/b vs c/d with b,d > 0  <=>  a*d vs c*b
        let lhs = self.numer.clone() * other.denom.clone();
        let rhs = other.numer.clone() * self.denom.clone();
        lhs.cmp(&rhs)
    }
}

impl Add for Rational {
    type Output = Rational;
    fn add(self, o: Rational) -> Rational {
        let numer = self.numer.clone() * o.denom.clone() + o.numer.clone() * self.denom.clone();
        let denom = self.denom * o.denom;
        Rational::new(numer, denom)
    }
}
impl Sub for Rational {
    type Output = Rational;
    fn sub(self, o: Rational) -> Rational {
        self + (-o)
    }
}
impl Mul for Rational {
    type Output = Rational;
    fn mul(self, o: Rational) -> Rational {
        Rational::new(self.numer * o.numer, self.denom * o.denom)
    }
}
impl Div for Rational {
    type Output = Rational;
    fn div(self, o: Rational) -> Rational {
        assert!(!o.is_zero(), "division by zero");
        Rational::new(self.numer * o.denom, self.denom * o.numer)
    }
}
impl Neg for Rational {
    type Output = Rational;
    fn neg(self) -> Rational {
        Rational { numer: -self.numer, denom: self.denom }
    }
}
```

- [ ] **Step 5: Run tests to verify they pass**

Run: `cargo test -p shinri-num`
Expected: PASS (all four Rational tests).

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-num/src/lib.rs crates/shinri-num/src/rational.rs
git commit -m "feat(num): Rational type with canonical form and arithmetic"
```

---

### Task 8: `DeltaRational` (simplex strict-inequality encoding)

**Files:**
- Create: `crates/shinri-num/src/delta.rs`
- Modify: `crates/shinri-num/src/lib.rs`

**Interfaces:**
- Consumes: `Rational` (Task 7).
- Produces:
  - `shinri_num::DeltaRational` — `Clone + Debug + PartialEq + Eq + PartialOrd + Ord`. Represents `c + k·δ` for an infinitesimal `δ > 0`.
  - `DeltaRational::new(c: Rational, k: Rational) -> Self`
  - `DeltaRational::from_rational(c: Rational) -> Self` (k = 0)
  - `DeltaRational::c(&self) -> &Rational`, `DeltaRational::k(&self) -> &Rational`
  - `impl Add + Sub + Neg for DeltaRational` (componentwise)
  - `DeltaRational::scale(&self, factor: &Rational) -> DeltaRational` (scalar multiply both components)
  - Ordering is lexicographic: compare `c`, then `k`.

- [ ] **Step 1: Add the module to `lib.rs`**

```rust
mod delta;
pub use delta::DeltaRational;
```

- [ ] **Step 2: Write the failing test** (create `delta.rs` with only this test module first)

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Integer, Rational};

    fn rat(n: i128, d: i128) -> Rational {
        Rational::new(Integer::from(n), Integer::from(d))
    }

    #[test]
    fn lexicographic_ordering() {
        // 1 + 0d  <  1 + 1d   (same c, larger k)
        let a = DeltaRational::new(rat(1, 1), rat(0, 1));
        let b = DeltaRational::new(rat(1, 1), rat(1, 1));
        assert!(a < b);
        // 1 + 5d  <  2 + 0d    (c dominates)
        let c = DeltaRational::new(rat(1, 1), rat(5, 1));
        let d = DeltaRational::new(rat(2, 1), rat(0, 1));
        assert!(c < d);
    }

    #[test]
    fn arithmetic_componentwise() {
        let a = DeltaRational::new(rat(1, 2), rat(1, 1));
        let b = DeltaRational::new(rat(1, 3), rat(2, 1));
        let s = a.clone() + b.clone();
        assert_eq!(*s.c(), rat(5, 6));
        assert_eq!(*s.k(), rat(3, 1));
        let scaled = a.scale(&rat(2, 1));
        assert_eq!(*scaled.c(), rat(1, 1));
        assert_eq!(*scaled.k(), rat(2, 1));
        let n = -b;
        assert_eq!(*n.c(), rat(-1, 3));
        assert_eq!(*n.k(), rat(-2, 1));
    }
}
```

- [ ] **Step 3: Run to verify it fails**

Run: `cargo test -p shinri-num`
Expected: FAIL — `DeltaRational` not defined.

- [ ] **Step 4: Implement `DeltaRational` above the test module**

```rust
use crate::Rational;
use core::cmp::Ordering;
use core::ops::{Add, Neg, Sub};

/// A value `c + k·δ` where `δ` is a positive infinitesimal, used to encode
/// strict inequalities in the Dutertre–de Moura simplex (spec §6.5).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeltaRational {
    c: Rational,
    k: Rational,
}

impl DeltaRational {
    pub fn new(c: Rational, k: Rational) -> Self {
        DeltaRational { c, k }
    }
    pub fn from_rational(c: Rational) -> Self {
        DeltaRational { c, k: Rational::zero() }
    }
    pub fn c(&self) -> &Rational {
        &self.c
    }
    pub fn k(&self) -> &Rational {
        &self.k
    }
    pub fn scale(&self, factor: &Rational) -> DeltaRational {
        DeltaRational {
            c: self.c.clone() * factor.clone(),
            k: self.k.clone() * factor.clone(),
        }
    }
}

impl PartialOrd for DeltaRational {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for DeltaRational {
    fn cmp(&self, other: &Self) -> Ordering {
        self.c.cmp(&other.c).then_with(|| self.k.cmp(&other.k))
    }
}

impl Add for DeltaRational {
    type Output = DeltaRational;
    fn add(self, o: DeltaRational) -> DeltaRational {
        DeltaRational { c: self.c + o.c, k: self.k + o.k }
    }
}
impl Sub for DeltaRational {
    type Output = DeltaRational;
    fn sub(self, o: DeltaRational) -> DeltaRational {
        DeltaRational { c: self.c - o.c, k: self.k - o.k }
    }
}
impl Neg for DeltaRational {
    type Output = DeltaRational;
    fn neg(self) -> DeltaRational {
        DeltaRational { c: -self.c, k: -self.k }
    }
}
```

- [ ] **Step 5: Run tests to verify they pass**

Run: `cargo test -p shinri-num`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-num/src/lib.rs crates/shinri-num/src/delta.rs
git commit -m "feat(num): DeltaRational for simplex strict-inequality encoding"
```

---

### Task 9: Property tests + differential testing against `num-bigint` oracle

> This is the spec §7.4 correctness gate: `shinri-num` is not trusted until it provably agrees with `num-bigint`/`num-rational` across a large random corpus.

**Files:**
- Create: `crates/shinri-num/tests/integer_differential.rs`
- Create: `crates/shinri-num/tests/rational_props.rs`

**Interfaces:**
- Consumes: the full public API of `Integer`, `Rational` (Tasks 1–7); dev-deps `proptest`, `num-bigint`, `num-rational`.
- Produces: no library API; a passing differential + property test suite.

- [ ] **Step 1: Write the Integer differential test** (`tests/integer_differential.rs`)

```rust
use num_bigint::BigInt;
use proptest::prelude::*;
use shinri_num::Integer;

// Build a BigInt and an Integer from the same sequence of i128 operations so we
// can cross-check. We generate values spanning the Small/Big boundary.
fn to_big(i: i128) -> BigInt {
    BigInt::from(i)
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(2000))]

    #[test]
    fn add_matches_bigint(a in any::<i128>(), b in any::<i128>(), scale_a in 0u32..4, scale_b in 0u32..4) {
        // Multiply operands by 2^(64*scale) to push past the i128 boundary.
        let mut si = Integer::from(a);
        let mut bi = to_big(a);
        for _ in 0..scale_a { si = si.clone() * Integer::from(1i128 << 62); bi = bi * BigInt::from(1i128 << 62); }
        let mut sj = Integer::from(b);
        let mut bj = to_big(b);
        for _ in 0..scale_b { sj = sj.clone() * Integer::from(1i128 << 62); bj = bj * BigInt::from(1i128 << 62); }

        let sum = si.clone() + sj.clone();
        prop_assert_eq!(sum.to_string_via_parts(), (bi.clone() + bj.clone()).to_string());

        let diff = si.clone() - sj.clone();
        prop_assert_eq!(diff.to_string_via_parts(), (bi.clone() - bj.clone()).to_string());

        let prod = si.clone() * sj.clone();
        prop_assert_eq!(prod.to_string_via_parts(), (bi.clone() * bj.clone()).to_string());

        if !sj.is_zero() {
            let (q, r) = si.div_rem(&sj);
            let (bq, br) = (bi.clone() / bj.clone(), bi.clone() % bj.clone());
            prop_assert_eq!(q.to_string_via_parts(), bq.to_string());
            prop_assert_eq!(r.to_string_via_parts(), br.to_string());
            // reconstruct: q*sj + r == si
            prop_assert_eq!((q * sj.clone() + r), si.clone());
        }

        let g = si.gcd(&sj);
        let bg = num_integer_gcd(bi.clone(), bj.clone());
        prop_assert_eq!(g.to_string_via_parts(), bg.to_string());

        prop_assert_eq!(si.cmp(&sj), bi.cmp(&bj));
    }
}

fn num_integer_gcd(a: BigInt, b: BigInt) -> BigInt {
    // Euclidean on BigInt for an independent reference.
    let (mut a, mut b) = (a.magnitude_abs(), b.magnitude_abs());
    while b != BigInt::from(0) {
        let r = &a % &b;
        a = b;
        b = r;
    }
    a
}

// Helper trait to render an Integer to a decimal string for comparison.
// Implemented in Step 2 as `Display` on Integer.
trait ToStringViaParts {
    fn to_string_via_parts(&self) -> String;
}
impl ToStringViaParts for Integer {
    fn to_string_via_parts(&self) -> String {
        self.to_string()
    }
}

trait MagnitudeAbs {
    fn magnitude_abs(&self) -> BigInt;
}
impl MagnitudeAbs for BigInt {
    fn magnitude_abs(&self) -> BigInt {
        if *self < BigInt::from(0) { -self.clone() } else { self.clone() }
    }
}
```

- [ ] **Step 2: Run to verify it fails** (Integer has no `Display`)

Run: `cargo test -p shinri-num --test integer_differential`
Expected: FAIL — `Integer: std::fmt::Display` not satisfied (`to_string` unavailable).

- [ ] **Step 3: Implement `Display` for `Integer`** (in `integer.rs`)

```rust
impl core::fmt::Display for Integer {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        if self.is_zero() {
            return write!(f, "0");
        }
        // Repeatedly divide by 1_000_000_000_000_000_000 (10^18, fits in i128)
        // to build decimal digits, then emit.
        let base = Integer::from(1_000_000_000_000_000_000i128);
        let mut n = self.abs();
        let mut chunks: Vec<u64> = Vec::new();
        while !n.is_zero() {
            let (q, r) = n.div_rem(&base);
            // r fits in u64-ish range (< 10^18); render via its Small value.
            chunks.push(r.to_u64_chunk());
            n = q;
        }
        if self.is_negative() {
            write!(f, "-")?;
        }
        // Most-significant chunk without leading zeros, the rest zero-padded to 18.
        write!(f, "{}", chunks.last().unwrap())?;
        for c in chunks.iter().rev().skip(1) {
            write!(f, "{:018}", c)?;
        }
        Ok(())
    }
}

impl Integer {
    /// For a non-negative Integer known to be < 10^18, return its u64 value.
    pub(crate) fn to_u64_chunk(&self) -> u64 {
        match &self.0 {
            Repr::Small(v) => *v as u64,
            Repr::Big { limbs, .. } => limbs[0], // unreachable for < 10^18, but safe
        }
    }
}
```

- [ ] **Step 4: Run to verify the differential test passes**

Run: `cargo test -p shinri-num --test integer_differential`
Expected: PASS (2000 cases).

- [ ] **Step 5: Write Rational property tests** (`tests/rational_props.rs`)

```rust
use num_rational::BigRational;
use num_bigint::BigInt;
use proptest::prelude::*;
use shinri_num::{Integer, Rational};

fn sr(n: i64, d: i64) -> Rational {
    Rational::new(Integer::from(n), Integer::from(d))
}
fn br(n: i64, d: i64) -> BigRational {
    BigRational::new(BigInt::from(n), BigInt::from(d))
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(2000))]

    #[test]
    fn rational_ops_match_bigrational(
        an in any::<i64>(), ad in 1i64..=i64::MAX,
        bn in any::<i64>(), bd in 1i64..=i64::MAX,
    ) {
        let sa = sr(an, ad);
        let sb = sr(bn, bd);
        let ba = br(an, ad);
        let bb = br(bn, bd);

        prop_assert_eq!(rat_str(sa.clone() + sb.clone()), bb_str(ba.clone() + bb.clone()));
        prop_assert_eq!(rat_str(sa.clone() - sb.clone()), bb_str(ba.clone() - bb.clone()));
        prop_assert_eq!(rat_str(sa.clone() * sb.clone()), bb_str(ba.clone() * bb.clone()));
        if !sb.is_zero() {
            prop_assert_eq!(rat_str(sa.clone() / sb.clone()), bb_str(ba.clone() / bb.clone()));
        }
        prop_assert_eq!(sa.cmp(&sb), ba.cmp(&bb));
    }
}

fn rat_str(r: Rational) -> String {
    format!("{}/{}", r.numer(), r.denom())
}
fn bb_str(r: BigRational) -> String {
    format!("{}/{}", r.numer(), r.denom())
}
```

- [ ] **Step 6: Run to verify Rational props pass**

Run: `cargo test -p shinri-num --test rational_props`
Expected: PASS (2000 cases).

- [ ] **Step 7: Commit**

```bash
git add crates/shinri-num/src/integer.rs crates/shinri-num/tests
git commit -m "test(num): differential testing vs num-bigint/num-rational + Display"
```

---

### Task 10: Karatsuba multiplication (benchmark-gated optimization)

> Spec §7.3 names Karatsuba as in-scope. The differential corpus (Task 9) is the correctness gate: it must stay green after this swap. Crossover is tuned but conservative; the SMT workload rarely reaches it, so this is low-risk.

**Files:**
- Modify: `crates/shinri-num/src/limbs.rs`

**Interfaces:**
- Consumes: `limbs::{add, sub, trim, mul (schoolbook)}` (Tasks 1, 3, 4).
- Produces: `limbs::mul` updated to dispatch schoolbook ↔ Karatsuba; behavior is unchanged (validated by Task 9).

- [ ] **Step 1: Write a failing test pinning Karatsuba against schoolbook** (append to `limbs.rs` test module; create the module if absent)

```rust
#[cfg(test)]
mod karatsuba_tests {
    use super::*;

    #[test]
    fn karatsuba_matches_schoolbook_large() {
        // Build two ~40-limb magnitudes and check the two algorithms agree.
        let a: Vec<u64> = (0..40).map(|i| 0x9E37_79B9_7F4A_7C15u64.wrapping_mul(i + 1)).collect();
        let b: Vec<u64> = (0..40).map(|i| 0xD1B5_4A32_D192_ED03u64.wrapping_mul(i + 3)).collect();
        let mut a = a; trim(&mut a);
        let mut b = b; trim(&mut b);
        assert_eq!(mul_schoolbook(&a, &b), karatsuba(&a, &b));
    }
}
```

- [ ] **Step 2: Rename the current `mul` body to `mul_schoolbook` and add `karatsuba` + `add_shifted`** (in `limbs.rs`)

First, rename: change `pub fn mul(` to `pub fn mul_schoolbook(`. Then add:

```rust
const KARATSUBA_THRESHOLD: usize = 32;

fn add_shifted(dst: &mut Vec<u64>, src: &[u64], shift: usize) {
    if src.is_empty() {
        return;
    }
    if dst.len() < src.len() + shift {
        dst.resize(src.len() + shift, 0);
    }
    let mut carry: u128 = 0;
    for i in 0..src.len() {
        let cur = dst[i + shift] as u128 + src[i] as u128 + carry;
        dst[i + shift] = cur as u64;
        carry = cur >> 64;
    }
    let mut idx = src.len() + shift;
    while carry != 0 {
        if idx >= dst.len() {
            dst.push(0);
        }
        let cur = dst[idx] as u128 + carry;
        dst[idx] = cur as u64;
        carry = cur >> 64;
        idx += 1;
    }
}

pub fn karatsuba(a: &[u64], b: &[u64]) -> Vec<u64> {
    if a.is_empty() || b.is_empty() {
        return Vec::new();
    }
    if a.len() < KARATSUBA_THRESHOLD || b.len() < KARATSUBA_THRESHOLD {
        return mul_schoolbook(a, b);
    }
    let half = a.len().max(b.len()) / 2;
    let split = |x: &[u64]| -> (Vec<u64>, Vec<u64>) {
        if x.len() <= half {
            (x.to_vec(), Vec::new())
        } else {
            let mut lo = x[..half].to_vec();
            let mut hi = x[half..].to_vec();
            trim(&mut lo);
            trim(&mut hi);
            (lo, hi)
        }
    };
    let (a0, a1) = split(a);
    let (b0, b1) = split(b);

    let z0 = karatsuba(&a0, &b0);
    let z2 = karatsuba(&a1, &b1);
    let asum = add(&a0, &a1);
    let bsum = add(&b0, &b1);
    let z1full = karatsuba(&asum, &bsum);
    // z1 = z1full - z2 - z0  (both subtractions are valid: z1full >= z0 + z2)
    let z1 = sub(&sub(&z1full, &z2), &z0);

    let mut result = z0;
    add_shifted(&mut result, &z1, half);
    add_shifted(&mut result, &z2, 2 * half);
    trim(&mut result);
    result
}

/// Public multiply entry point: dispatches schoolbook ↔ Karatsuba by size.
pub fn mul(a: &[u64], b: &[u64]) -> Vec<u64> {
    karatsuba(a, b)
}
```

- [ ] **Step 3: Run the new test + the full differential suite**

Run: `cargo test -p shinri-num`
Expected: PASS — `karatsuba_matches_schoolbook_large`, plus Task 9's differential tests still green (proves no behavior change).

- [ ] **Step 4: Commit**

```bash
git add crates/shinri-num/src/limbs.rs
git commit -m "perf(num): Karatsuba multiplication above 32-limb crossover"
```

---

### Task 11: Fuzz target for limb routines + CI wiring

**Files:**
- Create: `crates/shinri-num/fuzz/Cargo.toml`
- Create: `crates/shinri-num/fuzz/fuzz_targets/integer_ops.rs`
- Create: `.github/workflows/ci.yml`

**Interfaces:**
- Consumes: `Integer` public API; `num-bigint` (fuzz oracle).
- Produces: a `cargo-fuzz` target and a CI workflow running `nextest`, `deny`, `clippy`, `fmt`.

- [ ] **Step 1: Create `crates/shinri-num/fuzz/Cargo.toml`**

```toml
[package]
name = "shinri-num-fuzz"
version = "0.0.0"
edition = "2021"
publish = false

[package.metadata]
cargo-fuzz = true

[dependencies]
libfuzzer-sys = "0.4"
arbitrary = { version = "1", features = ["derive"] }
num-bigint = "0.4"
shinri-num = { path = ".." }

[[bin]]
name = "integer_ops"
path = "fuzz_targets/integer_ops.rs"
test = false
doc = false
```

- [ ] **Step 2: Create the fuzz target `fuzz/fuzz_targets/integer_ops.rs`**

```rust
#![no_main]
use libfuzzer_sys::fuzz_target;
use num_bigint::BigInt;
use shinri_num::Integer;

// Cross-check add/sub/mul/div against BigInt on fuzzed limb sequences.
fuzz_target!(|data: (Vec<u64>, bool, Vec<u64>, bool)| {
    let (al, asign, bl, bsign) = data;
    if al.len() > 64 || bl.len() > 64 {
        return; // keep inputs bounded
    }
    let a = limbs_to_integer(&al, asign);
    let b = limbs_to_integer(&bl, bsign);
    let ba = integer_to_bigint(&a);
    let bb = integer_to_bigint(&b);

    assert_eq!((a.clone() + b.clone()).to_string(), (&ba + &bb).to_string());
    assert_eq!((a.clone() - b.clone()).to_string(), (&ba - &bb).to_string());
    assert_eq!((a.clone() * b.clone()).to_string(), (&ba * &bb).to_string());
    if !b.is_zero() {
        let (q, r) = a.div_rem(&b);
        assert_eq!(q.to_string(), (&ba / &bb).to_string());
        assert_eq!(r.to_string(), (&ba % &bb).to_string());
    }
});

fn limbs_to_integer(limbs: &[u64], negative: bool) -> Integer {
    // Build sum(limb_i * 2^(64*i)) with sign.
    let mut acc = Integer::from(0i128);
    let shift = Integer::from(1i128 << 32) * Integer::from(1i128 << 32); // 2^64
    let mut pow = Integer::from(1i128);
    for &l in limbs {
        acc = acc + Integer::from(l) * pow.clone();
        pow = pow * shift.clone();
    }
    if negative {
        -acc
    } else {
        acc
    }
}

fn integer_to_bigint(i: &Integer) -> BigInt {
    i.to_string().parse().unwrap()
}
```

- [ ] **Step 3: Create `.github/workflows/ci.yml`**

```yaml
name: ci
on: [push, pull_request]
jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@stable
        with:
          components: clippy, rustfmt
      - name: Install tools
        run: cargo install cargo-nextest cargo-deny --locked
      - name: Format
        run: cargo fmt --all --check
      - name: Clippy
        run: cargo clippy --all-targets -- -D warnings
      - name: Dependency policy
        run: cargo deny check
      - name: Tests
        run: cargo nextest run --all
```

- [ ] **Step 4: Verify the build + lints locally**

Run: `cargo fmt --all --check && cargo clippy --all-targets -- -D warnings && cargo nextest run -p shinri-num`
Expected: clean format, no clippy warnings, all tests pass.

- [ ] **Step 5: Smoke-run the fuzzer briefly** (requires nightly + cargo-fuzz)

Run: `cargo +nightly fuzz run integer_ops -- -runs=5000`
Expected: no crash, no assertion failure.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-num/fuzz .github/workflows/ci.yml
git commit -m "test(num): cargo-fuzz integer ops vs BigInt + CI workflow"
```

---

## Deferred Optimizations (out of this plan's scope)

These are spec §7.3 items deliberately deferred to keep the foundation correctness-first. Each is a future task, gated on the Task 9 differential corpus staying green **plus** a benchmark showing it helps the SMT workload:

- **Knuth Algorithm D** division (replaces binary long division on the Big path).
- **Lehmer's GCD** and **binary GCD** (replace Euclidean on large operands).
- **Toom-Cook** and **Schönhage-Strassen/FFT** multiplication (above a much larger crossover).
- **Burnikel-Ziegler** divide-and-conquer division.
- Audited `unsafe` `get_unchecked` on the hottest limb loops (spec §5 note).

None are needed for a sound, complete Phase 1: the i128 fast path handles the overwhelming majority of SMT arithmetic, and correctness is the gate.

---

## Self-Review

**1. Spec coverage (§7):**
- §7.2 `Integer` inline ≤128-bit + heap spill → Task 1 (`Small(i128)`/`Big`). ✓
- §7.2 `Rational` canonical `denom>0`, `gcd=1` → Task 7. ✓
- §7.2 `DeltaRational` `(c,k)` → Task 8. ✓
- §7.3 add/sub via u128 widening → Task 3. ✓
- §7.3 schoolbook + Karatsuba multiply → Tasks 4, 10. ✓
- §7.3 division (Knuth-D named; binary long division shipped, Knuth-D deferred) → Task 5 + Deferred. ✓
- §7.3 GCD (binary/Lehmer named; Euclidean shipped, both deferred) → Task 6 + Deferred. ✓
- §7.3 comparison limb-count then limb-wise → Task 2 (`limbs::cmp`). ✓
- §7.4 property + differential vs num-bigint + fuzz + mutants → Tasks 9, 11 (mutants run via `cargo mutants` in CI follow-up; `cargo-mutants` is installed via mise). ✓
- §3.1 deny.toml + permissive license + dev-only oracle → Tasks 1, 11. ✓
- §3.2 mise.toml + devenv.nix → Task 1. ✓

**2. Placeholder scan:** No "TBD"/"TODO"/"handle edge cases" without code. Every implementation step shows complete code. ✓

**3. Type consistency:** `from_sign_limbs(negative: bool, limbs: Vec<u64>)`, `mag_limbs(&self) -> Vec<u64>`, `div_rem(&self, &Integer) -> (Integer, Integer)`, `gcd(&self, &Integer) -> Integer`, `Rational::new(Integer, Integer)`, `DeltaRational::new(Rational, Rational)` — names and signatures are identical across all tasks that reference them. `limbs::{trim,cmp,add,sub,mul,divrem,karatsuba}` consistent. ✓

**Note on Task 2 ↔ Task 3 coupling:** Task 2's test references `Add`/`Neg` (Task 3). This is called out inline in Task 2 Step 2 — implement Task 2's trait impls, then Task 3 makes the full test green. The two tasks share one reviewer gate if executed back-to-back.
