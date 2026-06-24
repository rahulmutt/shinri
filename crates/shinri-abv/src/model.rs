//! Finite array model assembly + SMT-LIB `store`-chain rendering.
use shinri_core::{BuiltinOp, Context, Op, SortNode, TermId, TermNode};
use shinri_num::Integer;

use crate::abstraction::Abstraction;
use crate::collect::Collected;
use crate::driver::SatBridge;

/// A finite array model: a default element value plus a list of
/// (index value → element value) override points, sorted by index.
pub struct ArrayModel {
    pub idx_width: u32,
    pub elem_width: u32,
    /// Sorted, deduplicated by index value.
    pub points: Vec<(Integer, Integer)>,
    pub default: Integer,
}

// ---------------------------------------------------------------------------
// Formatting helpers (mirrored from `shinri-solver`'s private helpers).
// ---------------------------------------------------------------------------

/// Format `val` as exactly `digits` lower-case hex characters (no prefix).
fn format_hex_fixed(val: &Integer, digits: usize) -> String {
    let sixteen = Integer::from(16u64);
    let mut remaining = val.clone();
    let mut nibbles: Vec<u8> = Vec::with_capacity(digits);
    for _ in 0..digits {
        let (q, r) = remaining.div_rem(&sixteen);
        let nibble = r.to_i128().unwrap_or(0) as u8;
        nibbles.push(nibble);
        remaining = q;
    }
    nibbles.reverse();
    nibbles.iter().map(|&n| format!("{:x}", n)).collect()
}

/// Format `val` as exactly `width` binary characters, MSB first (no prefix).
fn format_bin_fixed(val: &Integer, width: u32) -> String {
    let two = Integer::from(2u64);
    let mut remaining = val.clone();
    let mut bits: Vec<u8> = Vec::with_capacity(width as usize);
    for _ in 0..width {
        let (q, r) = remaining.div_rem(&two);
        bits.push(r.to_i128().unwrap_or(0) as u8);
        remaining = q;
    }
    bits.reverse();
    bits.iter()
        .map(|&b| if b == 1 { '1' } else { '0' })
        .collect()
}

/// Format a BV constant as SMT-LIB literal (`#x…` or `#b…`).
fn fmt_bv(width: u32, val: &Integer) -> String {
    if width.is_multiple_of(4) {
        let digits = (width / 4) as usize;
        format!("#x{}", format_hex_fixed(val, digits))
    } else {
        format!("#b{}", format_bin_fixed(val, width))
    }
}

// ---------------------------------------------------------------------------
// Public interface
// ---------------------------------------------------------------------------

/// Render an `ArrayModel` as SMT-LIB: a nested chain of `store` over
/// `((as const (Array …)) default)`.
pub fn render(m: &ArrayModel) -> String {
    let base = format!(
        "((as const (Array (_ BitVec {}) (_ BitVec {}))) {})",
        m.idx_width,
        m.elem_width,
        fmt_bv(m.elem_width, &m.default)
    );
    let mut out = base;
    for (idx, val) in &m.points {
        out = format!(
            "(store {out} {} {})",
            fmt_bv(m.idx_width, idx),
            fmt_bv(m.elem_width, val)
        );
    }
    out
}

/// Extract the base array and index from a `select` application.
fn select_parts(ctx: &Context, sel: TermId) -> Option<(TermId, TermId)> {
    match ctx.term_node(sel) {
        TermNode::App {
            op: Op::Builtin(BuiltinOp::Select),
            args,
            ..
        } => {
            let k = ctx.children(*args);
            Some((k[0], k[1]))
        }
        _ => None,
    }
}

/// Build a finite array model for `arr` from the selects collected during
/// abstraction, reading concrete values through `bridge`.
///
/// Points are sorted by index value; first occurrence wins when two selects
/// share the same index. Default value is zero.
pub fn array_model(
    ctx: &Context,
    c: &Collected,
    abs: &Abstraction,
    arr: TermId,
    bridge: &dyn SatBridge,
) -> ArrayModel {
    let (idx_width, elem_width) = match ctx.sort_node(ctx.sort_of(arr)) {
        SortNode::Array(i, e) => (
            ctx.bv_width(*i).expect("array index must be a BV sort"),
            ctx.bv_width(*e).expect("array element must be a BV sort"),
        ),
        _ => panic!("array_model: term is not array-sorted"),
    };

    let mut points: Vec<(Integer, Integer)> = Vec::new();
    // Integer doesn't implement Hash, so we use a Vec for dedup.
    let mut seen: Vec<Integer> = Vec::new();

    for &sel in &c.selects {
        if let Some((base, idx)) = select_parts(ctx, sel) {
            if base != arr {
                continue;
            }
            if let Some(&r) = abs.read_of.get(&sel) {
                if let (Some((_iw, iv)), Some((_ew, rv))) =
                    (bridge.value_bv(ctx, idx), bridge.value_bv(ctx, r))
                {
                    if !seen.contains(&iv) {
                        seen.push(iv.clone());
                        points.push((iv, rv));
                    }
                }
            }
        }
    }

    points.sort_by(|a, b| a.0.cmp(&b.0));

    ArrayModel {
        idx_width,
        elem_width,
        points,
        default: Integer::from(0u64),
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn renders_nested_store_over_const() {
        let m = ArrayModel {
            idx_width: 8,
            elem_width: 8,
            points: vec![(Integer::from(1u64), Integer::from(255u64))],
            default: Integer::from(0u64),
        };
        let s = render(&m);
        assert_eq!(
            s,
            "(store ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x00) #x01 #xff)"
        );
    }
}
