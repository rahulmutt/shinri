//! Slice 61: joint witness words for the free leaves of concat-subject
//! memberships (spec
//! `docs/superpowers/specs/2026-10-05-shinri-slice61-joint-concat-seeds-design.md`).
//!
//! `model::memb_seeds` seeds a leaf only against its OWN bare memberships,
//! so the operands of `(str.++ x "z" y) ∈ R` are never chosen together and
//! the post-solve gate rejects the composed concat. `joint_seeds` groups
//! concat-subject memberships by shared free leaves; `solve_group` runs one
//! DFS that assigns the leaves a character at a time while advancing every
//! constraint's derivative. The words are CANDIDATES: they override the
//! per-leaf seeds and the gate re-checks every assertion, so a miss or a bug
//! can only leave the prior sound `unknown`.

#![allow(dead_code)] // TEMP: removed in Task 3 (first non-test caller)

use crate::regex::{self, Rex};
use rustc_hash::FxHashSet;

/// Per-pass DFS step cap (spec §4.4): the witness search's own cap.
pub(crate) const JOINT_SEARCH_STEP_CAP: usize = regex::MEMB_SEARCH_STEP_CAP;
/// Pass 2's budget on the total characters of a group's leaves (spec §4.5).
pub(crate) const JOINT_FREE_LEN_CAP: usize = 64;

/// One operand of a flattened concat subject.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum JOp {
    /// A string constant's code points.
    Lit(Vec<u32>),
    /// A free leaf: an index into the group's leaf list.
    Leaf(usize),
}

/// The concatenation of `ops` is in `rex` (polarity already folded).
#[derive(Clone, Debug)]
pub(crate) struct JConstraint {
    pub(crate) ops: Vec<JOp>,
    pub(crate) rex: Rex,
}

/// How long each leaf's word may be (spec §4.5).
#[derive(Clone, Copy, Debug)]
pub(crate) enum Lengths<'a> {
    /// Pass 1: every leaf's exact model length, by leaf index.
    Fixed(&'a [usize]),
    /// Pass 2: free lengths; the total over all leaves is at most this.
    Free(usize),
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) enum Outcome {
    /// One word per leaf, by leaf index.
    Found(Vec<String>),
    /// No words exist within the lengths (and below every cap but steps).
    Exhausted,
    /// `JOINT_SEARCH_STEP_CAP` was hit: not a verdict.
    Aborted,
}

/// A DFS node. Leaves are assigned in index order.
#[derive(Clone)]
struct Node {
    /// The leaf being assigned (== the leaf count once all are assigned).
    leaf: usize,
    /// `Fixed`: characters the current leaf still needs. `Free`: budget left.
    rem: usize,
    /// The current leaf's own-language derivative.
    own: Rex,
    /// Per constraint: the next unconsumed operand and the derivative of its
    /// regex by everything consumed so far.
    cur: Vec<(usize, Rex)>,
    /// Words by leaf; the current leaf's is partial.
    words: Vec<Vec<u32>>,
}

/// Memo key: the node's state, plus every word that some constraint has
/// still to consume outside its active position (a constraint waiting on a
/// later leaf, or a repeated leaf). Those words shape the future, so two
/// nodes that differ only in them are different states.
type Key = (usize, usize, Rex, Vec<(usize, Rex)>, Vec<(usize, Vec<u32>)>);

#[derive(Clone, Copy)]
enum Move {
    /// Finish the current leaf.
    End,
    /// Append this code point to the current leaf.
    Char(u32),
}

enum Visit {
    Word,
    Dead,
    Abort,
    Explore(Key, Vec<Move>),
}

fn is_dead(r: &Rex) -> bool {
    matches!(r, Rex::Empty) || regex::node_count(r) > regex::FUEL_NODE_CAP
}

fn feed(r: &Rex, cs: &[u32]) -> Rex {
    let mut d = r.clone();
    for &c in cs {
        d = regex::deriv(c, &d);
        if is_dead(&d) {
            break;
        }
    }
    d
}

/// True iff constraint `j`'s next operand is the leaf being assigned.
fn is_active(n: &Node, cons: &[JConstraint], j: usize) -> bool {
    cons[j].ops.get(n.cur[j].0) == Some(&JOp::Leaf(n.leaf))
}

/// Consume each constraint's operands up to its next unassigned leaf
/// (constants, and the words of assigned leaves). False iff a derivative
/// died.
fn advance(n: &mut Node, cons: &[JConstraint]) -> bool {
    let Node {
        leaf, cur, words, ..
    } = n;
    for (c, (i, d)) in cons.iter().zip(cur.iter_mut()) {
        while let Some(op) = c.ops.get(*i) {
            let cs: &[u32] = match op {
                JOp::Lit(cs) => cs,
                JOp::Leaf(l) if *l < *leaf => &words[*l],
                JOp::Leaf(_) => break,
            };
            *d = feed(d, cs);
            if is_dead(d) {
                return false;
            }
            *i += 1;
        }
    }
    true
}

fn key(n: &Node, cons: &[JConstraint]) -> Key {
    let pending = (0..=n.leaf)
        .filter(|&l| {
            cons.iter().zip(&n.cur).any(|(c, (i, _))| {
                c.ops
                    .iter()
                    .enumerate()
                    .skip(*i)
                    .any(|(p, op)| *op == JOp::Leaf(l) && !(p == *i && l == n.leaf))
            })
        })
        .map(|l| (l, n.words[l].clone()))
        .collect();
    (n.leaf, n.rem, n.own.clone(), n.cur.clone(), pending)
}

fn moves(n: &Node, cons: &[JConstraint], lens: Lengths<'_>) -> Vec<Move> {
    let mut mv = Vec::new();
    let may_end = match lens {
        Lengths::Fixed(_) => n.rem == 0,
        Lengths::Free(_) => true,
    };
    // End first: in pass 2 this biases towards short words.
    if may_end && regex::nullable(&n.own) {
        mv.push(Move::End);
    }
    if n.rem > 0 {
        let mut parts = vec![n.own.clone()];
        parts.extend(
            (0..cons.len())
                .filter(|&j| is_active(n, cons, j))
                .map(|j| n.cur[j].1.clone()),
        );
        // Constraints that will consume this leaf's characters later: a
        // waiting one, or a later occurrence of this leaf in any.
        let later: Vec<&Rex> = (0..cons.len())
            .filter(|&j| {
                let from = n.cur[j].0 + usize::from(is_active(n, cons, j));
                cons[j].ops[from..].contains(&JOp::Leaf(n.leaf))
            })
            .map(|j| &n.cur[j].1)
            .collect();
        // The head bounds of an `Inter` are every member's: the common
        // refinement, then refined for `later`. `None` (past the cap) leaves
        // no char move — completeness only.
        if let Some(classes) = regex::joint_classes(&regex::inter(parts), &later) {
            mv.extend(
                classes
                    .into_iter()
                    .filter_map(|(lo, hi)| regex::class_witness(lo, hi))
                    .map(Move::Char),
            );
        }
    }
    mv
}

fn apply(n: &Node, mv: Move, own: &[Rex], cons: &[JConstraint], lens: Lengths<'_>) -> Option<Node> {
    let mut ch = n.clone();
    match mv {
        Move::Char(c) => {
            ch.own = regex::deriv(c, &n.own);
            if is_dead(&ch.own) {
                return None;
            }
            for j in 0..cons.len() {
                if is_active(n, cons, j) {
                    let d = regex::deriv(c, &n.cur[j].1);
                    if is_dead(&d) {
                        return None;
                    }
                    ch.cur[j].1 = d;
                }
            }
            ch.words[n.leaf].push(c);
            ch.rem -= 1;
        }
        Move::End => {
            for j in 0..cons.len() {
                if is_active(n, cons, j) {
                    ch.cur[j].0 += 1;
                }
            }
            ch.leaf += 1;
            if ch.leaf < own.len() {
                ch.own = own[ch.leaf].clone();
                if let Lengths::Fixed(ls) = lens {
                    ch.rem = ls[ch.leaf];
                }
            }
            if !advance(&mut ch, cons) {
                return None;
            }
        }
    }
    Some(ch)
}

fn visit(
    n: &Node,
    own: &[Rex],
    cons: &[JConstraint],
    lens: Lengths<'_>,
    steps: &mut usize,
    dead: &FxHashSet<Key>,
) -> Visit {
    if *steps >= JOINT_SEARCH_STEP_CAP {
        return Visit::Abort;
    }
    *steps += 1;
    if n.leaf == own.len() {
        // Every leaf is assigned, so `advance` consumed every operand.
        debug_assert!(cons.iter().zip(&n.cur).all(|(c, (i, _))| *i == c.ops.len()));
        return if n.cur.iter().all(|(_, d)| regex::nullable(d)) {
            Visit::Word
        } else {
            Visit::Dead
        };
    }
    let k = key(n, cons);
    if dead.contains(&k) {
        return Visit::Dead;
    }
    Visit::Explore(k, moves(n, cons, lens))
}

fn render(words: &[Vec<u32>]) -> Vec<String> {
    words
        .iter()
        .map(|w| {
            w.iter()
                .map(|&c| char::from_u32(c).expect("class_witness yields a char"))
                .collect()
        })
        .collect()
}

/// Words for a group's leaves such that every constraint's concatenation is
/// in its regex and every leaf is in its own language (spec §4.4). DFS with
/// an explicit frame stack (a leaf can be thousands of characters long) and
/// a dead-state memo, like `regex::search_word`.
pub(crate) fn solve_group(own: &[Rex], cons: &[JConstraint], lens: Lengths<'_>) -> Outcome {
    struct Frame {
        node: Node,
        key: Key,
        moves: Vec<Move>,
        idx: usize,
    }
    let mut root = Node {
        leaf: 0,
        rem: match lens {
            Lengths::Fixed(ls) => ls[0],
            Lengths::Free(b) => b,
        },
        own: own[0].clone(),
        cur: cons.iter().map(|c| (0, c.rex.clone())).collect(),
        words: vec![Vec::new(); own.len()],
    };
    if !advance(&mut root, cons) {
        return Outcome::Exhausted;
    }
    let mut steps = 0usize;
    let mut dead: FxHashSet<Key> = FxHashSet::default();
    let mut stack: Vec<Frame> = Vec::new();
    match visit(&root, own, cons, lens, &mut steps, &dead) {
        Visit::Word => return Outcome::Found(render(&root.words)),
        Visit::Dead => return Outcome::Exhausted,
        Visit::Abort => return Outcome::Aborted,
        Visit::Explore(key, moves) => stack.push(Frame {
            node: root,
            key,
            moves,
            idx: 0,
        }),
    }
    'descend: while let Some(mut f) = stack.pop() {
        while f.idx < f.moves.len() {
            let mv = f.moves[f.idx];
            f.idx += 1;
            let Some(child) = apply(&f.node, mv, own, cons, lens) else {
                continue;
            };
            match visit(&child, own, cons, lens, &mut steps, &dead) {
                Visit::Word => return Outcome::Found(render(&child.words)),
                Visit::Dead => continue,
                Visit::Abort => return Outcome::Aborted,
                Visit::Explore(key, moves) => {
                    stack.push(f);
                    stack.push(Frame {
                        node: child,
                        key,
                        moves,
                        idx: 0,
                    });
                    continue 'descend;
                }
            }
        }
        dead.insert(f.key);
    }
    Outcome::Exhausted
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::regex::{self, Rex};

    fn ch(c: char) -> Rex {
        Rex::Range(c as u32, c as u32)
    }

    fn lit(s: &str) -> JOp {
        JOp::Lit(s.chars().map(|c| c as u32).collect())
    }

    fn sigma_star() -> Rex {
        regex::inter(Vec::new())
    }

    /// Independent check: every constraint's composed subject and every
    /// leaf's own language accept `words` under `eval_membership`.
    fn satisfies(own: &[Rex], cons: &[JConstraint], words: &[String]) -> bool {
        own.iter()
            .zip(words)
            .all(|(r, w)| regex::eval_membership(w, r) == Some(true))
            && cons.iter().all(|c| {
                let s: String = c
                    .ops
                    .iter()
                    .map(|op| match op {
                        JOp::Lit(cs) => cs.iter().map(|&k| char::from_u32(k).unwrap()).collect(),
                        JOp::Leaf(i) => words[*i].clone(),
                    })
                    .collect();
                regex::eval_membership(&s, &c.rex) == Some(true)
            })
    }

    /// The `norn-benchmark-531` group (spec §1.2), leaves `var_8` = 0,
    /// `var_9` = 1. z3's model: `var_8 = "a"`, `var_9 = "aa"`.
    fn norn_531() -> (Vec<Rex>, Vec<JConstraint>) {
        let ab_star = regex::star(regex::union(vec![ch('b'), ch('a')]));
        let r1 = regex::concat(vec![
            regex::star(regex::concat(vec![ch('a'), ab_star.clone(), ch('z')])),
            ch('a'),
            ab_star,
        ]);
        let r2 = regex::concat(vec![
            regex::star(regex::union(vec![
                ch('z'),
                regex::concat(vec![ch('a'), regex::star(ch('a')), ch('z')]),
            ])),
            ch('a'),
            regex::star(ch('a')),
        ]);
        let r3 = regex::concat(vec![
            regex::star(regex::union(vec![
                ch('z'),
                ch('b'),
                regex::concat(vec![ch('a'), regex::union(vec![ch('z'), ch('a')])]),
            ])),
            ch('a'),
        ]);
        let au = regex::star(Rex::Range('a' as u32, 'u' as u32));
        let xzy = vec![JOp::Leaf(0), lit("z"), JOp::Leaf(1)];
        let cons = vec![
            JConstraint {
                ops: xzy.clone(),
                rex: r1,
            },
            JConstraint { ops: xzy, rex: r2 },
            JConstraint {
                ops: vec![lit("b"), JOp::Leaf(0), lit("z"), lit("b"), JOp::Leaf(1)],
                rex: regex::comp(r3),
            },
        ];
        (vec![au.clone(), au], cons)
    }

    fn found(o: Outcome) -> Vec<String> {
        match o {
            Outcome::Found(w) => w,
            other => panic!("expected Found, got {other:?}"),
        }
    }

    #[test]
    fn regex_035_shape_fixed() {
        // (str.++ y x) ∈ b*, no bare memberships: y = 0, x = 1.
        let own = vec![sigma_star(), sigma_star()];
        let cons = vec![JConstraint {
            ops: vec![JOp::Leaf(0), JOp::Leaf(1)],
            rex: regex::star(ch('b')),
        }];
        let w = found(solve_group(&own, &cons, Lengths::Fixed(&[1, 2])));
        assert_eq!(w, vec!["b".to_string(), "bb".to_string()]);
    }

    #[test]
    fn norn_531_fixed_at_z3_lengths() {
        let (own, cons) = norn_531();
        let w = found(solve_group(&own, &cons, Lengths::Fixed(&[1, 2])));
        assert!(satisfies(&own, &cons, &w), "{w:?}");
        assert_eq!((w[0].chars().count(), w[1].chars().count()), (1, 2));
    }

    #[test]
    fn repeated_leaf_is_forced_on_second_occurrence() {
        // x·"c"·x ∈ abcab: the second copy of x is fed as forced characters.
        let own = vec![sigma_star()];
        let cons = vec![JConstraint {
            ops: vec![JOp::Leaf(0), lit("c"), JOp::Leaf(0)],
            rex: regex::concat(vec![ch('a'), ch('b'), ch('c'), ch('a'), ch('b')]),
        }];
        assert_eq!(
            found(solve_group(&own, &cons, Lengths::Fixed(&[2]))),
            vec!["ab"]
        );
        // x·"c"·x ∈ abcba has no solution: the second copy must repeat the first.
        let cons2 = vec![JConstraint {
            ops: vec![JOp::Leaf(0), lit("c"), JOp::Leaf(0)],
            rex: regex::concat(vec![ch('a'), ch('b'), ch('c'), ch('b'), ch('a')]),
        }];
        assert_eq!(
            solve_group(&own, &cons2, Lengths::Fixed(&[2])),
            Outcome::Exhausted
        );
    }

    #[test]
    fn waiting_constraint_consumes_whole_word() {
        // x·y ∈ [a-b]* and y·x ∈ bab, leaves x = 0, y = 1: the second
        // constraint waits on y while x is assigned. [a-b]* alone gives x one
        // class [a-b] (witness 'a'); only `joint_classes`' refinement by the
        // waiting "bab" lets x be "ab".
        let ab = regex::star(regex::union(vec![ch('a'), ch('b')]));
        let own = vec![sigma_star(), sigma_star()];
        let cons = vec![
            JConstraint {
                ops: vec![JOp::Leaf(0), JOp::Leaf(1)],
                rex: ab,
            },
            JConstraint {
                ops: vec![JOp::Leaf(1), JOp::Leaf(0)],
                rex: regex::concat(vec![ch('b'), ch('a'), ch('b')]),
            },
        ];
        // |x| = 2, |y| = 1 forces y = "b", x = "ab".
        let w = found(solve_group(&own, &cons, Lengths::Fixed(&[2, 1])));
        assert_eq!(w, vec!["ab".to_string(), "b".to_string()]);
        assert!(satisfies(&own, &cons, &w));
    }

    #[test]
    fn jointly_empty_group_exhausted() {
        // x·y ∈ a*, x ∈ b+ (x's own language).
        let own = vec![
            regex::concat(vec![ch('b'), regex::star(ch('b'))]),
            sigma_star(),
        ];
        let cons = vec![JConstraint {
            ops: vec![JOp::Leaf(0), JOp::Leaf(1)],
            rex: regex::star(ch('a')),
        }];
        assert_eq!(
            solve_group(&own, &cons, Lengths::Fixed(&[1, 1])),
            Outcome::Exhausted
        );
    }

    #[test]
    fn long_fixed_length_found_without_recursion() {
        // x·"z" ∈ a*z with |x| = 3000: one frame per character.
        let own = vec![sigma_star()];
        let cons = vec![JConstraint {
            ops: vec![JOp::Leaf(0), lit("z")],
            rex: regex::concat(vec![regex::star(ch('a')), ch('z')]),
        }];
        let w = found(solve_group(&own, &cons, Lengths::Fixed(&[3000])));
        assert_eq!(w[0], "a".repeat(3000));
    }

    #[test]
    fn step_cap_aborts() {
        // x·y ∈ (a|c)* gives x two live characters per position; y·x ∈ ∅
        // waits on y, so every distinct x is a distinct memo key (its word is
        // pending) and no path succeeds: 2^20 paths > JOINT_SEARCH_STEP_CAP.
        let own = vec![sigma_star(), sigma_star()];
        let cons = vec![
            JConstraint {
                ops: vec![JOp::Leaf(0), JOp::Leaf(1)],
                rex: regex::star(regex::union(vec![ch('a'), ch('c')])),
            },
            JConstraint {
                ops: vec![JOp::Leaf(1), JOp::Leaf(0)],
                rex: Rex::Empty,
            },
        ];
        assert_eq!(
            solve_group(&own, &cons, Lengths::Fixed(&[20, 0])),
            Outcome::Aborted
        );
    }
}
