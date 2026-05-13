//! Theorem anchor — Layer 4 of the soundness layering.
//!
//! Computes a 32-byte SHA-256 digest over the canonical encoding of the
//! "main" declaration (last entry in the declar map — by lean4export's
//! topological ordering, that's the user-named theorem). The anchor binds
//! the SNARK's public output to a specific theorem **statement** (name +
//! type expression), not just to the input bytes.
//!
//! ## Why a custom canonical encoding rather than `bincode(declar)`?
//!
//! `bincode(declar)` would include the declar's `Ptr` indices, which are
//! sensitive to the order things were inserted into the DAG. Two NDJSONs
//! that encode the same theorem statement could have different ptr
//! indices and therefore different bincode bytes — so verifiers couldn't
//! reproduce the anchor without running our exact host pipeline.
//!
//! The encoding here resolves every `Ptr` to its underlying content
//! (strings, primitives, nested structure) as the walk proceeds. The
//! resulting digest is a function of the term *shape*, not of how the
//! DAG happens to be laid out.

use sha2::{Digest, Sha256};

use crate::env::Declar;
use crate::expr::{Expr, FVarId};
use crate::level::Level;
use crate::name::Name;
use crate::util::{
    BigUintPtr, CowStr, ExportFile, ExprPtr, LeanDag, LevelPtr, LevelsPtr, NamePtr, StringPtr,
};

// ---------------------------------------------------------------------------
// Type tags. One byte per node kind, fixed forever — changing these would
// invalidate any anchor a verifier has previously cached.
// ---------------------------------------------------------------------------

const TAG_NAME_ANON: u8 = 0;
const TAG_NAME_STR: u8 = 1;
const TAG_NAME_NUM: u8 = 2;

const TAG_LEVEL_ZERO: u8 = 10;
const TAG_LEVEL_SUCC: u8 = 11;
const TAG_LEVEL_MAX: u8 = 12;
const TAG_LEVEL_IMAX: u8 = 13;
const TAG_LEVEL_PARAM: u8 = 14;

const TAG_EXPR_VAR: u8 = 20;
const TAG_EXPR_SORT: u8 = 21;
const TAG_EXPR_CONST: u8 = 22;
const TAG_EXPR_APP: u8 = 23;
const TAG_EXPR_PI: u8 = 24;
const TAG_EXPR_LAMBDA: u8 = 25;
const TAG_EXPR_LET: u8 = 26;
const TAG_EXPR_LOCAL: u8 = 27;
const TAG_EXPR_PROJ: u8 = 28;
const TAG_EXPR_STRINGLIT: u8 = 29;
const TAG_EXPR_NATLIT: u8 = 30;

// ---------------------------------------------------------------------------
// Public entry point.
// ---------------------------------------------------------------------------

/// Compute the anchor for the declaration at `declars[idx]`. Returns
/// `None` if the index is out of bounds. The SNARK commits this anchor to
/// the public output so verifiers can check the proof is for *their*
/// theorem statement.
pub fn declaration_anchor<'p>(ef: &ExportFile<'p>, idx: usize) -> Option<[u8; 32]> {
    let (_n, declar) = ef.declars.get_index(idx)?;
    Some(hash_declar(&ef.dag, declar))
}

/// Convenience — anchor the *last* declaration (by lean4export's topological
/// ordering, this is the user-supplied theorem; its dependencies come first).
pub fn last_declaration_anchor<'p>(ef: &ExportFile<'p>) -> Option<[u8; 32]> {
    if ef.declars.is_empty() {
        return None;
    }
    declaration_anchor(ef, ef.declars.len() - 1)
}

// ---------------------------------------------------------------------------
// Hashing the "outermost" declar. We commit to the kind of declar (axiom
// vs theorem vs definition vs ...) plus its name and type. We deliberately
// DO NOT hash the body of theorems/definitions — the body is the proof,
// which is the thing the SNARK certifies via type-checking. The anchor
// binds to the *statement*, not the proof.
// ---------------------------------------------------------------------------

fn hash_declar<'p>(dag: &LeanDag<'p>, d: &Declar<'p>) -> [u8; 32] {
    let mut h = Sha256::new();
    match d {
        Declar::Axiom { info } => {
            h.update([0u8]);
            hash_name_into(&mut h, dag, info.name);
            hash_levels_params_into(&mut h, dag, info.uparams);
            hash_expr_into(&mut h, dag, info.ty);
        }
        Declar::Quot { info } => {
            h.update([1u8]);
            hash_name_into(&mut h, dag, info.name);
            hash_levels_params_into(&mut h, dag, info.uparams);
            hash_expr_into(&mut h, dag, info.ty);
        }
        Declar::Theorem { info, .. } => {
            h.update([2u8]);
            hash_name_into(&mut h, dag, info.name);
            hash_levels_params_into(&mut h, dag, info.uparams);
            hash_expr_into(&mut h, dag, info.ty);
        }
        Declar::Definition { info, .. } => {
            h.update([3u8]);
            hash_name_into(&mut h, dag, info.name);
            hash_levels_params_into(&mut h, dag, info.uparams);
            hash_expr_into(&mut h, dag, info.ty);
        }
        Declar::Opaque { info, .. } => {
            h.update([4u8]);
            hash_name_into(&mut h, dag, info.name);
            hash_levels_params_into(&mut h, dag, info.uparams);
            hash_expr_into(&mut h, dag, info.ty);
        }
        Declar::Inductive(d) => {
            h.update([5u8]);
            hash_name_into(&mut h, dag, d.info.name);
            hash_levels_params_into(&mut h, dag, d.info.uparams);
            hash_expr_into(&mut h, dag, d.info.ty);
            h.update((d.num_params as u32).to_le_bytes());
            h.update((d.num_indices as u32).to_le_bytes());
        }
        Declar::Constructor(c) => {
            h.update([6u8]);
            hash_name_into(&mut h, dag, c.info.name);
            hash_levels_params_into(&mut h, dag, c.info.uparams);
            hash_expr_into(&mut h, dag, c.info.ty);
            h.update((c.ctor_idx as u32).to_le_bytes());
        }
        Declar::Recursor(r) => {
            h.update([7u8]);
            hash_name_into(&mut h, dag, r.info.name);
            hash_levels_params_into(&mut h, dag, r.info.uparams);
            hash_expr_into(&mut h, dag, r.info.ty);
            h.update((r.num_params as u32).to_le_bytes());
            h.update((r.num_indices as u32).to_le_bytes());
            h.update((r.num_motives as u32).to_le_bytes());
            h.update((r.num_minors as u32).to_le_bytes());
            h.update([if r.is_k { 1 } else { 0 }]);
        }
    }
    h.finalize().into()
}

// ---------------------------------------------------------------------------
// Recursive walks. Each emits a type tag, then content; for child nodes we
// recurse so the digest depends on tree shape, not on DAG indices.
// ---------------------------------------------------------------------------

fn hash_name_into<'p>(h: &mut Sha256, dag: &LeanDag<'p>, p: NamePtr<'p>) {
    let n = dag.names.get_index(p.idx()).copied().unwrap();
    match n {
        Name::Anon => {
            h.update([TAG_NAME_ANON]);
        }
        Name::Str(pfx, sfx, _) => {
            h.update([TAG_NAME_STR]);
            hash_name_into(h, dag, pfx);
            hash_string_into(h, dag, sfx);
        }
        Name::Num(pfx, k, _) => {
            h.update([TAG_NAME_NUM]);
            hash_name_into(h, dag, pfx);
            h.update(k.to_le_bytes());
        }
    }
}

fn hash_string_into<'p>(h: &mut Sha256, dag: &LeanDag<'p>, p: StringPtr<'p>) {
    let s = dag.strings.get_index(p.idx()).unwrap();
    let bytes: &[u8] = match s {
        CowStr::Borrowed(s) => s.as_bytes(),
        CowStr::Owned(s) => s.as_bytes(),
    };
    h.update((bytes.len() as u64).to_le_bytes());
    h.update(bytes);
}

fn hash_level_into<'p>(h: &mut Sha256, dag: &LeanDag<'p>, p: LevelPtr<'p>) {
    let l = dag.levels.get_index(p.idx()).copied().unwrap();
    match l {
        Level::Zero => {
            h.update([TAG_LEVEL_ZERO]);
        }
        Level::Succ(pred, _) => {
            h.update([TAG_LEVEL_SUCC]);
            hash_level_into(h, dag, pred);
        }
        Level::Max(a, b, _) => {
            h.update([TAG_LEVEL_MAX]);
            hash_level_into(h, dag, a);
            hash_level_into(h, dag, b);
        }
        Level::IMax(a, b, _) => {
            h.update([TAG_LEVEL_IMAX]);
            hash_level_into(h, dag, a);
            hash_level_into(h, dag, b);
        }
        Level::Param(name, _) => {
            h.update([TAG_LEVEL_PARAM]);
            hash_name_into(h, dag, name);
        }
    }
}

fn hash_levels_into<'p>(h: &mut Sha256, dag: &LeanDag<'p>, p: LevelsPtr<'p>) {
    let v = dag.uparams.get_index(p.idx()).cloned().unwrap();
    h.update((v.len() as u64).to_le_bytes());
    for l in v.iter() {
        hash_level_into(h, dag, *l);
    }
}

/// For a declar's universe parameters, we want to commit to the LIST of
/// param-names (positional). They're stored as a `LevelsPtr`, but only
/// `Level::Param` entries should appear there.
fn hash_levels_params_into<'p>(h: &mut Sha256, dag: &LeanDag<'p>, p: LevelsPtr<'p>) {
    hash_levels_into(h, dag, p)
}

fn hash_biguint_into<'p>(h: &mut Sha256, dag: &LeanDag<'p>, p: BigUintPtr<'p>) {
    let bs = dag.bignums.as_ref().expect("nat literal but no bignum store").get_index(p.idx()).unwrap();
    let raw = bs.to_bytes_le();
    h.update((raw.len() as u64).to_le_bytes());
    h.update(&raw);
}

fn hash_expr_into<'p>(h: &mut Sha256, dag: &LeanDag<'p>, p: ExprPtr<'p>) {
    let e = dag.exprs.get_index(p.idx()).copied().unwrap();
    match e {
        Expr::Var { dbj_idx, .. } => {
            h.update([TAG_EXPR_VAR]);
            h.update((dbj_idx as u32).to_le_bytes());
        }
        Expr::Sort { level, .. } => {
            h.update([TAG_EXPR_SORT]);
            hash_level_into(h, dag, level);
        }
        Expr::Const { name, levels, .. } => {
            h.update([TAG_EXPR_CONST]);
            hash_name_into(h, dag, name);
            hash_levels_into(h, dag, levels);
        }
        Expr::App { fun, arg, .. } => {
            h.update([TAG_EXPR_APP]);
            hash_expr_into(h, dag, fun);
            hash_expr_into(h, dag, arg);
        }
        Expr::Pi { binder_name, binder_type, body, .. } => {
            // We deliberately omit `binder_style` — that's pretty-printing
            // metadata, not part of the type's identity for our purposes.
            h.update([TAG_EXPR_PI]);
            hash_name_into(h, dag, binder_name);
            hash_expr_into(h, dag, binder_type);
            hash_expr_into(h, dag, body);
        }
        Expr::Lambda { binder_name, binder_type, body, .. } => {
            h.update([TAG_EXPR_LAMBDA]);
            hash_name_into(h, dag, binder_name);
            hash_expr_into(h, dag, binder_type);
            hash_expr_into(h, dag, body);
        }
        Expr::Let { binder_name, binder_type, val, body, .. } => {
            h.update([TAG_EXPR_LET]);
            hash_name_into(h, dag, binder_name);
            hash_expr_into(h, dag, binder_type);
            hash_expr_into(h, dag, val);
            hash_expr_into(h, dag, body);
        }
        Expr::Local { binder_name, binder_type, id, .. } => {
            h.update([TAG_EXPR_LOCAL]);
            hash_name_into(h, dag, binder_name);
            hash_expr_into(h, dag, binder_type);
            match id {
                FVarId::DbjLevel(l) => {
                    h.update([0u8]);
                    h.update((l as u32).to_le_bytes());
                }
                FVarId::Unique(u) => {
                    h.update([1u8]);
                    h.update(u.to_le_bytes());
                }
            }
        }
        Expr::Proj { ty_name, idx, structure, .. } => {
            h.update([TAG_EXPR_PROJ]);
            hash_name_into(h, dag, ty_name);
            h.update((idx as u64).to_le_bytes());
            hash_expr_into(h, dag, structure);
        }
        Expr::StringLit { ptr, .. } => {
            h.update([TAG_EXPR_STRINGLIT]);
            hash_string_into(h, dag, ptr);
        }
        Expr::NatLit { ptr, .. } => {
            h.update([TAG_EXPR_NATLIT]);
            hash_biguint_into(h, dag, ptr);
        }
    }
}
