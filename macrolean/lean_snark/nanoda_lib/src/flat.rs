//! Flat (de)serialisation of an `ExportFile` for the SP1 guest.
//!
//! ## Why this exists
//!
//! `parse_export_file` does serde_json line-by-line and rebuilds the term DAG
//! by hashing every node into `IndexSet`s. JSON parsing is extremely expensive
//! inside the SP1 zkVM (every transient `String` and `IndexSet` insert costs
//! cycles tracked in the proof). This module gives the host a way to do that
//! work outside the zkVM and ship a flat binary blob to the guest, which then
//! rehydrates an `ExportFile` by *in-order* insertion into fresh containers —
//! no JSON, no reordering, no equality probes against existing entries.
//!
//! ## Soundness
//!
//! The SNARK certifies what the guest does: deserialise these bytes, run
//! `check_all_declars`. To bind the proof to a particular Lean theorem, the
//! guest commits `sha256(input_bytes)` (see `zkvm_entry`). The conversion
//! `NDJSON -> FlatExportFile -> bytes` is deterministic and runs on the host;
//! anyone can re-run it on the original NDJSON and check the hash matches.

use std::sync::Arc;

use num_bigint::BigUint;
use serde::{Deserialize, Serialize};

use crate::env::{
    ConstructorData, Declar, DeclarInfo, InductiveData, Notation, RecRule, RecursorData,
};
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;
use crate::util::{
    new_fx_hash_map, new_fx_index_map, BigUintPtr, Config, CowStr, ExportFile, ExprPtr, LeanDag,
    LevelPtr, LevelsPtr, NamePtr, StringPtr,
};

/// Resolve a `NamePtr` against a `LeanDag` to its dotted-path string form
/// (e.g. `Quot.lift`). Mirrors what the parser's private `name_to_string`
/// does — kept here so zkvm_entry can validate axioms post-deserialisation
/// without depending on parser internals.
pub(crate) fn name_to_string<'a>(dag: &LeanDag<'a>, p: NamePtr<'a>) -> String {
    match dag.names.get_index(p.idx()).copied().unwrap() {
        crate::name::Name::Anon => String::new(),
        crate::name::Name::Str(pfx, sfx, _) => {
            let s_owned: String = match dag.strings.get_index(sfx.idx()).unwrap() {
                CowStr::Borrowed(s) => (*s).to_string(),
                CowStr::Owned(s) => s.clone(),
            };
            let prefix = name_to_string(dag, pfx);
            if prefix.is_empty() { s_owned } else { format!("{}.{}", prefix, s_owned) }
        }
        crate::name::Name::Num(pfx, n, _) => {
            let prefix = name_to_string(dag, pfx);
            if prefix.is_empty() { n.to_string() } else { format!("{}.{}", prefix, n) }
        }
    }
}

// ---------------------------------------------------------------------------
// FlatExportFile — the on-the-wire form. All lifetimes erased to `'static`,
// since the runtime data is just `u32` indices + primitives + owned strings.
// ---------------------------------------------------------------------------

#[derive(Serialize, Deserialize)]
pub struct FlatExportFile {
    /// Names, EXCLUDING the implicit `Name::Anon` at index 0 of the rehydrated DAG.
    pub names: Vec<Name<'static>>,
    /// Levels, EXCLUDING the implicit `Level::Zero` at index 0.
    pub levels: Vec<Level<'static>>,
    pub exprs: Vec<Expr<'static>>,
    pub uparams: Vec<Vec<LevelPtr<'static>>>,
    pub strings: Vec<String>,
    pub bignums: Option<Vec<BigUint>>,
    pub declars: Vec<(NamePtr<'static>, Declar<'static>)>,
    pub notations: Vec<(NamePtr<'static>, Notation<'static>)>,
    pub mutual_block_sizes: Vec<(NamePtr<'static>, (usize, usize))>,
    pub config: Config,
}

// ---------------------------------------------------------------------------
// Lifetime-cast helpers. Every `Ptr<A>` is just a `u32` plus PhantomData, so
// changing the phantom lifetime is a no-op at runtime — these helpers do it
// safely by routing through `Ptr::cast<B>()` and rebuilding enums/structs
// field-by-field.
// ---------------------------------------------------------------------------

#[inline]
fn cast_name_ptr<'a, 'b>(p: NamePtr<'a>) -> NamePtr<'b> { p.cast() }
#[inline]
fn cast_level_ptr<'a, 'b>(p: LevelPtr<'a>) -> LevelPtr<'b> { p.cast() }
#[inline]
fn cast_expr_ptr<'a, 'b>(p: ExprPtr<'a>) -> ExprPtr<'b> { p.cast() }
#[inline]
fn cast_levels_ptr<'a, 'b>(p: LevelsPtr<'a>) -> LevelsPtr<'b> { p.cast() }
#[inline]
fn cast_string_ptr<'a, 'b>(p: StringPtr<'a>) -> StringPtr<'b> { p.cast() }
#[inline]
fn cast_biguint_ptr<'a, 'b>(p: BigUintPtr<'a>) -> BigUintPtr<'b> { p.cast() }

fn cast_name<'a, 'b>(n: Name<'a>) -> Name<'b> {
    match n {
        Name::Anon => Name::Anon,
        Name::Str(p, s, h) => Name::Str(cast_name_ptr(p), cast_string_ptr(s), h),
        Name::Num(p, k, h) => Name::Num(cast_name_ptr(p), k, h),
    }
}

fn cast_level<'a, 'b>(l: Level<'a>) -> Level<'b> {
    match l {
        Level::Zero => Level::Zero,
        Level::Succ(p, h) => Level::Succ(cast_level_ptr(p), h),
        Level::Max(a, b, h) => Level::Max(cast_level_ptr(a), cast_level_ptr(b), h),
        Level::IMax(a, b, h) => Level::IMax(cast_level_ptr(a), cast_level_ptr(b), h),
        Level::Param(n, h) => Level::Param(cast_name_ptr(n), h),
    }
}

fn cast_expr<'a, 'b>(e: Expr<'a>) -> Expr<'b> {
    match e {
        Expr::Var { hash, dbj_idx } => Expr::Var { hash, dbj_idx },
        Expr::Sort { hash, level } => Expr::Sort { hash, level: cast_level_ptr(level) },
        Expr::Const { hash, name, levels } => {
            Expr::Const { hash, name: cast_name_ptr(name), levels: cast_levels_ptr(levels) }
        }
        Expr::App { hash, fun, arg, num_loose_bvars, has_fvars } => Expr::App {
            hash,
            fun: cast_expr_ptr(fun),
            arg: cast_expr_ptr(arg),
            num_loose_bvars,
            has_fvars,
        },
        Expr::Pi {
            hash,
            binder_name,
            binder_style,
            binder_type,
            body,
            num_loose_bvars,
            has_fvars,
        } => Expr::Pi {
            hash,
            binder_name: cast_name_ptr(binder_name),
            binder_style,
            binder_type: cast_expr_ptr(binder_type),
            body: cast_expr_ptr(body),
            num_loose_bvars,
            has_fvars,
        },
        Expr::Lambda {
            hash,
            binder_name,
            binder_style,
            binder_type,
            body,
            num_loose_bvars,
            has_fvars,
        } => Expr::Lambda {
            hash,
            binder_name: cast_name_ptr(binder_name),
            binder_style,
            binder_type: cast_expr_ptr(binder_type),
            body: cast_expr_ptr(body),
            num_loose_bvars,
            has_fvars,
        },
        Expr::Let {
            hash,
            binder_name,
            binder_type,
            val,
            body,
            num_loose_bvars,
            has_fvars,
            nondep,
        } => Expr::Let {
            hash,
            binder_name: cast_name_ptr(binder_name),
            binder_type: cast_expr_ptr(binder_type),
            val: cast_expr_ptr(val),
            body: cast_expr_ptr(body),
            num_loose_bvars,
            has_fvars,
            nondep,
        },
        Expr::Local { hash, binder_name, binder_style, binder_type, id } => Expr::Local {
            hash,
            binder_name: cast_name_ptr(binder_name),
            binder_style,
            binder_type: cast_expr_ptr(binder_type),
            id,
        },
        Expr::Proj { hash, ty_name, idx, structure, num_loose_bvars, has_fvars } => Expr::Proj {
            hash,
            ty_name: cast_name_ptr(ty_name),
            idx,
            structure: cast_expr_ptr(structure),
            num_loose_bvars,
            has_fvars,
        },
        Expr::StringLit { hash, ptr } => Expr::StringLit { hash, ptr: cast_string_ptr(ptr) },
        Expr::NatLit { hash, ptr } => Expr::NatLit { hash, ptr: cast_biguint_ptr(ptr) },
    }
}

fn cast_arc_name_slice<'a, 'b>(slice: &Arc<[NamePtr<'a>]>) -> Arc<[NamePtr<'b>]> {
    let v: Vec<NamePtr<'b>> = slice.iter().map(|p| cast_name_ptr(*p)).collect();
    Arc::from(v)
}

fn cast_arc_recrules<'a, 'b>(slice: &Arc<[RecRule<'a>]>) -> Arc<[RecRule<'b>]> {
    let v: Vec<RecRule<'b>> = slice.iter().map(|r| cast_rec_rule(*r)).collect();
    Arc::from(v)
}

fn cast_declar_info<'a, 'b>(i: DeclarInfo<'a>) -> DeclarInfo<'b> {
    DeclarInfo {
        name: cast_name_ptr(i.name),
        uparams: cast_levels_ptr(i.uparams),
        ty: cast_expr_ptr(i.ty),
    }
}

fn cast_rec_rule<'a, 'b>(r: RecRule<'a>) -> RecRule<'b> {
    RecRule {
        ctor_name: cast_name_ptr(r.ctor_name),
        ctor_telescope_size_wo_params: r.ctor_telescope_size_wo_params,
        val: cast_expr_ptr(r.val),
    }
}

fn cast_inductive<'a, 'b>(i: &InductiveData<'a>) -> InductiveData<'b> {
    InductiveData {
        info: cast_declar_info(i.info),
        is_recursive: i.is_recursive,
        is_nested: i.is_nested,
        num_params: i.num_params,
        num_indices: i.num_indices,
        all_ind_names: cast_arc_name_slice(&i.all_ind_names),
        all_ctor_names: cast_arc_name_slice(&i.all_ctor_names),
    }
}

fn cast_constructor<'a, 'b>(c: &ConstructorData<'a>) -> ConstructorData<'b> {
    ConstructorData {
        info: cast_declar_info(c.info),
        inductive_name: cast_name_ptr(c.inductive_name),
        ctor_idx: c.ctor_idx,
        num_params: c.num_params,
        num_fields: c.num_fields,
    }
}

fn cast_recursor<'a, 'b>(r: &RecursorData<'a>) -> RecursorData<'b> {
    RecursorData {
        info: cast_declar_info(r.info),
        all_inductives: cast_arc_name_slice(&r.all_inductives),
        num_params: r.num_params,
        num_indices: r.num_indices,
        num_motives: r.num_motives,
        num_minors: r.num_minors,
        rec_rules: cast_arc_recrules(&r.rec_rules),
        is_k: r.is_k,
    }
}

fn cast_declar<'a, 'b>(d: &Declar<'a>) -> Declar<'b> {
    match d {
        Declar::Axiom { info } => Declar::Axiom { info: cast_declar_info(*info) },
        Declar::Quot { info } => Declar::Quot { info: cast_declar_info(*info) },
        Declar::Theorem { info, val } => {
            Declar::Theorem { info: cast_declar_info(*info), val: cast_expr_ptr(*val) }
        }
        Declar::Definition { info, val, hint } => Declar::Definition {
            info: cast_declar_info(*info),
            val: cast_expr_ptr(*val),
            hint: *hint,
        },
        Declar::Opaque { info, val } => {
            Declar::Opaque { info: cast_declar_info(*info), val: cast_expr_ptr(*val) }
        }
        Declar::Inductive(i) => Declar::Inductive(cast_inductive(i)),
        Declar::Constructor(c) => Declar::Constructor(cast_constructor(c)),
        Declar::Recursor(r) => Declar::Recursor(cast_recursor(r)),
    }
}

fn cast_notation<'a, 'b>(n: &Notation<'a>) -> Notation<'b> {
    match n {
        Notation::Prefix { name, priority, oper } => {
            Notation::Prefix { name: cast_name_ptr(*name), priority: *priority, oper: oper.clone() }
        }
        Notation::Infix { name, priority, oper } => {
            Notation::Infix { name: cast_name_ptr(*name), priority: *priority, oper: oper.clone() }
        }
        Notation::Postfix { name, priority, oper } => Notation::Postfix {
            name: cast_name_ptr(*name),
            priority: *priority,
            oper: oper.clone(),
        },
    }
}

// ---------------------------------------------------------------------------
// to_flat: ExportFile<'p> -> FlatExportFile (host side)
// ---------------------------------------------------------------------------

impl FlatExportFile {
    pub fn from_export_file<'p>(ef: &ExportFile<'p>) -> Self {
        // Skip slot 0 of names/levels — those are implicit `Anon` / `Zero`
        // that the rehydrator's fresh `LeanDag::new` will already contain.
        let names: Vec<Name<'static>> =
            ef.dag.names.iter().skip(1).map(|n| cast_name(*n)).collect();
        let levels: Vec<Level<'static>> =
            ef.dag.levels.iter().skip(1).map(|l| cast_level(*l)).collect();
        let exprs: Vec<Expr<'static>> = ef.dag.exprs.iter().map(|e| cast_expr(*e)).collect();

        let uparams: Vec<Vec<LevelPtr<'static>>> = ef
            .dag
            .uparams
            .iter()
            .map(|seq| seq.iter().map(|p| cast_level_ptr(*p)).collect())
            .collect();

        let strings: Vec<String> = ef
            .dag
            .strings
            .iter()
            .map(|c| match c {
                CowStr::Borrowed(s) => (*s).to_string(),
                CowStr::Owned(s) => s.clone(),
            })
            .collect();

        let bignums: Option<Vec<BigUint>> =
            ef.dag.bignums.as_ref().map(|s| s.iter().cloned().collect());

        let declars: Vec<(NamePtr<'static>, Declar<'static>)> = ef
            .declars
            .iter()
            .map(|(n, d)| (cast_name_ptr(*n), cast_declar(d)))
            .collect();

        let notations: Vec<(NamePtr<'static>, Notation<'static>)> = ef
            .notations
            .iter()
            .map(|(n, no)| (cast_name_ptr(*n), cast_notation(no)))
            .collect();

        let mutual_block_sizes: Vec<(NamePtr<'static>, (usize, usize))> = ef
            .mutual_block_sizes
            .iter()
            .map(|(n, sz)| (cast_name_ptr(*n), *sz))
            .collect();

        FlatExportFile {
            names,
            levels,
            exprs,
            uparams,
            strings,
            bignums,
            declars,
            notations,
            mutual_block_sizes,
            config: ef.config.clone(),
        }
    }

    /// Reverse of `from_export_file`. Inserts everything in the order it was
    /// written — since the underlying hashers are deterministic and the data
    /// has the same hash as the originals, indices align with what
    /// `parse_export_file` would have produced.
    pub fn into_export_file<'p>(self) -> ExportFile<'p> {
        let FlatExportFile {
            names,
            levels,
            exprs,
            uparams,
            strings,
            bignums,
            declars,
            notations,
            mutual_block_sizes,
            config,
        } = self;

        let mut dag: LeanDag<'p> = LeanDag::new(&config);

        for n in names {
            dag.names.insert(cast_name(n));
        }
        for l in levels {
            dag.levels.insert(cast_level(l));
        }
        for e in exprs {
            dag.exprs.insert(cast_expr(e));
        }
        for seq in uparams {
            let v: Vec<LevelPtr<'p>> = seq.into_iter().map(cast_level_ptr).collect();
            dag.uparams.insert(Arc::from(v));
        }
        for s in strings {
            dag.strings.insert(CowStr::Owned(s));
        }
        if let Some(nums) = bignums {
            if let Some(bset) = dag.bignums.as_mut() {
                for n in nums {
                    bset.insert(n);
                }
            }
        }

        let mut declars_map = new_fx_index_map();
        for (n, d) in declars {
            declars_map.insert(cast_name_ptr(n), cast_declar(&d));
        }

        let mut notations_map = new_fx_hash_map();
        for (n, no) in notations {
            notations_map.insert(cast_name_ptr(n), cast_notation(&no));
        }

        let mut mutual_block_sizes_map = new_fx_hash_map();
        for (n, sz) in mutual_block_sizes {
            mutual_block_sizes_map.insert(cast_name_ptr(n), sz);
        }

        let name_cache = dag.mk_name_cache();

        ExportFile {
            dag,
            declars: declars_map,
            notations: notations_map,
            name_cache,
            config,
            mutual_block_sizes: mutual_block_sizes_map,
        }
    }
}
