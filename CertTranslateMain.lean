import CertTranslate
import CertCheck

/-! # CLI: translate a named test from Dependent.lean into a Cert dump.

Usage: `lake exe cert-translate <test-name>`
Produces `slop/cert_dep_<safe-name>.lurk`.

We deliberately reference small tests directly (not via `Dependent.tests`)
to avoid forcing evaluation of the giant sqrt term at startup. -/

open Cert

private def supported : List (String × (_root_.Term × _root_.Term)) :=
  [ ("a_imp_a",                 a_imp_a),
    ("a_imp_b_imp_ab",          a_imp_b_imp_ab),
    ("a_imp_b_imp_ba",          a_imp_b_imp_ba),
    ("not_ab_imp_not_a",        not_ab_imp_not_a),
    ("a_imp_not_not_a",         a_imp_not_not_a),
    ("not_not_not_a_imp_not_a", not_not_not_a_imp_not_a),
    ("forall_a_exists_b_eq_a",  forall_a_exists_b_eq_a),
    ("if'",                     if'),
    ("false_elim",              false_elim),
    ("sqrt_two_irrational",     sqrt_two_irrational) ]

/-- Helper theorems used (transitively) by `sqrt_two_irrational`.  Listed in
roughly the same order they appear in `Dependent.lean` (which is a valid
topological order — each definition references only earlier ones).

Order matters: theorem N may opaque-reference theorems 0..N-1; we register
them sequentially so dependencies are visible. -/
private def sqrtHelpers : List (String × _root_.Term × _root_.Term) :=
  [ ("false_elim",          false_elim.1,          false_elim.2),
    ("rw",                  rw.1,                  rw.2),
    ("eq_symm",             eq_symm.1,             eq_symm.2),
    ("eq_trans",            eq_trans.1,            eq_trans.2),
    ("cong_suc",            cong_suc.1,            cong_suc.2),
    ("cong_add_l",          cong_add_l.1,          cong_add_l.2),
    ("cong_add_r",          cong_add_r.1,          cong_add_r.2),
    ("zero_add",            zero_add.1,            zero_add.2),
    ("add_zero_eq_zero_add", add_zero_eq_zero_add.1, add_zero_eq_zero_add.2),
    ("succ_add",            succ_add.1,            succ_add.2),
    ("add_comm",            add_comm.1,            add_comm.2),
    ("add_assoc",           add_assoc.1,           add_assoc.2),
    -- Skip `pred`: it is a top-level function (an `ap nat_rec ...`), not a
    -- lambda-form proof.  Marking it opaque hides the iota-reduction
    -- `pred (suc n) ⟶ n`, which downstream proofs (e.g. suc_inj) rely on.
    ("zero_mul",            zero_mul.1,            zero_mul.2),
    ("succ_mul",            succ_mul.1,            succ_mul.2),
    ("mul_comm",            mul_comm.1,            mul_comm.2),
    ("succ_ne_zero",        succ_ne_zero.1,        succ_ne_zero.2),
    ("suc_inj",             suc_inj.1,             suc_inj.2),
    ("even_zero",           even_zero.1,           even_zero.2),
    ("even_imp_succ_odd",   even_imp_succ_odd.1,   even_imp_succ_odd.2),
    ("odd_imp_succ_even",   odd_imp_succ_even.1,   odd_imp_succ_even.2),
    ("even_or_odd",         even_or_odd.1,         even_or_odd.2),
    ("mul_two_eq_add",      mul_two_eq_add.1,      mul_two_eq_add.2),
    ("even_ne_odd_base",    even_ne_odd_base.1,    even_ne_odd_base.2),
    ("even_ne_odd",         even_ne_odd.1,         even_ne_odd.2),
    ("double_sum",          double_sum.1,          double_sum.2),
    ("double_inj",          double_inj.1,          double_inj.2),
    ("mul_even_even",       mul_even_even.1,       mul_even_even.2),
    ("odd_sq_odd",          odd_sq_odd.1,          odd_sq_odd.2),
    ("even_sq_imp_even",    even_sq_imp_even.1,    even_sq_imp_even.2),
    ("add_eq_zero_l",       add_eq_zero_l.1,       add_eq_zero_l.2),
    ("double_mul",          double_mul.1,          double_mul.2),
    ("sq_half",             sq_half.1,             sq_half.2),
    ("half_sq",             half_sq.1,             half_sq.2),
    ("strong_sqrt_two",     strong_sqrt_two.1,     strong_sqrt_two.2) ]

/-- Tests that should be translated with opaque helpers.  Keys must match
`supported` keys. -/
private def opaqueHelpersFor (name : String) :
    List (String × _root_.Term × _root_.Term) :=
  if name == "sqrt_two_irrational" then sqrtHelpers else []

/-- Run the Lean-side type checker before dumping, so we can report ok/FAIL
locally and skip producing a bogus Lurk dump. -/
def runTranslate (name : String) (pair : _root_.Term × _root_.Term) : IO Unit := do
  let helpers := opaqueHelpersFor name
  let build := Cert.translatePairWithTheorems helpers pair
  if !helpers.isEmpty then
    IO.println s!"  [info] {name}: using {helpers.length} opaque helpers"
  let t0 ← IO.monoMsNow
  let (ok, why, _b) := Cert.runCheckDebug build
  let t1 ← IO.monoMsNow
  if !ok then
    IO.println s!"  Lean-check FAIL  {name} ({t1 - t0} ms): {why}"
  else
    IO.println s!"  Lean-check ok    {name} ({t1 - t0} ms)"
  -- Dump anyway so we can disassemble and diagnose.
  Cert.runOneWithDbtypes name s!"dep_{name.replace "'" "_prime"}" build

def main (args : List String) : IO Unit := do
  match args with
  | [name] =>
    match supported.find? (·.1 == name) with
    | some (_, pair) => runTranslate name pair
    | none           => IO.println s!"test '{name}' not in the supported list"
  | [] =>
    IO.println "running all supported tests..."
    for (name, pair) in supported do
      runTranslate name pair
  | _ => IO.println "usage: cert-translate [<test-name>]"
