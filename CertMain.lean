import CertProofs
import CertCheck

/-! # Cert CLI

`lake exe cert [name]` regenerates `slop/cert_<base>.lurk` for the named proof
(or all of them if no arg).  Pass `--check` first to also run the Lean-side
type checker on each proof and report ok/FAIL before dumping. -/

open Cert

private def proofs : List (String × String × BuilderM (Nat × Nat)) :=
  [ ("a_imp_a",                 "a_imp_a",   buildAImpA),
    ("not_not_not_a_imp_not_a", "triple_neg", buildTripleNeg),
    ("k",                       "k",          buildK),
    ("ki",                      "ki",         buildKI),
    ("id_fls",                  "id_fls",     buildIdFls),
    ("prod_fls_type",           "prod_fls_type", buildProdFlsType),
    ("sum_fls_type",            "sum_fls_type",  buildSumFlsType),
    ("eq_fls_type",             "eq_fls_type",   buildEqFlsType),
    ("beta_identity",           "beta_identity", buildBetaIdentity),
    ("iota_eq_smoke",           "iota_eq_smoke", buildIotaEqSmoke),
    ("iota_nat_z_smoke",        "iota_nat_z_smoke", buildIotaNatZSmoke),
    ("iota_nat_s_smoke",        "iota_nat_s_smoke", buildIotaNatSSmoke),
    ("iota_prod_smoke",         "iota_prod_smoke",  buildIotaProdSmoke),
    ("iota_sum_l_smoke",        "iota_sum_l_smoke", buildIotaSumLSmoke),
    ("iota_sum_r_smoke",        "iota_sum_r_smoke", buildIotaSumRSmoke),
    ("opaque_identity",         "opaque_identity",  buildOpaqueIdentity)
  ]

/-- Bad proofs: `checkLean` should reject these. -/
private def badProofs : List (String × BuilderM (Nat × Nat)) :=
  [ ("bad_lam_fls",        buildBadLamFls),
    ("bad_var_type",       buildBadVarType),
    ("bad_opaque_body",    buildBadOpaqueBody),
    ("unregistered_opaque", buildUnregisteredOpaque)
  ]

def main (args : List String) : IO Unit := do
  if args.head? == some "--check" then
    -- Lean-side type-check every proof; print ok/FAIL.
    let mut ok := 0
    let mut fail := 0
    for (name, _base, build) in proofs do
      let (good, _b, _es) := runCheck build
      if good then
        IO.println s!"  ok    {name}"
        ok := ok + 1
      else
        IO.println s!"  FAIL  {name}"
        fail := fail + 1
    IO.println s!"checkLean: {ok} ok / {fail} fail (expected: all ok)"
    -- Also run the bad proofs; we WANT them to fail.
    IO.println "\nNegative tests (these should be rejected):"
    let mut nOk := 0
    let mut nFail := 0
    for (name, build) in badProofs do
      let (good, _, _) := runCheck build
      if good then
        IO.println s!"  WRONGLY ACCEPTED  {name}"
        nOk := nOk + 1
      else
        IO.println s!"  correctly rejected  {name}"
        nFail := nFail + 1
    IO.println s!"checkLean (negative): {nFail} rejected / {nOk} wrongly accepted (expected: all rejected)"
    return
  let want := args.head?
  for (name, base, build) in proofs do
    match want with
    | some s => if s == name then runOne name base build
    | none   => runOne name base build
