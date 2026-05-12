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

/-- Run the Lean-side type checker before dumping, so we can report ok/FAIL
locally and skip producing a bogus Lurk dump. -/
def runTranslate (name : String) (pair : _root_.Term × _root_.Term) : IO Unit := do
  let build := Cert.translatePair pair
  let (ok, why, _b) := Cert.runCheckDebug build
  if !ok then
    IO.println s!"  Lean-check FAIL  {name}: {why}"
  else
    IO.println s!"  Lean-check ok    {name}"
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
