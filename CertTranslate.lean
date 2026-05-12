import Cert
import Dependent

/-! # Translator from `Dependent.Term` to `Cert.Node`

`Dependent.Term` is a regular tree; the per-`app` φ-field bloat is only
introduced at *serialisation* time.  We walk the tree once, calling our
hash-consing smart constructors, so the resulting indexed AST automatically
shares duplicate subterms.

The dbify-only constructors (`name`, `vlam`, `vfn`) should be gone before we
get here; if they're present, the translator panics.
-/

namespace Cert

partial def translateTerm : _root_.Term → BuilderM Nat
  | _root_.Term.var x        => Cert.var x
  | _root_.Term.lam b        => do let b' ← translateTerm b; Cert.lam b'
  | _root_.Term.app f φ a    => do
      let f' ← translateTerm f
      let φ' ← translateTerm φ
      let a' ← translateTerm a
      Cert.app f' φ' a'
  | _root_.Term.typ u        => Cert.typ u
  | _root_.Term.fn α β       => do
      let α' ← translateTerm α
      let β' ← translateTerm β
      Cert.fn α' β'
  | _root_.Term.prod α β     => do
      let α' ← translateTerm α
      let β' ← translateTerm β
      Cert.prod α' β'
  | _root_.Term.pmk          => Cert.pmk
  | _root_.Term.prod_rec     => Cert.prodRec
  | _root_.Term.sum α β      => do
      let α' ← translateTerm α
      let β' ← translateTerm β
      Cert.sum α' β'
  | _root_.Term.inl          => Cert.inl
  | _root_.Term.inr          => Cert.inr
  | _root_.Term.sum_rec      => Cert.sumRec
  | _root_.Term.eq a a' α    => do
      let ea  ← translateTerm a
      let ea' ← translateTerm a'
      let eα  ← translateTerm α
      Cert.eq ea ea' eα
  | _root_.Term.refl         => Cert.refl
  | _root_.Term.eq_rec       => Cert.eqRec
  | _root_.Term.nat          => Cert.nat
  | _root_.Term.zero         => Cert.zero
  | _root_.Term.succ         => Cert.succ
  | _root_.Term.nat_rec      => Cert.natRec
  | _root_.Term.unit         => Cert.unit
  | _root_.Term.intro        => Cert.intro
  | _root_.Term.fls          => Cert.fls
  | _root_.Term.fls_rec      => Cert.flsRec
  | _root_.Term.name s       => panic! s!"`name {s}` reached translator; call dbify first"
  | _root_.Term.vlam s _     => panic! s!"`vlam {s}` reached translator; call dbify first"
  | _root_.Term.vfn s _ _    => panic! s!"`vfn {s}` reached translator; call dbify first"

/-- The 14 built-in constructors that have a fixed dbtype (paired with their
tag number). -/
private def builtinConstants : List (Nat × _root_.Term) :=
  [ (6,  _root_.Term.pmk),
    (7,  _root_.Term.prod_rec),
    (9,  _root_.Term.inl),
    (10, _root_.Term.inr),
    (11, _root_.Term.sum_rec),
    (13, _root_.Term.refl),
    (14, _root_.Term.eq_rec),
    (15, _root_.Term.nat),
    (16, _root_.Term.zero),
    (17, _root_.Term.succ),
    (18, _root_.Term.nat_rec),
    (19, _root_.Term.unit),
    (20, _root_.Term.intro),
    (21, _root_.Term.fls),
    (22, _root_.Term.fls_rec) ]

/-- Translate a `(term, type)` pair from `Dependent.lean`.  Both are dbify-d
first so all `name`/`vlam`/`vfn` go away.  Also translates the dbtype of each
built-in constant so check-cert can look them up. -/
def translatePair (p : _root_.Term × _root_.Term) : BuilderM (Nat × Nat × List (Nat × Nat)) := do
  let t ← translateTerm (dbify [] p.1)
  let τ ← translateTerm (dbify [] p.2)
  let mut dbtypeIdxs : List (Nat × Nat) := []
  for (tag, c) in builtinConstants do
    let dbt := c.dbtype
    let idx ← translateTerm dbt
    dbtypeIdxs := dbtypeIdxs ++ [(tag, idx)]
  return (t, τ, dbtypeIdxs)

end Cert
