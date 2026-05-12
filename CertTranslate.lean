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

/-- Translator with opaque-theorem substitution: at every subterm, check
whether it `==` (BEq) one of the known theorem's body Terms.  If so, emit a
reference to that theorem's opaque leaf instead of recursing.  Each helper's
body is assumed *closed* (no free `name`s), so `dbify [] body` is independent
of the names list at the use site. -/
partial def translateTermK (known : List (_root_.Term × Nat))
    (t : _root_.Term) : BuilderM Nat := do
  match known.find? (·.1 == t) with
  | some (_, opaqueIdx) => return opaqueIdx
  | none =>
    match t with
    | _root_.Term.var x        => Cert.var x
    | _root_.Term.lam b        => do let b' ← translateTermK known b; Cert.lam b'
    | _root_.Term.app f φ a    => do
        let f' ← translateTermK known f
        let φ' ← translateTermK known φ
        let a' ← translateTermK known a
        Cert.app f' φ' a'
    | _root_.Term.typ u        => Cert.typ u
    | _root_.Term.fn α β       => do
        let α' ← translateTermK known α
        let β' ← translateTermK known β
        Cert.fn α' β'
    | _root_.Term.prod α β     => do
        let α' ← translateTermK known α
        let β' ← translateTermK known β
        Cert.prod α' β'
    | _root_.Term.pmk          => Cert.pmk
    | _root_.Term.prod_rec     => Cert.prodRec
    | _root_.Term.sum α β      => do
        let α' ← translateTermK known α
        let β' ← translateTermK known β
        Cert.sum α' β'
    | _root_.Term.inl          => Cert.inl
    | _root_.Term.inr          => Cert.inr
    | _root_.Term.sum_rec      => Cert.sumRec
    | _root_.Term.eq a a' α    => do
        let ea  ← translateTermK known a
        let ea' ← translateTermK known a'
        let eα  ← translateTermK known α
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

/-- Plain translator — equivalent to `translateTermK []`. -/
@[inline] def translateTerm (t : _root_.Term) : BuilderM Nat := translateTermK [] t

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

/-- Translate a `(term, type)` pair, treating each entry of `helpers` as an
opaque theorem.  `helpers` must be in dependency order: theorem #i may only
reference theorems #0..#(i-1) opaquely.

Each helper is registered via `opaqueTheorem` (whose body is verified by the
emitted assert before the main proof's assert runs).  The main proof is then
translated with all helpers visible — any subterm equal (BEq) to a helper's
dbify'd body is replaced by a reference to that helper's opaque leaf. -/
def translatePairWithTheorems
    (helpers : List (String × _root_.Term × _root_.Term))
    (p : _root_.Term × _root_.Term) :
    BuilderM (Nat × Nat × List (Nat × Nat)) := do
  let mut known : List (_root_.Term × Nat) := []
  for (hname, hbody, htype) in helpers do
    let dbBody := dbify [] hbody
    let dbType := dbify [] htype
    -- Capture for the closure.
    let curKnown := known
    let opaqueIdx ← opaqueTheorem hname
      (translateTermK curKnown dbBody)
      (translateTermK curKnown dbType)
    known := known ++ [(dbBody, opaqueIdx)]
  let t ← translateTermK known (dbify [] p.1)
  let τ ← translateTermK known (dbify [] p.2)
  let mut dbtypeIdxs : List (Nat × Nat) := []
  for (tag, c) in builtinConstants do
    let dbt := c.dbtype
    let idx ← translateTerm dbt
    dbtypeIdxs := dbtypeIdxs ++ [(tag, idx)]
  return (t, τ, dbtypeIdxs)

end Cert
