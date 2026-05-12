import Cert

/-! # Proof definitions

Each proof is a `BuilderM (Nat × Nat)` returning the indices of (term, type)
in the shared term table.  Add new proofs here as we extend the verifier.
-/

namespace Cert

/-- `λα. λa. a : ∀α : 𝒰, α → α` — the trivial identity.
Exercises only `id`, `congLam`, `congFn`, and `var`/`lam`/`fn` in `check-cert`. -/
def buildAImpA : BuilderM (Nat × Nat) := do
  let u0  ← typ 0
  let v0  ← var 0
  let v1  ← var 1
  let innerFn ← fn v0 v1
  let typeIdx ← fn u0 innerFn
  let innerLam ← lam v0
  let termIdx ← lam innerLam
  return (termIdx, typeIdx)

/-- `λα f a. f (λg. g a) : ∀α, ¬¬¬α → ¬α`.  Exercises `congApp` (with the
sub-result witness) and the var/lam/fn machinery under several binders. -/
def buildTripleNeg : BuilderM (Nat × Nat) := do
  let u0  ← typ 0
  let bot ← fls
  let v0  ← var 0
  let v1  ← var 1
  let v2  ← var 2
  let v3  ← var 3
  let alphaBot   ← fn v0 bot
  let alphaBot2  ← fn alphaBot bot
  let alphaBot3  ← fn alphaBot2 bot
  let aType      ← fn v1 bot
  let fType      ← fn alphaBot3 aType
  let fullType   ← fn u0 fType
  let aType3      ← fn v2 bot
  let aType3Bot   ← fn aType3 bot
  let aType3Bot2  ← fn aType3Bot bot
  let gType       ← fn v3 bot
  let appG        ← app v0 gType v1
  let lamG        ← lam appG
  let appF        ← app v1 aType3Bot2 lamG
  let lamA        ← lam appF
  let lamF        ← lam lamA
  let lamAlpha    ← lam lamF
  return (lamAlpha, fullType)

/-- `λα. λa. λb. a : ∀α β : 𝒰, α → β → α` — the K combinator.
Exercises chained binders (env grows to 4 entries) and a deeper `var` lookup. -/
def buildK : BuilderM (Nat × Nat) := do
  let u0 ← typ 0
  let v0 ← var 0
  let v1 ← var 1
  let v2 ← var 2
  let v3 ← var 3
  -- Type: ∀α β, α → β → α    after dbify with [α, β]:
  --   fn 𝒰 (fn 𝒰 (fn (var 1) (fn (var 1) (var 3))))
  -- (under α: var 0 = α; under α,β: var 0 = β, var 1 = α; under α,β,a:
  --  var 0 = a, var 1 = β, var 2 = α; under α,β,a,b: var 1 = a, var 3 = α.)
  let inner3 ← fn v1 v3   -- b → α
  let inner2 ← fn v1 inner3
  let inner1 ← fn u0 inner2
  let typeIdx ← fn u0 inner1
  -- Term: λ. λ. λ. λ. var 1   (under α,β,a,b binders, var 1 = a)
  let lam0 ← lam v1
  let lam1 ← lam lam0
  let lam2 ← lam lam1
  let termIdx ← lam lam2
  return (termIdx, typeIdx)

/-- `λα. λa. λb. b : ∀α β : 𝒰, α → β → β` — sister of K.  Sanity check that
`var` lookup at index 0 works alongside index 1 from the previous test. -/
def buildKI : BuilderM (Nat × Nat) := do
  let u0 ← typ 0
  let v0 ← var 0
  let v1 ← var 1
  let v2 ← var 2
  -- Type: fn 𝒰 (fn 𝒰 (fn (var 1) (fn (var 1) (var 2))))
  -- (return β: under α,β,a,b binders β = var 2)
  let inner3 ← fn v1 v2   -- b → β
  let inner2 ← fn v1 inner3
  let inner1 ← fn u0 inner2
  let typeIdx ← fn u0 inner1
  -- Term: λ. λ. λ. λ. var 0
  let lam0 ← lam v0
  let lam1 ← lam lam0
  let lam2 ← lam lam1
  let termIdx ← lam lam2
  return (termIdx, typeIdx)

/-- `λα. λx. x : ⊥ → ⊥` — identity restricted to the empty type.  Stresses
the `fls` constructor showing up as both a binder type and a return type. -/
def buildIdFls : BuilderM (Nat × Nat) := do
  let bot ← fls
  let v0 ← var 0
  let typeIdx ← fn bot bot
  let lam0 ← lam v0
  return (lam0, typeIdx)

/-- Smoke test for `congProd` and `prod-vs-typ`.  Type-check the type
`prod ⊥ (λ_. ⊥)` against `𝒰` (term-idx and type-idx are the same node here
because we are asking the verifier to recognise the syntactic *type*). -/
def buildProdFlsType : BuilderM (Nat × Nat) := do
  let bot ← fls
  let lamBot ← lam bot
  let prodFls ← prod bot lamBot
  let u0 ← typ 0
  return (prodFls, u0)

/-- Smoke test for `congSum` and `sum-vs-typ`. -/
def buildSumFlsType : BuilderM (Nat × Nat) := do
  let bot ← fls
  let sumFls ← sum bot bot
  let u0 ← typ 0
  return (sumFls, u0)

/-- Smoke test for `congEq` and `eq-vs-typ`.  We need the equality's `α`
field to be a type, and the two LHS/RHS terms to have that type.  Pick
`α = ⊥`-as-a-type at `𝒰₁`, `a = a' = ⊥` (both inhabit `𝒰₁`). -/
def buildEqFlsType : BuilderM (Nat × Nat) := do
  let bot ← fls
  let u1 ← typ 1
  let eqIdx ← eq bot bot u1     -- eq ⊥ ⊥ 𝒰₁
  let u2 ← typ 2
  return (eqIdx, u2)

/-- Smoke test for `beta`: `(λα. α) 𝒰 : 𝒰₁`.  The lambda is the identity on
types, applied to `𝒰`; the eval reduces to `𝒰`, type is `𝒰₁`. -/
def buildBetaIdentity : BuilderM (Nat × Nat) := do
  let u0 ← typ 0
  let u1 ← typ 1
  let v0 ← var 0
  let lamId ← lam v0          -- λα. α
  let phi ← fn u1 u1          -- 𝒰₁ → 𝒰₁ (lamId's type)
  let appTerm ← app lamId phi u0   -- (λα. α) 𝒰
  return (appTerm, u1)

/-- Smoke test for `iotaSumL`. -/
def buildIotaSumLSmoke : BuilderM (Nat × Nat) := do
  let (term, typ_) ← buildAImpA
  let bot ← fls
  let sr ← sumRec
  let il ← inl
  let γ ← fn bot bot
  let γFn ← fn γ bot          -- (γ ⇨ _) — phi-of-(arg1 f')
  let phiPlaceholder ← fn bot bot
  let g ← intro
  -- f' = 5-deep sum_rec, with phi-of-arg1-f' = (γ ⇨ _) and arg3 = g.
  let l4 ← app sr phiPlaceholder bot
  let l3 ← app l4 phiPlaceholder bot
  let l2 ← app l3 phiPlaceholder bot
  let l1 ← app l2 γFn g
  let f5 ← app l1 phiPlaceholder bot
  -- a' = 3-deep inl with `a` at arg3 a'.
  let aVal ← intro
  let aL2 ← app il phiPlaceholder bot
  let aL1 ← app aL2 phiPlaceholder bot
  let a3 ← app aL1 phiPlaceholder aVal
  let _outer ← app f5 phiPlaceholder a3
  return (term, typ_)

/-- Smoke test for `iotaSumR`. -/
def buildIotaSumRSmoke : BuilderM (Nat × Nat) := do
  let (term, typ_) ← buildAImpA
  let bot ← fls
  let sr ← sumRec
  let ir ← inr
  let γ ← fn bot bot
  let γFn ← fn γ bot
  let phiPlaceholder ← fn bot bot
  let g ← intro
  -- f' = 5-deep sum_rec, with phi-of-f' = (γ ⇨ _) and arg3 = g.
  let l4 ← app sr phiPlaceholder bot
  let l3 ← app l4 phiPlaceholder bot
  let l2 ← app l3 phiPlaceholder bot
  let l1 ← app l2 phiPlaceholder bot
  let f5 ← app l1 γFn g
  -- a' = 3-deep inr with `b` at arg3 a'.
  let bVal ← intro
  let aL2 ← app ir phiPlaceholder bot
  let aL1 ← app aL2 phiPlaceholder bot
  let a3 ← app aL1 phiPlaceholder bVal
  let _outer ← app f5 phiPlaceholder a3
  return (term, typ_)

/-- Smoke test for `iotaProd`: build the iota-prod trigger
`app (prod_rec α β m g) phi (pmk α β a b)`. -/
def buildIotaProdSmoke : BuilderM (Nat × Nat) := do
  let (term, typ_) ← buildAImpA
  let bot ← fls
  let pr ← prodRec
  let pk ← pmk
  -- γ must be a fn type so the constructed outer's phi is fn.
  let γ ← fn bot bot
  let alphaFnGamma ← fn bot γ
  let phiOfFp ← fn alphaFnGamma bot
  let phiPlaceholder ← fn bot bot
  let g ← intro
  -- f' chain: 4-deep prod_rec
  let l3 ← app pr phiPlaceholder bot
  let l2 ← app l3 phiPlaceholder bot
  let l1 ← app l2 phiPlaceholder bot
  let f4 ← app l1 phiOfFp g
  -- a' chain: 4-deep pmk with `a` at arg3 of (arg1 a') and `b` at arg3 a'
  let aVal ← intro
  let bVal ← refl
  let aL3 ← app pk phiPlaceholder bot
  let aL2 ← app aL3 phiPlaceholder bot
  let aL1 ← app aL2 phiPlaceholder aVal
  let a4 ← app aL1 phiPlaceholder bVal
  let _outer ← app f4 phiPlaceholder a4
  return (term, typ_)

/-- Smoke test for `iotaNatS`: build the iota-nat-s trigger pattern `app
(nat_rec ... g) _ (succ ... n)`. -/
def buildIotaNatSSmoke : BuilderM (Nat × Nat) := do
  let (term, typ_) ← buildAImpA
  let bot ← fls
  let nr ← natRec
  let sc ← succ
  let nt ← nat
  -- We need phi-of-f' = ((nat ⇨ γ) ⇨ _) so the verifier can extract γ.
  -- γ must itself be a fn type so the constructed outer app's phi is a fn
  -- (otherwise evalM's cong-app would fail on the constructed outer).
  let γ ← fn bot bot                   -- γ = (⊥ → ⊥)
  let natFnGamma ← fn nt γ            -- (nat ⇨ γ)
  let phiOfFp ← fn natFnGamma bot     -- ((nat ⇨ γ) ⇨ _)
  -- f' chain: app(app(app(nat_rec, ⊥, ⊥), ⊥, ⊥), phiOfFp, g)
  let g ← intro                       -- placeholder g
  let phiPlaceholder ← fn bot bot
  let l2 ← app nr phiPlaceholder bot
  let l1 ← app l2 phiPlaceholder bot
  let f3 ← app l1 phiOfFp g
  -- a' chain: app(succ, (nat ⇨ nat), n)
  let n ← pmk                         -- placeholder n
  let natFnNat ← fn nt nt
  let a1 ← app sc natFnNat n
  -- The outer app whose eval triggers iota-nat-s.
  let _outer ← app f3 phiPlaceholder a1
  return (term, typ_)

/-- Smoke test for `iotaNatZ`: build the iota-nat-z trigger pattern `app
(app (app nat_rec _ z) _ _) _ zero` and let the eval rule fire.  Use
`a_imp_a` for the actual check assertion. -/
def buildIotaNatZSmoke : BuilderM (Nat × Nat) := do
  let (term, typ_) ← buildAImpA
  let bot ← fls
  let z ← intro                  -- placeholder z
  let nr ← natRec
  let zr ← zero
  let phiPlaceholder ← fn bot bot
  -- f' chain: app(app(app(nat_rec, ⊥, ⊥), ⊥, z), ⊥, ⊥)
  let l2 ← app nr phiPlaceholder bot
  let l1 ← app l2 phiPlaceholder z
  let f3 ← app l1 phiPlaceholder bot
  -- The outer app whose eval triggers iota-nat-z.
  let _outer ← app f3 phiPlaceholder zr
  return (term, typ_)

/-- Smoke test for `iotaEq`.  Builds the syntactic pattern that triggers the
iota-eq rule during eval — an `app f φ a` where `f` is a 5-deep app of
`eq_rec` and `a` is a 2-deep app of `refl` — using `⊥` and `𝒰`-valued
placeholders for the ignored type-positions.  We only need *eval* on this
node to fire `iotaEq`; the actual `check-cert` assertion uses a trivial
identity type-check (`a_imp_a`) so we don't have to construct a fully
well-typed `eq_rec` usage by hand. -/
def buildIotaEqSmoke : BuilderM (Nat × Nat) := do
  -- Trivial check target.
  let (term, typ_) ← buildAImpA
  -- Build the iota-eq trigger pattern.  We use `⊥` everywhere for types
  -- (it's `(21n)` — a leaf — so no validation cares about its shape) and
  -- `pmk` (`(6n)`) as the placeholder value `ha`.
  let bot ← fls
  let ha ← pmk                -- arbitrary placeholder for `ha`
  let er ← eqRec
  let rf ← refl
  let phiPlaceholder ← fn bot bot
  -- f' chain: app(app(app(app(app(eq_rec, ⊥, ⊥), ⊥, ⊥), ⊥, ⊥), ⊥, ha), ⊥, ⊥)
  let l4 ← app er phiPlaceholder bot
  let l3 ← app l4 phiPlaceholder bot
  let l2 ← app l3 phiPlaceholder bot
  let l1 ← app l2 phiPlaceholder ha    -- ha at arg3 of l1
  let f5 ← app l1 phiPlaceholder bot
  -- a' chain: app(app(refl, ⊥, ⊥), ⊥, ⊥)
  let r1 ← app rf phiPlaceholder bot
  let a2 ← app r1 phiPlaceholder bot
  -- The outer app whose eval triggers iota-eq.
  let _outer ← app f5 phiPlaceholder a2
  return (term, typ_)

/-! ## Intentionally bad proofs (for negative testing of `checkLean`) -/

/-- `lam (var 0)` claimed to have type `⊥`.  A lambda needs a function type;
this should be rejected by `checkLean`. -/
def buildBadLamFls : BuilderM (Nat × Nat) := do
  let bot ← fls
  let v0 ← var 0
  let lamId ← lam v0
  return (lamId, bot)

/-- `var 0` checked against `𝒰` in an env that says var 0 has type `⊥`.  The
type doesn't match, so this should be rejected. -/
def buildBadVarType : BuilderM (Nat × Nat) := do
  -- Ill-formed at top level (no env), but we wrap in a lam to give it env.
  -- λ_:⊥. (var 0) — claim type (⊥ → 𝒰).  Body's var 0 has type ⊥, not 𝒰.
  let bot ← fls
  let u0 ← typ 0
  let v0 ← var 0
  let lamBody ← lam v0
  let badType ← fn bot u0    -- ⊥ → 𝒰
  return (lamBody, badType)

end Cert
