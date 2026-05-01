-- A type checker for simply typed lambda calculus with a few inductive types

/--
Types in the μLean language

We use Greek letters for variables with type `Typ`

TODO: Equality
-/
inductive Typ
  /-- New named type -/
  | new : Nat → Typ
  /-- Function type -/
  | fn : Typ → Typ → Typ
  -- All types below are inductive
  /-- Product type -/
  | prod : Typ → Typ → Typ
  /-- Sum type -/
  | sum : Typ → Typ → Typ
  /-- Natural number type -/
  | nat : Typ
  /-- False (no terms of this type) -/
  | fls : Typ
deriving BEq, ReflBEq, LawfulBEq

/--
Terms in μLean

We hardcode all the inductive type constructors and eliminators here instead of implementing them separately as axioms (which would significantly simplify the type checker) to prevent adversies from writing fake proofs that use arbitrary axioms
-/
inductive Term
  /-- Variable -/
  | var : Nat → Term
  /-- Lambda -/
  | lam : Term × Typ → Term
  /-- Function application -/
  | app : Term × Typ → Term × Typ → Term
  /-- Construct a product -/
  | and : Term × Typ → Term × Typ → Term
  /-- Get first element of product -/
  | and1 : Term × Typ → Term
  /-- Get second element of product -/
  | and2 : Term × Typ → Term
  /-- Construct a sum -/
  | or : Term × Typ → Term
  /-- Zero as a nat -/
  | zero : Term
  /-- One or greater as a nat -/
  | succ : Term × Typ → Term
  /-- Eliminator (recursor) for nats -/
  | nat_elim : Typ → Term × Typ → Term × Typ → Term × Typ → Term
  /-- Eliminator for false -/
  | fls_elim : Term × Typ → Term

/-- Convert the Lean-based μLean syntax to the Lurk-based s-exp syntax -/
def Typ.toString : Typ → String
  | new α => s!"(list 0n {α}n)"
  | fn α β => s!"(list 1n {α.toString} {β.toString})"
  | prod α β => s!"(list 2n {α.toString} {β.toString})"
  | sum α β => s!"(list 3n {α.toString} {β.toString})"
  | nat => s!"'(4n)"
  | fls => s!"'(5n)"

instance : ToString Typ := ⟨Typ.toString⟩

mutual
def toString (t : Term × Typ) := s!"(cons {t.1.toString} {t.2})"

def Term.toString : Term → String
  | .var x => s!"(list 10n {x})"
  | .lam b => s!"(list 11n {toString b})"
  | .app f a => s!"(list 12n {toString f} {toString a})"
  | .and x y => s!"(list 13n {toString x} {toString y})"
  | .and1 x => s!"(list 14n {toString x})"
  | .and2 x => s!"(list 15n {toString x})"
  | .or z => s!"(list 16n {toString z})"
  | .zero => s!"'(17n)"
  | .succ n => s!"(list 18n {toString n})"
  | .nat_elim α n x f => s!"(list 19n {α} {toString n} {toString x} {toString f})"
  | .fls_elim x => s!"(list 20n {toString x})"
end

instance : ToString (Term × Typ) := ⟨toString⟩

instance : ToString Term := ⟨Term.toString⟩

/--
The μLean type checker!

The variable names are chosen intentionally so that i.e. `a : Term` corresponds to `α : Typ`.
-/
def check (env : List Typ) : Term → Typ → Bool
  | .var x, α =>
    if _ : x < env.length then env[x] == α else false
  | .lam (b, β), .fn α β' =>
    β' == β && check (.cons α env) b β
  | .app (f, .fn α β) (a, α'), β' =>
    α' == α && β' == β && check env f (.fn α β) && check env a α
  | .and (a, α) (b, β), .prod α' β' =>
    α' == α && β' == β && check env a α && check env b β
  | .and1 (x, .prod α β), α' =>
    α' == α && check env x (.prod α β)
  | .and2 (x, .prod α β), β' =>
    β' == β && check env x (.prod α β)
  | .or (c, γ), .sum α β =>
    (γ == α || γ == β) && check env c γ
  | .zero, .nat =>
    true
  | .succ (n, .nat), .nat =>
    check env n .nat
  | .nat_elim α (n, .nat) (b, β) (f, .fn .nat (.fn γ δ)), .fn .nat τ =>
    τ == α && τ == β && τ == γ && τ == δ && check env n .nat && check env b β && check env f (.fn .nat (.fn γ δ))
  | .fls_elim (x, .fls), _ =>
    check env x .fls
  | _, _ =>
    false

/-! ### Consistency proof

We give a denotational semantics: each `Typ` is interpreted as a Lean `Type`,
and every `check`-passing term gets a corresponding inhabitant. Since `Typ.fls`
is interpreted as `Empty`, no closed term can have type `fls`. -/

@[reducible]
def Typ.interp : Typ → Type
  | .new _   => Unit
  | .fn α β  => α.interp → β.interp
  | .prod α β => α.interp × β.interp
  | .sum α β => α.interp ⊕ β.interp
  | .nat     => Nat
  | .fls     => Empty

/-- Semantic environment: a heterogeneous list realising each `Typ` in `env`. -/
@[reducible]
def Env : List Typ → Type
  | []      => PUnit
  | α :: αs => α.interp × Env αs

def Env.get : {env : List Typ} → Env env → (i : Nat) → (h : i < env.length) → (env[i]'h).interp
  | _ :: _,  (v, _), 0,     _ => v
  | _ :: αs, (_, ρ), i + 1, h => Env.get (env := αs) ρ i (Nat.lt_of_succ_lt_succ h)

/-- Tactic shorthand: we hit an impossible `check` outcome; close the goal. -/
local syntax "absurdCheck" : tactic
local macro_rules | `(tactic| absurdCheck) => `(tactic| (simp [check] at *))

/-- Directly evaluate a `check`-passing term to a Lean value of its interpreted type.
This is the model construction: it shows STLC + these inductives is consistent. -/
def evalChk : (env : List Typ) → Env env → (t : Term) → (α : Typ) →
    check env t α = true → α.interp
  | env, ρ, .var x, α, h => by
      simp only [check] at h
      split at h
      · rename_i hx
        have heq : (env[x]'hx) = α := LawfulBEq.eq_of_beq h
        exact heq ▸ Env.get ρ x hx
      · exact absurd h Bool.false_ne_true
  | env, ρ, .lam (b, β), α, h => by
      cases α with
      | fn α' β' =>
        simp only [check, Bool.and_eq_true] at h
        obtain ⟨hβ, hb⟩ := h
        have e : β' = β := LawfulBEq.eq_of_beq hβ
        subst e
        exact fun (v : α'.interp) => evalChk (α' :: env) (v, ρ) b β' hb
      | new _ => absurdCheck
      | prod _ _ => absurdCheck
      | sum _ _ => absurdCheck
      | nat => absurdCheck
      | fls => absurdCheck
  | env, ρ, .app (f, φ) (a, α'), β'', h => by
      cases φ with
      | fn α β =>
        simp only [check, Bool.and_eq_true] at h
        obtain ⟨⟨⟨hα, hβ⟩, hf⟩, ha⟩ := h
        have e1 : α' = α := LawfulBEq.eq_of_beq hα
        have e2 : β'' = β := LawfulBEq.eq_of_beq hβ
        subst e1; subst e2
        exact evalChk env ρ f (.fn α' β'') hf (evalChk env ρ a α' ha)
      | new _ => absurdCheck
      | prod _ _ => absurdCheck
      | sum _ _ => absurdCheck
      | nat => absurdCheck
      | fls => absurdCheck
  | env, ρ, .and (a, α) (b, β), γ, h => by
      cases γ with
      | prod α' β' =>
        simp only [check, Bool.and_eq_true] at h
        obtain ⟨⟨⟨hα, hβ⟩, ha⟩, hb⟩ := h
        have e1 : α' = α := LawfulBEq.eq_of_beq hα
        have e2 : β' = β := LawfulBEq.eq_of_beq hβ
        subst e1; subst e2
        exact (evalChk env ρ a α' ha, evalChk env ρ b β' hb)
      | new _ => absurdCheck
      | fn _ _ => absurdCheck
      | sum _ _ => absurdCheck
      | nat => absurdCheck
      | fls => absurdCheck
  | env, ρ, .and1 (x, π), α', h => by
      cases π with
      | prod α β =>
        simp only [check, Bool.and_eq_true] at h
        obtain ⟨hα, hx⟩ := h
        have e1 : α' = α := LawfulBEq.eq_of_beq hα
        subst e1
        exact (evalChk env ρ x (.prod α' β) hx).1
      | new _ => absurdCheck
      | fn _ _ => absurdCheck
      | sum _ _ => absurdCheck
      | nat => absurdCheck
      | fls => absurdCheck
  | env, ρ, .and2 (x, π), β', h => by
      cases π with
      | prod α β =>
        simp only [check, Bool.and_eq_true] at h
        obtain ⟨hβ, hx⟩ := h
        have e1 : β' = β := LawfulBEq.eq_of_beq hβ
        subst e1
        exact (evalChk env ρ x (.prod α β') hx).2
      | new _ => absurdCheck
      | fn _ _ => absurdCheck
      | sum _ _ => absurdCheck
      | nat => absurdCheck
      | fls => absurdCheck
  | env, ρ, .or (c, γ), σ, h => by
      cases σ with
      | sum α β =>
        simp only [check, Bool.and_eq_true, Bool.or_eq_true] at h
        obtain ⟨hor, hc⟩ := h
        by_cases hα : (γ == α) = true
        · have e : γ = α := LawfulBEq.eq_of_beq hα
          subst e
          exact (Sum.inl (evalChk env ρ c γ hc) : (γ.sum β).interp)
        · have hβ : (γ == β) = true := hor.resolve_left hα
          have e : γ = β := LawfulBEq.eq_of_beq hβ
          subst e
          exact (Sum.inr (evalChk env ρ c γ hc) : (α.sum γ).interp)
      | new _ => absurdCheck
      | fn _ _ => absurdCheck
      | prod _ _ => absurdCheck
      | nat => absurdCheck
      | fls => absurdCheck
  | _, _, .zero, α, h => by
      cases α with
      | nat => exact (0 : Nat)
      | new _ => absrdCheck
      | fn _ _ => absurdCheck
      | prod _ _ => absurdCheck
      | sum _ _ => absurdCheck
      | fls => absurdCheck
  | env, ρ, .succ (n, ν), α, h => by
      cases ν with
      | nat =>
        cases α with
        | nat =>
          simp only [check] at h
          exact ((evalChk env ρ n .nat h) + 1 : Nat)
        | new _ => absurdCheck
        | fn _ _ => absurdCheck
        | prod _ _ => absurdCheck
        | sum _ _ => absurdCheck
        | fls => absurdCheck
      | new _ => absurdCheck
      | fn _ _ => absurdCheck
      | prod _ _ => absurdCheck
      | sum _ _ => absurdCheck
      | fls => absurdCheck
  | env, ρ, .nat_elim μ (n, ν) (b, β) (f, φ), σ, h => by
      -- The lone "successful" path: ν=nat, φ=fn nat (fn γ δ), σ=fn nat σ2.
      -- Try every other combination → absurdCheck.
      cases ν with
      | nat =>
        cases φ with
        | fn φ1 φ2 =>
          cases φ1 with
          | nat =>
            cases φ2 with
            | fn γ δ =>
              cases σ with
              | fn σ1 σ2 =>
                cases σ1 with
                | nat =>
                  simp only [check, Bool.and_eq_true] at h
                  obtain ⟨⟨⟨⟨⟨⟨hμ, hβ⟩, hγ⟩, hδ⟩, hn⟩, hb⟩, hf⟩ := h
                  have eμ : σ2 = μ := LawfulBEq.eq_of_beq hμ
                  have eβ : σ2 = β := LawfulBEq.eq_of_beq hβ
                  have eγ : σ2 = γ := LawfulBEq.eq_of_beq hγ
                  have eδ : σ2 = δ := LawfulBEq.eq_of_beq hδ
                  subst eμ; subst eβ; subst eγ; subst eδ
                  exact fun (m : Nat) =>
                    Nat.rec
                      (motive := fun _ => σ2.interp)
                      (evalChk env ρ b σ2 hb)
                      (fun k r => evalChk env ρ f (.fn .nat (.fn σ2 σ2)) hf k r)
                      m
                | new _ => absurdCheck
                | fn _ _ => absurdCheck
                | prod _ _ => absurdCheck
                | sum _ _ => absurdCheck
                | fls => absurdCheck
              | new _ => absurdCheck
              | prod _ _ => absurdCheck
              | sum _ _ => absurdCheck
              | nat => absurdCheck
              | fls => absurdCheck
            | new _ => absurdCheck
            | prod _ _ => absurdCheck
            | sum _ _ => absurdCheck
            | nat => absurdCheck
            | fls => absurdCheck
          | new _ => absurdCheck
          | fn _ _ => absurdCheck
          | prod _ _ => absurdCheck
          | sum _ _ => absurdCheck
          | fls => absurdCheck
        | new _ => absurdCheck
        | prod _ _ => absurdCheck
        | sum _ _ => absurdCheck
        | nat => absurdCheck
        | fls => absurdCheck
      | new _ => absurdCheck
      | fn _ _ => absurdCheck
      | prod _ _ => absurdCheck
      | sum _ _ => absurdCheck
      | fls => absurdCheck
  | env, ρ, .fls_elim (x, ξ), α, h => by
      cases ξ with
      | fls =>
        simp only [check] at h
        exact (evalChk env ρ x .fls h).elim
      | new _ => absurdCheck
      | fn _ _ => absurdCheck
      | prod _ _ => absurdCheck
      | sum _ _ => absurdCheck
      | nat => absurdCheck
termination_by env _ t _ _ => sizeOf t
decreasing_by all_goals (simp_wf; omega)

/-- The headline: no closed term has type `fls`. -/
theorem false_empty : ∀ {t : Term}, check [] t .fls = false := by
  intro t
  cases hb : check [] t .fls with
  | false => rfl
  | true  => exact (evalChk [] PUnit.unit t .fls hb).elim

-- TODO: Implement eval so we can state 2 + 2 = 4

def a_imp_a := (Term.lam (.var 0, .new 0), Typ.fn (.new 0) (.new 0))

#guard check [] a_imp_a.1 a_imp_a.2

#eval IO.println a_imp_a

/-- A → B → B ∧ A -/
def a_imp_b_imp_ba := (Term.lam (.lam (.and (.var 0, .new 1) (.var 1, .new 0), .prod (.new 1) (.new 0)), .fn (.new 1) (.prod (.new 1) (.new 0))), Typ.fn (.new 0) (.fn (.new 1) (.prod (.new 1) (.new 0))))

#guard check [] a_imp_b_imp_ba.1 a_imp_b_imp_ba.2

#eval IO.println a_imp_b_imp_ba

/-- A ∧ B → B ∧ A -/
def ab_imp_ba := (Term.lam (.and (.and2 (.var 0, .prod (.new 0) (.new 1)), .new 1) (.and1 (.var 0, .prod (.new 0) (.new 1)), .new 0), .prod (.new 1) (.new 0)), Typ.fn (.prod (.new 0) (.new 1)) (.prod (.new 1) (.new 0)))

#guard check [] ab_imp_ba.1 ab_imp_ba.2

#eval IO.println ab_imp_ba

/-- ¬(A ∨ B) → ¬A -/
def not_ab_imp_not_a := (Term.lam (.lam (.app (.var 1, .fn (.sum (.new 0) (.new 1)) .fls) (.or (.var 0, .new 0), .sum (.new 0) (.new 1)), .fls), .fn (.new 0) .fls), Typ.fn (.fn (.sum (.new 0) (.new 1)) .fls) (.fn (.new 0) .fls))

#guard check [] not_ab_imp_not_a.1 not_ab_imp_not_a.2

#eval IO.println not_ab_imp_not_a

/-- A → ¬¬A -/
def a_imp_not_not_a := (Term.lam (.lam (.app (.var 0, .fn (.new 0) .fls) (.var 1, .new 0), .fls), .fn (.fn (.new 0) .fls) .fls), Typ.fn (.new 0) (.fn (.fn (.new 0) .fls) .fls))

#guard check [] a_imp_not_not_a.1 a_imp_not_not_a.2

#eval IO.println a_imp_not_not_a

/-- ¬¬¬A → ¬A -/
def not_not_not_a_imp_not_a := (Term.lam (.lam (.app (.var 1, .fn (.fn (.fn (.new 0) .fls) .fls) .fls) (.app a_imp_not_not_a (.var 0, .new 0), .fn (.fn (.new 0) .fls) .fls), .fls), .fn (.new 0) .fls), Typ.fn (.fn (.fn (.fn (.new 0) .fls) .fls) .fls) (.fn (.new 0) .fls))

#guard check [] not_not_not_a_imp_not_a.1 not_not_not_a_imp_not_a.2

#eval IO.println not_not_not_a_imp_not_a

/-- 2 exists (yeah I know this is not super exciting) -/
def two := (Term.succ ((.succ (.zero, .nat)), .nat), Typ.nat)

#guard check [] two.1 two.2

/-- 4 exists -/
def four := (Term.succ (.succ two, .nat), Typ.nat)

#guard check [] four.1 four.2

/-- Addition -/
def add := (Term.lam (.nat_elim .nat (.zero, .nat) (.var 0, .nat) (.lam (.lam (.succ (.var 2, .nat), .nat), .fn .nat .nat), .fn .nat (.fn .nat .nat)), .fn .nat .nat), Typ.fn .nat (.fn .nat .nat))

#guard check [] add.1 add.2

def two_plus_two := (Term.app (.app add two, .fn .nat .nat) two, Typ.nat)

#guard check [] two_plus_two.1 two_plus_two.2
