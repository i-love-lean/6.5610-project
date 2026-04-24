import Std.Data.HashMap

-- A type checker for simply typed lambda calculus with a few inductive types

/--
Types in our toy language

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
deriving BEq

/--
Terms in our toy language

We hardcode all the inductive type constructors and eliminators here instead of implementing them separately as axioms (which would significantly simplify the type checker) to prevent adversies from writing fake proofs that use arbitrary axioms
-/
inductive Term
  /-- Variable -/
  | var : String → Term
  /-- Lambda -/
  | lam : String → Term × Typ → Term
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
  | .var x => s!"(list 10n '{x})"
  | .lam x b => s!"(list 11n '{x} {toString b})"
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
The type checker!

The variable names are chosen intentionally so that i.e. `a : Term` corresponds to `α : Typ`.
-/
def check (env : Std.HashMap String Typ) : Term → Typ → Bool
  | .var x, α =>
    (· == α) <$> env[x]? |>.getD false
  | .lam x (b, β), .fn α β' =>
    β' == β && check (env.insert x α) b β
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
  | .fls_elim (_, .fls), _ =>
    true
  | _, _ =>
    false

theorem false_empty : check (.ofList []) t .fls == false := by
  sorry

-- TODO: Implement eval so we can state 2 + 2 = 4

def a_imp_a := (Term.lam "a" (.var "a", .new 0), Typ.fn (.new 0) (.new 0))

#guard check (.ofList []) a_imp_a.1 a_imp_a.2

#eval IO.println a_imp_a

/-- A → B → B ∧ A -/
def a_imp_b_imp_ba := (Term.lam "a" (.lam "b" (.and (.var "b", .new 1) (.var "a", .new 0), .prod (.new 1) (.new 0)), .fn (.new 1) (.prod (.new 1) (.new 0))), Typ.fn (.new 0) (.fn (.new 1) (.prod (.new 1) (.new 0))))

#guard check (.ofList []) a_imp_b_imp_ba.1 a_imp_b_imp_ba.2

#eval IO.println a_imp_b_imp_ba

/-- A ∧ B → B ∧ A -/
def ab_imp_ba := (Term.lam "ab" (.and (.and2 (.var "ab", .prod (.new 0) (.new 1)), .new 1) (.and1 (.var "ab", .prod (.new 0) (.new 1)), .new 0), .prod (.new 1) (.new 0)), Typ.fn (.prod (.new 0) (.new 1)) (.prod (.new 1) (.new 0)))

#guard check (.ofList []) ab_imp_ba.1 ab_imp_ba.2

#eval IO.println ab_imp_ba

/-- ¬(A ∨ B) → ¬A -/
def not_ab_imp_not_a := (Term.lam "f" (.lam "a" (.app (.var "f", .fn (.sum (.new 0) (.new 1)) .fls) (.or (.var "a", .new 0), .sum (.new 0) (.new 1)), .fls), .fn (.new 0) .fls), Typ.fn (.fn (.sum (.new 0) (.new 1)) .fls) (.fn (.new 0) .fls))

#guard check (.ofList []) not_ab_imp_not_a.1 not_ab_imp_not_a.2

#eval IO.println not_ab_imp_not_a

/-- 2 exists (yeah I know this is not super exciting) -/
def two := (Term.succ ((.succ (.zero, .nat)), .nat), Typ.nat)

#guard check (.ofList []) two.1 two.2

/-- 4 exists -/
def four := (Term.succ (.succ two, .nat), Typ.nat)

#guard check (.ofList []) four.1 four.2

/-- Addition -/
def add := (Term.lam "a" (.nat_elim .nat (.zero, .nat) (.var "a", .nat) (.lam "_" (.lam "b" (.succ (.var "b", .nat), .nat), .fn .nat .nat), .fn .nat (.fn .nat .nat)), .fn .nat .nat), Typ.fn .nat (.fn .nat .nat))

#guard check (.ofList []) add.1 add.2

def two_plus_two := (Term.app (.app add two, .fn .nat .nat) two, Typ.nat)

#guard check (.ofList []) two_plus_two.1 two_plus_two.2
