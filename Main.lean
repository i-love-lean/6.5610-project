import Std.Data.HashMap

-- A type checker for simply typed lambda calculus with a few inductive types

/--
Types in our toy language

We use Greek letters for variables with type `Typ`

TODO: Equality
-/
inductive Typ
  /-- New named type -/
  | new : String → Typ
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

The other advantage of that approach is that it enables us to write an evaluator for this toy language, which admittedly isn't very useful
-/
inductive Term
  /-- Variable -/
  | var : String → Term
  /-- Lambda -/
  | lam : String → Typ × Term → Term
  /-- Function application -/
  | app : Typ × Term → Typ × Term → Term
  /-- Construct a product -/
  | and : Typ × Term → Typ × Term → Term
  /-- Get first element of product -/
  | and1 : Typ × Term → Term
  /-- Get second element of product -/
  | and2 : Typ × Term → Term
  /-- Construct a sum -/
  | or : Typ × Term → Term
  /-- Zero as a nat -/
  | zero : Term
  /-- One or greater as a nat -/
  | succ : Typ × Term → Term
  /-- Eliminator (recursor) for nats -/
  | nat_elim : Typ → Typ × Term → Typ × Term → Typ × Term → Term
  /-- Eliminator for false -/
  | fls_elim : Typ × Term → Term

def Typ.toString : Typ → String
  | new α => s!"(list 0n \"{α}\")"
  | fn α β => s!"(list 1n {α.toString} {β.toString})"
  | prod α β => s!"(list 2n {α.toString} {β.toString})"
  | sum α β => s!"(list 3n {α.toString} {β.toString})"
  | nat => s!"'(4n)"
  | fls => s!"'(5n)"

instance : ToString Typ := ⟨Typ.toString⟩

mutual
def toString (t : Typ × Term) := s!"(cons {t.1} {t.2.toString})"

def Term.toString : Term → String
  | .var x => s!"(list 10n '{x})"
  | .lam x b => s!"(list 11n '{x} {toString b})"
  | .app f x => s!"(list 12n {toString f} {toString x})"
  | .and x y => s!"(list 13n {toString x} {toString y})"
  | .and1 x => s!"(list 14n {toString x})"
  | .and2 y => s!"(list 15n {toString y})"
  | .or z => s!"(list 16n {toString z})"
  | .zero => s!"'(17n)"
  | .succ x => s!"(list 18n {toString x})"
  | .nat_elim τ a b c => s!"(list 19n {τ} {toString a} {toString b} {toString c})"
  | .fls_elim x => s!"(list 20n {toString x})"
end

instance : ToString (Typ × Term) := ⟨toString⟩

instance : ToString Term := ⟨Term.toString⟩

/--
The type checker!

TODO: Port to Lurk
-/
def check (env : Std.HashMap String Typ) : Typ → Term → Bool
  | τ, .var x =>
    (· == τ) <$> env[x]? |>.getD false
  | .fn α β, .lam x (β', b) =>
    β' == β && check (env.insert x α) β' b
  | τ, .app (.fn α β, f) (α', x) =>
    α' == α && β == τ && check env (.fn α β) f && check env α' x
  | .prod α β, .and (α', x) (β', y) =>
    α' == α && β' == β && check env α' x && check env β' y
  | τ, .and1 (.prod α β, x) =>
    τ == α && check env (.prod α β) x
  | τ, .and2 (.prod α β, y) =>
    τ == β && check env (.prod α β) y
  | .sum α β, .or (γ, z) =>
    (γ == α || γ == β) && check env γ z
  | .nat, .zero =>
    true
  | .nat, .succ (α, x) =>
    α == .nat && check env α x
  | .fn .nat τ, .nat_elim α (.nat, a) (β, b) (.fn .nat (.fn γ δ), c) =>
    τ == α && τ == β && τ == γ && τ == δ && check env .nat a && check env β b && check env (.fn .nat (.fn γ δ)) c
  | _, .fls_elim (.fls, _) =>
    true
  | _, _ =>
    false

theorem false_empty : check (.ofList []) .fls t == false := by
  sorry

-- TODO: Implement eval so we can state 2 + 2 = 4
-- def eval env (venv : Std.HashMap String Term) τ t (h : check env τ t) (henv : ∀ x, x ∈ env.keys → x ∈ venv.keys) : Term :=
--   match τ, t with
--   | _, .var x =>
--     venv[x]'(by sorry)
--   | .fn α β, .lam x (β', b) =>
--     .lam x (eval (env.insert x α) venv β b (by sorry) (by sorry))
--   | .app (.fn α β, f) (α', x) =>
--     eval

def a_imp_a := (Typ.fn (.new "A") (.new "A"), Term.lam "a" (.new "A", .var "a"))

#guard check (.ofList []) a_imp_a.1 a_imp_a.2

#eval IO.println a_imp_a

/-- A → B → B ∧ A -/
def a_imp_b_imp_ba := (Typ.fn (.new "A") (.fn (.new "B") (.prod (.new "B") (.new "A"))), Term.lam "a" (.fn (.new "B") (.prod (.new "B") (.new "A")), .lam "b" (.prod (.new "B") (.new "A"), .and (.new "B", .var "b") (.new "A", .var "a"))))

#guard check (.ofList []) a_imp_b_imp_ba.1 a_imp_b_imp_ba.2

#eval IO.println a_imp_b_imp_ba

/-- A ∧ B → B ∧ A -/
def ab_imp_ba := (Typ.fn (.prod (.new "A") (.new "B")) (.prod (.new "B") (.new "A")), Term.lam "ab" (.prod (.new "B") (.new "A"), .and (.new "B", .and2 (.prod (.new "A") (.new "B"), .var "ab")) (.new "A", .and1 (.prod (.new "A") (.new "B"), .var "ab"))))

#guard check (.ofList []) ab_imp_ba.1 ab_imp_ba.2

#eval IO.println ab_imp_ba

/-- ¬(A ∨ B) → ¬A -/
def not_ab_imp_not_a := (Typ.fn (.fn (.sum (.new "A") (.new "B")) .fls) (.fn (.new "A") .fls), Term.lam "f" (.fn (.new "A") .fls, .lam "x" (.fls, .app (.fn (.sum (.new "A") (.new "B")) .fls, .var "f") (.sum (.new "A") (.new "B"), .or (.new "A", .var "x")))))

#guard check (.ofList []) not_ab_imp_not_a.1 not_ab_imp_not_a.2

#eval IO.println not_ab_imp_not_a

/-- 2 exists (yeah I know this is not super exciting) -/
def two := (Typ.nat, Term.succ (.nat, (.succ (.nat, .zero))))

#guard check (.ofList []) two.1 two.2

/-- 4 exists -/
def four := (Typ.nat, Term.succ (.nat, (.succ two)))

#guard check (.ofList []) four.1 four.2

/-- Addition -/
def add := (Typ.fn .nat (.fn .nat .nat), Term.lam "a" (.fn .nat .nat, .nat_elim .nat (.nat, .zero) (.nat, .var "a") (.fn .nat (.fn .nat .nat), .lam "_" (.fn .nat .nat, .lam "b" (.nat, .succ (.nat, .var "b"))))))

#guard check (.ofList []) add.1 add.2

def two_plus_two := (Typ.nat, Term.app (.fn .nat .nat, .app add two) two)

#guard check (.ofList []) two_plus_two.1 two_plus_two.2
