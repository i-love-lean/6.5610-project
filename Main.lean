import Std.Data.HashMap

-- A type checker for simply typed lambda calculus (equivalent to propositional logic)

/--
Types in our toy language

We use Greek letters for variables with type `Typ`
-/
inductive Typ
  /-- New named type -/
  | new : String → Typ
  /-- Function type -/
  | fn : Typ → Typ → Typ
  /-- Product type -/
  | prod : Typ → Typ → Typ
  /-- Sum type -/
  | sum : Typ → Typ → Typ
  /-- False (no terms of this type) -/
  | fls : Typ
deriving BEq

/-- Terms in our toy language -/
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

-- TODO: Convert `Term` into Lurk s-expression

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
  | _, _ => false

-- theorem false_empty (h : ∀ x, (_ : x ∈ env.keys) → env[x]'(by grind) != .fls) : check env .fls t == false := by
--   cases t <;> try grind [check]

/-- A → B → B ∧ A -/
def a_imp_b_imp_ba := (Typ.fn (.new "A") (.fn (.new "B") (.prod (.new "B") (.new "A"))), Term.lam "a" (.fn (.new "B") (.prod (.new "B") (.new "A")), .lam "b" (.prod (.new "B") (.new "A"), .and (.new "B", .var "b") (.new "A", .var "a"))))

#guard check (.ofList []) a_imp_b_imp_ba.1 a_imp_b_imp_ba.2

/-- A ∧ B → B ∧ A -/
def ab_imp_ba := (Typ.fn (.prod (.new "A") (.new "B")) (.prod (.new "B") (.new "A")), Term.lam "ab" (.prod (.new "B") (.new "A"), .and (.new "B", .and2 (.prod (.new "A") (.new "B"), .var "ab")) (.new "A", .and1 (.prod (.new "A") (.new "B"), .var "ab"))))

#guard check (.ofList []) ab_imp_ba.1 ab_imp_ba.2

/-- ¬(A ∨ B) → ¬A -/
def not_ab_imp_not_a := (Typ.fn (.fn (.sum (.new "A") (.new "B")) .fls) (.fn (.new "A") .fls), Term.lam "f" (.fn (.new "A") .fls, .lam "x" (.fls, .app (.fn (.sum (.new "A") (.new "B")) .fls, .var "f") (.sum (.new "A") (.new "B"), .or (.new "A", .var "x")))))

#guard check (.ofList []) not_ab_imp_not_a.1 not_ab_imp_not_a.2
