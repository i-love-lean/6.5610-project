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
  | nat_elim : Typ → Typ × Term → Typ × Term → Term
  /-- Eliminator for false -/
  | fls_elim : Typ × Term → Term

def Typ.toString : Typ → String
  | new α => s!"(cons \"new\" \"{α}\")"
  | fn α β => s!"(list \"fn\" {α.toString} {β.toString})"
  | prod α β => s!"(list \"prod\" {α.toString} {β.toString})"
  | sum α β => s!"(list \"sum\" {α.toString} {β.toString})"
  | nat => s!"'(\"nat\")"
  | fls => s!"'(\"fls\")"

instance : ToString Typ := ⟨Typ.toString⟩

mutual
def toString (t : Typ × Term) := s!"(cons {t.1} {t.2.toString})"

def Term.toString : Term → String
  | .var x => s!"(cons \"var\" \"{x}\")"
  | .lam x b => s!"(list \"lam\" \"{x}\" {toString b})"
  | .app f x => s!"(list \"app\" {toString f} {toString x})"
  | .and x y => s!"(list \"and\" {toString x} {toString y})"
  | .and1 x => s!"(cons \"and1\" {toString x})"
  | .and2 y => s!"(cons \"and2\" {toString y})"
  | .or z => s!"(cons \"or\" {toString z})"
  | .zero => s!"'(\"zero\")"
  | .succ x => s!"(cons \"succ\" {toString x})"
  | .nat_elim τ a b => s!"(list \"nat_elim\" {τ} {toString a} {toString b})"
  | .fls_elim x => s!"(cons \"fls_elim\" {toString x})"
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
  | .fn .nat τ, .nat_elim α (β, a) (.fn γ δ, b) =>
    τ == α && τ == β && τ == γ && τ == δ && check env β a && check env (.fn γ δ) b
  | _, .fls_elim (.fls, _) =>
    true
  | _, _ =>
    false

/-- A → B → B ∧ A -/
def a_imp_b_imp_ba := (Typ.fn (.new "A") (.fn (.new "B") (.prod (.new "B") (.new "A"))), Term.lam "a" (.fn (.new "B") (.prod (.new "B") (.new "A")), .lam "b" (.prod (.new "B") (.new "A"), .and (.new "B", .var "b") (.new "A", .var "a"))))

#guard check (.ofList []) a_imp_b_imp_ba.1 a_imp_b_imp_ba.2

/-- A ∧ B → B ∧ A -/
def ab_imp_ba := (Typ.fn (.prod (.new "A") (.new "B")) (.prod (.new "B") (.new "A")), Term.lam "ab" (.prod (.new "B") (.new "A"), .and (.new "B", .and2 (.prod (.new "A") (.new "B"), .var "ab")) (.new "A", .and1 (.prod (.new "A") (.new "B"), .var "ab"))))

#guard check (.ofList []) ab_imp_ba.1 ab_imp_ba.2

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
def add := (Typ.fn .nat (.fn .nat .nat), Term.lam "a" (.fn .nat .nat, .nat_elim .nat (.nat, .var "a") (.fn .nat .nat, .lam "b" (.nat, .succ (.nat, .var "b")))))

#guard check (.ofList []) add.1 add.2

def two_plus_two := (Typ.nat, Term.app (.fn .nat .nat, .app add two) two)

#guard check (.ofList []) two_plus_two.1 two_plus_two.2
