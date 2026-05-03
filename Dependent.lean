-- Trying to implement dependent types wheee

inductive Term
  -- Terms that cannot be types
  /-- Variable -/
  | var (x : Nat)
  /-- Lambda -/
  | lam (b β : Term)
  /-- Function application -/
  | app (f φ a α : Term)
  -- Types
  /-- New named type -/
  | new (x : Nat)
  /-- Dependent function type -/
  | fn (α β : Term)
  -- Inductive types
  /-- Dependent product type -/
  | prod (α β : Term)
  /-- Constructor for product -/
  | and (a α b β : Term)
  /-- Get first element of product -/
  | and1 (p π : Term)
  /-- Get second element of product -/
  | and2 (p π : Term)
  /-- Sum type -/
  | sum (α β : Term)
  /-- Construct a sum -/
  | or (c γ : Term)
  /-- Equality type -/
  | eq (a a' α : Term)
  /-- Constructor for equality -/
  | rfl (a α : Term)
  /-- Eliminator for equality -/
  | rw (a a' α f h ha : Term)
  /-- Natural number type -/
  | nat
  /-- Zero as a nat -/
  | zero
  /-- One or greater as a nat -/
  | succ (n ν : Term)
  /-- Eliminator for nats -/
  | nat_elim (α n ν b β f φ : Term)
  /-- False (no terms of this type) -/
  | fls
  /-- Eliminator for false -/
  | fls_elim (a α : Term)
  -- Universe stuff (only two universes for now)
  /-- Type of types -/
  | typ
deriving BEq, ReflBEq, LawfulBEq

/-- Increment free variables by 1 -/
def incr (d : Nat) : Term → Term
  | .var x =>
    .var (if d ≤ x then x + 1 else x)
  | .lam b β =>
    .lam (incr (d + 1) b) (incr (d + 1) β)
  | .app f φ a α =>
    .app (incr d f) (incr d φ) (incr d a) (incr d α)
  | .fn α β =>
    .fn (incr d α) (incr d β)
  | x => x

mutual
-- /-- -/
-- def defeq (env : List Term) a a' α :=
--   check env a α && check env a' α' && eval env a α == eval env a' α'

-- TODO: A lot of the `==`s here should use defeq
/-- Janky type checker -/
def check (env : List Term) : Term → Term → Bool
  | .var x, α =>
    if _ : x < env.length then env[x] == α else false
  | .lam b β, .fn α β' =>
    β' == β && (β == .typ || check (α :: env) β .typ) && check (α :: env) b β
  | .app f (.fn α β) a α', β' =>
    α' == α && β' == β && check env f (.fn α β) && check env a α
  | .new x, .typ =>
    true
  | .fn α β, .typ =>
    check env α .typ && check env β .typ
  | .prod α β, .typ =>
    check env α .typ && check env β .typ
  | .and a α b β, .prod α' β' =>
    α' == α && β' == β && (β == .typ || check (α :: env) β .typ) && check env a α && check env b β
  | .and1 p (.prod α β), α' =>
    α' == α && check env p (.prod α β)
  | .and2 p (.prod α β), β' =>
    β' == β && (β == .typ || check (α :: env) β .typ) && check env p (.prod α β)
  | .sum α β, .typ =>
    check env α .typ && check env β .typ
  | .or c γ, .sum α β =>
    (γ == α || γ == β) && check env c γ
  | .eq a a' α, .typ =>
    check env a α && check env a' α && check env α .typ
  | .rfl a α, .eq a' a'' α' =>
    α' == α && a' == a && a'' == a && check env a α
  | .rw a a' α m h ha, ha' =>
    -- TODO this needs eval for sure
    check env h (.eq a a' α) --&& check env ha (.app (.app m (.fn α (.fn (.eq ) .typ)) a α)) -- && check env ha' (.app p (.fn α .typ) a' α)
  | .nat, .typ | .zero, .nat =>
    true
  | .succ n .nat, .nat =>
    check env n .nat
  | .nat_elim α n .nat a α₁ f (.fn .nat (.fn α₂ α₃)), .fn .nat α₄ =>
    α₁ == α && α₂ == α && α₃ == α && α₄ == α && check env n .nat && check env a α && check env f (.fn .nat (.fn α α))
  | .fls, .typ =>
    true
  | .fls_elim a .fls, _ =>
    check env a .fls
  | _, _ =>
    false

end

/-- A → A -/
def a_imp_a := (Term.lam (.var 0) (.new 0), Term.fn (.new 0) (.new 0))

#guard check [] a_imp_a.1 a_imp_a.2

/-- A → B → B ∧ A -/
def a_imp_b_imp_ba := (Term.lam (.lam (.and (.var 0) (.new 1) (.var 1) (.new 0)) (.prod (.new 1) (.new 0))) (.fn (.new 1) (.prod (.new 1) (.new 0))), Term.fn (.new 0) (.fn (.new 1) (.prod (.new 1) (.new 0))))

#guard check [] a_imp_b_imp_ba.1 a_imp_b_imp_ba.2

/-- A ∧ B → B ∧ A -/
def ab_imp_ba := (Term.lam (.and (.and2 (.var 0) (.prod (.new 0) (.new 1))) (.new 1) (.and1 (.var 0) (.prod (.new 0) (.new 1))) (.new 0)) (.prod (.new 1) (.new 0)), Term.fn (.prod (.new 0) (.new 1)) (.prod (.new 1) (.new 0)))

#guard check [] ab_imp_ba.1 ab_imp_ba.2

/-- ¬(A ∨ B) → ¬A -/
def not_ab_imp_not_a := (Term.lam (.lam (.app (.var 1) (.fn (.sum (.new 0) (.new 1)) .fls) (.or (.var 0) (.new 0)) (.sum (.new 0) (.new 1))) (.fls)) (.fn (.new 0) .fls), Term.fn (.fn (.sum (.new 0) (.new 1)) .fls) (.fn (.new 0) .fls))

#guard check [] not_ab_imp_not_a.1 not_ab_imp_not_a.2

/-- A → ¬¬A -/
def a_imp_not_not_a := (Term.lam (.lam (.app (.var 0) (.fn (.new 0) .fls) (.var 1) (.new 0)) (.fls)) (.fn (.fn (.new 0) .fls) .fls), Term.fn (.new 0) (.fn (.fn (.new 0) .fls) .fls))

#guard check [] a_imp_not_not_a.1 a_imp_not_not_a.2

/-- ¬¬¬A → ¬A -/
def not_not_not_a_imp_not_a := (Term.lam (.lam (.app (.var 1) (.fn (.fn (.fn (.new 0) .fls) .fls) .fls) (.app a_imp_not_not_a.1 a_imp_not_not_a.2 (.var 0) (.new 0)) (.fn (.fn (.new 0) .fls) .fls)) (.fls)) (.fn (.new 0) .fls), Term.fn (.fn (.fn (.fn (.new 0) .fls) .fls) .fls) (.fn (.new 0) .fls))

#guard check [] not_not_not_a_imp_not_a.1 not_not_not_a_imp_not_a.2

/-- ∀ a : A, a = a -/
def a_eq_a := (Term.lam (.rfl (.var 0) (.new 0)) (.eq (.var 0) (.var 0) (.new 0)), Term.fn (.new 0) (.eq (.var 0) (.var 0) (.new 0)))

#guard check [] a_eq_a.1 a_eq_a.2

/-- 2 exists (yeah I know this is not super exciting) -/
def two := (Term.succ (.succ .zero .nat) .nat, Term.nat)

#guard check [] two.1 two.2

/-- 4 exists -/
def four := (Term.succ (.succ two.1 two.2) .nat, Term.nat)

#guard check [] four.1 four.2

/-- Addition -/
def add := (Term.lam (.nat_elim .nat .zero .nat (.var 0) .nat (.lam (.lam (.succ (.var 2) .nat) .nat) (.fn .nat .nat)) (.fn .nat (.fn .nat .nat))) (.fn .nat .nat), Term.fn .nat (.fn .nat .nat))

#guard check [] add.1 add.2

def two_plus_two := (Term.app (.app add.1 add.2 two.1 two.2) (.fn .nat .nat) two.1 two.2, Term.nat)

#guard check [] two_plus_two.1 two_plus_two.2

/-- 2 + 2 = 4 -/
def two_plus_two_eq_four := (Term.fls, Term.eq two_plus_two.1 four.1 .nat)

#guard check [] two_plus_two_eq_four.1 two_plus_two_eq_four.2
