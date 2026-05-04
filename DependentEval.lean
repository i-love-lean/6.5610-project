-- μLean, a very simple proof assistant with dependent types and polymorphism!

inductive Term
  -- The basic stuff
  /-- Variable with de Bruijn index -/
  | var (x : Nat)
  /-- Lambda -/
  | lam (b β : Term)
  /-- Function application -/
  | app (f φ a α : Term)
  -- Types
  /-- Type of types -/
  | typ
  /-- New named type -/
  | new (x : Nat)
  /-- Dependent function type -/
  | fn (α β : Term)
  -- Inductive types
  /-- Dependent product type -/
  | prod (α β : Term)
  /-- Constructor for product -/
  | and
  /-- Get first element of product -/
  | fst
  /-- Get second element of product -/
  | snd
  /-- Sum type -/
  | sum (α β : Term)
  /-- Construct a sum using left type -/
  | inl
  /-- Construct a sum using right type -/
  | inr
  /-- Equality type -/
  | eq (a a' α : Term)
  /-- Constructor for equality -/
  | rfl
  /-- Recursor for equality -/
  | eq_rec
  /-- Natural number type -/
  | nat
  /-- Zero as a nat -/
  | zero
  /-- One or greater as a nat -/
  | succ
  /-- Recursor for nats -/
  | nat_rec
  /-- False (empty type) -/
  | fls
  /-- Recursor for false -/
  | fls_rec
deriving BEq, ReflBEq, LawfulBEq

-- `infixr` doesn't work at compile time or something
notation l " ⇨ " r => Term.fn l r -- \he
-- `max` fixes some precedence issues when parsing
notation "λ " b:max β:max => Term.lam b β -- \fu
notation:max "’" r:max => Term.var r -- \rq
notation:max "₸" r:max => Term.new r -- \te
notation "𝒰" => Term.typ -- \McU
notation "⊥" => Term.fls -- \bo
notation "ℕ" => Term.nat -- \N

/-- Increment free variables by 1 -/
def incr (d : Nat) : Term → Term
  | ’x =>
    ’(if d ≤ x then x + 1 else x)
  | (λ b β) => -- Need parentheses to avoid parsing as a Lean lambda
    λ (incr (d + 1) b) (incr (d + 1) β)
  | .app f φ a α =>
    .app (incr d f) (incr d φ) (incr d a) (incr d α)
  | α ⇨ β =>
    incr d α ⇨ incr (d + 1) β
  | .prod α β =>
    .prod (incr d α) (incr (d + 1) β)
  | .sum α β =>
    .sum (incr d α) (incr d β)
  | .eq a a' α =>
    .eq (incr d a) (incr d a') (incr d α)
  | x => x

/-- Substitute `s` at index `n` in a term -/
def sub (n : Nat) (s : Term) : Term → Term
  | ’x =>
    if x == n then s else ’(if n < x then x - 1 else x)
  | (λ b β) =>
    λ (sub (n + 1) (incr 0 s) b) (sub (n + 1) (incr 0 s) β)
  | .app f φ a α =>
    .app (sub n s f) (sub n s φ) (sub n s a) (sub n s α)
  | α ⇨ β =>
    sub n s α ⇨ sub (n + 1) (incr 0 s) β
  | .prod α β =>
    .prod (sub n s α) (sub (n + 1) (incr 0 s) β)
  | .sum α β =>
    .sum (sub n s α) (sub n s β)
  | .eq a a' α =>
    .eq (sub n s a) (sub n s a') (sub n s α)
  | x => x

/-- Convenience wrapper around .app with currying -/
def app (f : Term) : Term → List Term → Term
  -- Need to eval both these guys?
  -- Probably need to `incr 0 <$> xs`? Actually no
  | α ⇨ β, x :: xs => app (.app f (α ⇨ β) x α) (sub 0 x β) xs
  | _, _ => f

def clean := 𝒰 ⇨ ’0 ⇨ (’1 ⇨ .eq ’1 ’0 ’2 ⇨ 𝒰) ⇨ app ’0 (’2 ⇨ .eq ’2 ’0 ’3 ⇨ 𝒰) [’1, app .rfl (𝒰 ⇨ ’0 ⇨ .eq ’0 ’0 ’1) [’2, ’2]] ⇨ ’3 ⇨ .eq ’3 ’0 ’4 ⇨ app ’3 (’5 ⇨ .eq ’5 ’0 ’6 ⇨ 𝒰) [’1, ’0]

#reduce clean
#reduce 𝒰 ⇨ ’0 ⇨ (’1 ⇨ .eq ’1 ’0 ’2 ⇨ 𝒰) ⇨ .app (.app ’0 (’2 ⇨ .eq ’2 ’0 ’3 ⇨ 𝒰) ’1 ’2) (.eq ’1 ’1 ’2 ⇨ 𝒰) (.app (.app .rfl (𝒰 ⇨ ’0 ⇨ .eq ’0 ’0 ’1) ’2 𝒰) (’2 ⇨ .eq ’0 ’0 ’3) ’2 ’3) (.eq ’1 ’1 ’2) ⇨ ’3 ⇨ .eq ’3 ’0 ’4 ⇨ .app (.app ’3 (’5 ⇨ .eq ’5 ’0 ’6 ⇨ 𝒰) ’1 ’5) (.eq ’4 ’1 ’5) ’0 (.eq ’4 ’1 ’5)

-- /-- -/
-- def defeq (env : List Term) a a' α :=
--   check env a α && check env a' α' && eval env a α == eval env a' α'

-- TODO: A lot of the `==`s here should use defeq
/-- Janky type checker -/
def check (env : List Term) : Term → Term → Bool
  | ’x, α =>
    if _ : x < env.length then env[x] == α else false
  | λ b β, α ⇨ β' =>
    β' == β && (β == 𝒰 || check (incr 0 <$> (α :: env)) β 𝒰) && check (incr 0 <$> (α :: env)) b β
  | .app f (α ⇨ β) a α', β' =>
    α' == α && β' == sub 0 a β && check env f (α ⇨ β) && check env a α
  | .new _, 𝒰
  | .nat, 𝒰
  | ⊥, 𝒰 =>
    true
  | α ⇨ β, 𝒰 =>
    check env α 𝒰 && check (incr 0 <$> (α :: env)) β 𝒰
  | .prod α β, 𝒰
  | .sum α β, 𝒰 =>
    check env α 𝒰 && check env β 𝒰
  | .eq a a' α, 𝒰 =>
    check env a α && check env a' α && check env α 𝒰
  | .and, 𝒰 ⇨ 𝒰 ⇨ ’1 ⇨ ’1 ⇨ .prod ’3 ’3
  | .fst, 𝒰 ⇨ 𝒰 ⇨ .prod ’1 ’1 ⇨ ’2
  | .snd, 𝒰 ⇨ 𝒰 ⇨ .prod ’1 ’1 ⇨ ’1
  | .inl, 𝒰 ⇨ 𝒰 ⇨ ’1 ⇨ .sum ’2 ’1
  | .inr, 𝒰 ⇨ 𝒰 ⇨ ’0 ⇨ .sum ’2 ’1
  | .rfl, 𝒰 ⇨ ’0 ⇨ .eq ’0 ’0 ’1
  | .eq_rec, 𝒰 ⇨ ’0 ⇨ (’1 ⇨ .eq ’1 ’0 ’2 ⇨ 𝒰) ⇨ .app (.app ’0 (’2 ⇨ .eq ’2 ’0 ’3 ⇨ 𝒰) ’1 ’2) (.eq ’1 ’1 ’2 ⇨ 𝒰) (.app (.app .rfl (𝒰 ⇨ ’0 ⇨ .eq ’0 ’0 ’1) ’2 𝒰) (’2 ⇨ .eq ’0 ’0 ’3) ’2 ’3) (.eq ’1 ’1 ’2) ⇨ ’3 ⇨ .eq ’3 ’0 ’4 ⇨ .app (.app ’3 (’5 ⇨ .eq ’5 ’0 ’6 ⇨ 𝒰) ’1 ’5) (.eq ’4 ’1 ’5) ’0 (.eq ’4 ’1 ’5)
  | .nat_rec, (ℕ ⇨ 𝒰) ⇨ .app ’0 (ℕ ⇨ 𝒰) .zero ℕ ⇨ (ℕ ⇨ .app ’2 (ℕ ⇨ 𝒰) ’0 ℕ ⇨ .app ’3 (ℕ ⇨ 𝒰) (.app .succ (ℕ ⇨ ℕ) ’1 ℕ) ℕ) ⇨ ℕ ⇨ .app ’0 ℕ ’3 (ℕ ⇨ 𝒰)
  | .zero, ℕ
  | .succ, ℕ ⇨ ℕ
  | .fls_rec, ⊥ ⇨ _ =>
    true
  | _, _ =>
    false

/-- `t` should be well-typed or bad things will happen! -/
partial def eval (t : Term) :=
  match t with
  | (λ b β) =>
    λ (eval b) (eval β)
  | .app (.app (.app .fst _ _ _) _ _ _) _ (.app (.app (.app (.app .and _ _ _) _ _ _) _ a _) _ _ _) _ =>
    eval a
  | .app (.app (.app .snd _ _ _) _ _ _) _ (.app (.app (.app (.app .and _ _ _) _ _ _) _ _ _) _ b _) _ =>
    eval b
  | .app (.app (.app (.app .nat_rec τ₁ m τ₂) τ₃ z ℕ) τ₄ f φ) τ₅ n ℕ =>
    match n with
    | .zero => eval z
    | .app .succ (ℕ ⇨ ℕ) n' ℕ => eval (.app (.app f φ n ℕ) (.app m τ₂ n' ℕ ⇨ .app m τ₂ n ℕ) (.app (.app (.app (.app .nat_rec τ₁ m τ₂) τ₃ z ℕ) τ₄ f φ) τ₅ n' ℕ) (.app m τ₂ n ℕ))
    | _ => t
  | .app f φ a α =>
    let a' := eval a
    match eval f with
    | (λ b _) => eval (sub 0 (incr 0 a') b)
    | x => .app x φ a' α
  | α ⇨ β =>
    eval α ⇨ eval β
  | .prod α β =>
    .prod (eval α) (eval β)
  | .sum α β =>
    .sum (eval α) (eval β)
  | .eq a a' α =>
    .eq (eval a) (eval a') (eval α)
  -- eq_rec
  | x =>
    x

/-- A → A -/
def a_imp_a := (λ ’0 ₸0, ₸0 ⇨ ₸0)

#guard check [] a_imp_a.1 a_imp_a.2

/-- ∀ A : 𝒰, A → A -/
def a_imp_a' := (λ (λ ’0 ’1) (’0 ⇨ ’1), 𝒰 ⇨ ’0 ⇨ ’1)

#guard check [] a_imp_a'.1 a_imp_a'.2

/-- A → B → A ∧ B -/
def a_imp_b_imp_ab := (app .and (𝒰 ⇨ 𝒰 ⇨ ’1 ⇨ ’1 ⇨ .prod ’3 ’3) [₸0, ₸1], ₸0 ⇨ ₸1 ⇨ .prod ₸0 ₸1)

#guard check [] a_imp_b_imp_ab.1 a_imp_b_imp_ab.2

/-- Convenience wrapper around `.and` -/
def and a α b β := app .and (𝒰 ⇨ 𝒰 ⇨ ’1 ⇨ ’1 ⇨ .prod ’3 ’3) [α, β, a, b]

/-- A → B → B ∧ A -/
def a_imp_b_imp_ba := (λ (λ (and ’0 ₸1 ’1 ₸0) (.prod ₸1 ₸0)) (₸1 ⇨ .prod ₸1 ₸0), ₸0 ⇨ ₸1 ⇨ .prod ₸1 ₸0)

#guard check [] a_imp_b_imp_ba.1 a_imp_b_imp_ba.2

/-- Convenience wrapper around `.fst` -/
def fst α β p := app .fst (𝒰 ⇨ 𝒰 ⇨ .prod ’1 ’1 ⇨ ’2) [α, β, p]

/-- Convenience wrapper around `.snd` -/
def snd α β p := app .snd (𝒰 ⇨ 𝒰 ⇨ .prod ’1 ’1 ⇨ ’1) [α, β, p]

/-- A ∧ B → B ∧ A -/
def ab_imp_ba := (λ (and (snd ₸0 ₸1 ’0) ₸1 (fst ₸0 ₸1 ’0) ₸0) (.prod ₸1 ₸0), .prod ₸0 ₸1 ⇨ .prod ₸1 ₸0)

#guard check [] ab_imp_ba.1 ab_imp_ba.2

/-- Convenience wrapper around `.inl` -/
def inl α β a := app .inl (𝒰 ⇨ 𝒰 ⇨ ’1 ⇨ .sum ’2 ’1) [α, β, a]

/-- ¬(A ∨ B) → ¬A -/
def not_ab_imp_not_a := (λ (λ (app ’1 (.sum ₸0 ₸1 ⇨ ⊥) [inl ₸0 ₸1 ’0]) ⊥) (₸0 ⇨ ⊥), (.sum ₸0 ₸1 ⇨ ⊥) ⇨ ₸0 ⇨ ⊥)

#guard check [] not_ab_imp_not_a.1 not_ab_imp_not_a.2

/-- A → ¬¬A -/
def a_imp_not_not_a := (λ (λ (app ’0 (₸0 ⇨ ⊥) [’1]) ⊥) ((₸0 ⇨ ⊥) ⇨ ⊥), ₸0 ⇨ (₸0 ⇨ ⊥) ⇨ ⊥)

#guard check [] a_imp_not_not_a.1 a_imp_not_not_a.2

/-- ¬¬¬A → ¬A -/
def not_not_not_a_imp_not_a := (λ (λ (app ’1 (((₸0 ⇨ ⊥) ⇨ ⊥) ⇨ ⊥) [app a_imp_not_not_a.1 a_imp_not_not_a.2 [’0]]) ⊥) (₸0 ⇨ ⊥), (((₸0 ⇨ ⊥) ⇨ ⊥) ⇨ ⊥) ⇨ ₸0 ⇨ ⊥)

#guard check [] not_not_not_a_imp_not_a.1 not_not_not_a_imp_not_a.2

/-- Convenience wrapper around `.rfl` -/
def rfl' a α := app .rfl (𝒰 ⇨ ’0 ⇨ .eq ’0 ’0 ’1) [α, a]

/-- ∀ a : A, a = a -/
def a_eq_a := (λ (rfl' ’0 ₸0) (.eq ’0 ’0 ₸0), ₸0 ⇨ .eq ’0 ’0 ₸0)

#guard check [] a_eq_a.1 a_eq_a.2

/-- Convenience wrapper around `.succ` -/
def succ n := app .succ (ℕ ⇨ ℕ) [n]

-- /-- 2 exists (yeah I know this is not super exciting) -/
def two := (succ (succ .zero), ℕ)

#guard check [] two.1 two.2

/-- 4 exists -/
def four := (succ (succ two.1), ℕ)

#guard check [] four.1 four.2

#check Nat.rec

/-- `.nat_rec` where the motive always returns `ℕ` -/
def nat_rec_nat z f := Term.app (.app (.app .nat_rec ((ℕ ⇨ 𝒰) ⇨ .app ’0 (ℕ ⇨ 𝒰) .zero ℕ ⇨ (ℕ ⇨ .app ’2 (ℕ ⇨ 𝒰) ’0 ℕ ⇨ .app ’3 (ℕ ⇨ 𝒰) (.app .succ (ℕ ⇨ ℕ) ’1 ℕ) ℕ) ⇨ ℕ ⇨ .app ’0 ℕ ’3 (ℕ ⇨ 𝒰)) (λ ℕ 𝒰) (ℕ ⇨ 𝒰)) (ℕ ⇨ (ℕ ⇨ ℕ ⇨ ℕ) ⇨ ℕ ⇨ ℕ) z ℕ) ((ℕ ⇨ ℕ ⇨ ℕ) ⇨ ℕ ⇨ ℕ) f (ℕ ⇨ ℕ ⇨ ℕ)

#eval nat_rec_nat ₸0 ₸1

def nat_rec_nat' z f := app .nat_rec ((ℕ ⇨ 𝒰) ⇨ .app ’0 (ℕ ⇨ 𝒰) .zero ℕ ⇨ (ℕ ⇨ .app ’2 (ℕ ⇨ 𝒰) ’0 ℕ ⇨ .app ’3 (ℕ ⇨ 𝒰) (.app .succ (ℕ ⇨ ℕ) ’1 ℕ) ℕ) ⇨ ℕ ⇨ .app ’0 ℕ ’3 (ℕ ⇨ 𝒰)) [λ ℕ 𝒰, z, f]

#eval nat_rec_nat' ₸0 ₸1

#check Nat.rec

/-- Addition -/
def add := (λ (nat_rec_nat ’0 (λ (λ (succ ’0) (ℕ ⇨ ℕ)) ℕ)) (ℕ ⇨ ℕ), ℕ ⇨ ℕ ⇨ ℕ)

#guard check [] add.1 add.2

def zero_plus_zero := app add.1 add.2 [.zero, .zero]

#eval eval (eval zero_plus_zero)

def zero_plus_one := app add.1 add.2 [.zero, succ .zero]

#eval eval (eval zero_plus_one)

-- example : eval zero_plus_zero.1 = .zero := by
--   unfold zero_plus_zero add
--   simp
--   unfold nat_rec_nat

def two_plus_two := app add.1 add.2 [two.1, two.1]

#eval eval (eval two_plus_two) == four.1

-- #guard check [] two_plus_two.1 two_plus_two.2

-- /-- 2 + 2 = 4 -/
-- def two_plus_two_eq_four := (Term.fls, Term.eq two_plus_two.1 four.1 ℕ)

-- #guard check [] two_plus_two_eq_four.1 two_plus_two_eq_four.2
-- -/
