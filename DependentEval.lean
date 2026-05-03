-- μLean, a very simple proof assistant with dependent types!

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

-- `infixr` doesn't work?
notation l " ⇨ " r => Term.fn l r
notation "λ " b:max β:max => Term.lam b β
notation "◆ " f:max φ:max a:max α:max => Term.app f φ a α
-- The `max` fixes some precedence issues when parsing or something
notation:max "’" r:max => Term.var r
notation:max "₸" r:max => Term.new r
notation "𝒰" => Term.typ
notation "⊥" => Term.fls
notation "ℕ" => Term.nat

/-- Increment free variables by 1 -/
def incr (d : Nat) : Term → Term
  | ’x =>
    ’(if d ≤ x then x + 1 else x)
  | (λ b β) => -- Need parentheses to avoid parsing as a Lean lambda
    λ (incr (d + 1) b) (incr (d + 1) β)
  | ◆ f φ a α =>
    ◆ (incr d f) (incr d φ) (incr d a) (incr d α)
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
  | ◆ f φ a α =>
    ◆ (sub n s f) (sub n s φ) (sub n s a) (sub n s α)
  | α ⇨ β =>
    sub n s α ⇨ sub (n + 1) (incr 0 s) β
  | .prod α β =>
    .prod (sub n s α) (sub (n + 1) (incr 0 s) β)
  | .sum α β =>
    .sum (sub n s α) (sub n s β)
  | .eq a a' α =>
    .eq (sub n s a) (sub n s a') (sub n s α)
  | x => x

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
  | ◆ f (α ⇨ β) a α', β' =>
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
  -- https://lean-lang.org/theorem_proving_in_lean4/Inductive-Types/#inductive-families
  | .eq_rec, 𝒰 ⇨ ’0 ⇨ (’1 ⇨ .eq ’1 ’0 ’2 ⇨ 𝒰) ⇨ ◆ (◆ ’0 (’2 ⇨ .eq ’2 ’0 ’3 ⇨ 𝒰) ’1 ’2) (.eq ’1 ’1 ’2 ⇨ 𝒰) (◆ (◆ .rfl (𝒰 ⇨ ’0 ⇨ .eq ’0 ’0 ’1) ’2 𝒰) (’2 ⇨ .eq ’0 ’0 ’3) ’2 ’3) (.eq ’1 ’1 ’2) ⇨ ’3 ⇨ .eq ’3 ’0 ’4 ⇨ ◆ (◆ ’3 (’5 ⇨ .eq ’5 ’0 ’6 ⇨ 𝒰) ’1 ’5) (.eq ’4 ’1 ’5) ’0 (.eq ’4 ’1 ’5)
  | .nat_rec, (ℕ ⇨ 𝒰) ⇨ ◆ ’0 (ℕ ⇨ 𝒰) .zero ℕ ⇨ (ℕ ⇨ ◆ ’2 (ℕ ⇨ 𝒰) ’0 ℕ ⇨ ◆ ’3 (ℕ ⇨ 𝒰) (◆ .succ (ℕ ⇨ ℕ) ’1 ℕ) ℕ) ⇨ ℕ ⇨ ◆ ’0 ℕ ’3 (ℕ ⇨ 𝒰)
  | .zero, ℕ
  | .succ, ℕ ⇨ ℕ
  | .fls_rec, ⊥ ⇨ _ =>
    true
  | _, _ =>
    false

-- /-- `incr` preserves type -/
-- theorem check_incr env' (h : check (env' ++ env) t τ) (hd : env'.length = d) : check (env' ++ α :: env) (incr d t) τ := by
--   match t, τ with
--   | .var x, α =>
--     grind [check, incr]
--   | .lam b β, .fn α β' =>
--     simp [check] at h
--     simpa [check, incr] using ⟨h.1, check_incr (α :: env') h.2 (by grind)⟩
--   | .app f (.fn α β) a α', β' =>
--     simp [check] at h
--     simpa [check, incr] using ⟨⟨h.1.1, check_incr env' h.1.2 hd⟩, check_incr env' h.2 hd⟩

-- /-- `sub` preserves type -/
-- theorem check_sub env' (h : check (env' ++ σ :: env) t τ) (hn : n = env'.length) (hs : check (env' ++ env) s σ) : check (env' ++ env) (sub n s t) τ := by
--   match t, τ with
--   | .var x, α =>
--     grind [check, sub]
--   | .lam (b, β), .fn α β' =>
--     simp [check] at h
--     simpa [check, sub] using ⟨h.1, check_sub (α :: env') h.2 (by grind) (check_incr [] hs (by rfl))⟩
--   | .app (f, .fn α β) (a, α'), β' =>
--     simp [check] at h
--     simpa [check, sub] using ⟨⟨h.1.1, check_sub env' h.1.2 hn hs⟩, check_sub env' h.2 hn hs⟩

/-- Eval without worrying about types -/
partial def eval_untyped : Term → Term
  | (λ b β) =>
    λ (eval_untyped b) β
  | ◆ f φ a α =>
    let a' := eval_untyped a
    match eval_untyped f with
    | .lam b _ => eval_untyped (sub 0 (incr 0 a') b)
    | x => .app x φ a' α
  | α ⇨ β =>
    (eval_untyped α) ⇨ (eval_untyped β)
  | .prod α β =>
    .prod (eval_untyped α) (eval_untyped β)
  -- and
  -- fst
  -- snd
  | .sum α β =>
    .sum (eval_untyped α) (eval_untyped β)
  -- inl
  -- inr
  | .eq a a' α =>
    .eq (eval_untyped a) (eval_untyped a') (eval_untyped α)
  -- eq_rec
  -- nat_rec
  | x =>
    x

/-
| var (x : Nat)
  | lam (b β : Term)
  | app (f φ a α : Term)
  -- Types
  | typ
  | new (x : Nat)
  | fn (α β : Term)
  -- Inductive types
  | prod (α β : Term)
  | and
  | fst
  | snd
  | sum (α β : Term)
  | inl
  | inr
  | eq (a a' α : Term)
  | rfl
  | eq_rec
  | nat
  | zero
  | succ
  | nat_rec
  | fls
  | fls_rec
  -/
  -- | x => x

/-- A → A -/
def a_imp_a := (λ ’0 ₸0, ₸0 ⇨ ₸0)

#guard check [] a_imp_a.1 a_imp_a.2

/-- ∀ A : 𝒰, A → A -/
def a_imp_a' := (λ (λ ’0 ’1) (’0 ⇨ ’1), 𝒰 ⇨ ’0 ⇨ ’1)

#guard check [] a_imp_a'.1 a_imp_a'.2

/-- Convenience wrapper around `.and` -/
def and a α b β := ◆ (◆ (◆ (◆ .and (𝒰 ⇨ 𝒰 ⇨ ’1 ⇨ ’1 ⇨ .prod ’3 ’3) α 𝒰) (𝒰 ⇨ α ⇨ ’1 ⇨ .prod α ’3) β 𝒰) (α ⇨ β ⇨ .prod α β) a α) (β ⇨ .prod α β) b β

/-- A → B → A ∧ B -/
def a_imp_b_imp_ab := (◆ (◆ .and (𝒰 ⇨ 𝒰 ⇨ ’1 ⇨ ’1 ⇨ .prod ’3 ’3) ₸0 𝒰) (𝒰 ⇨ ₸0 ⇨ ’1 ⇨ .prod ₸0 ’3) ₸1 𝒰, ₸0 ⇨ ₸1 ⇨ .prod ₸0 ₸1)

#guard check [] a_imp_b_imp_ab.1 a_imp_b_imp_ab.2

/-- A → B → B ∧ A -/
def a_imp_b_imp_ba := (λ (λ (and ’0 ₸1 ’1 ₸0) (.prod ₸1 ₸0)) (₸1 ⇨ .prod ₸1 ₸0), ₸0 ⇨ ₸1 ⇨ .prod ₸1 ₸0)

#guard check [] a_imp_b_imp_ba.1 a_imp_b_imp_ba.2

/-- Convenience wrapper around `.fst` -/
def fst α β p := ◆ (◆ (◆ .fst (𝒰 ⇨ 𝒰 ⇨ .prod ’1 ’1 ⇨ ’2) α 𝒰) (𝒰 ⇨ .prod α ’1 ⇨ α) β 𝒰) (.prod α β ⇨ α) p (.prod α β)

/-- Convenience wrapper around `.snd` -/
def snd α β p := ◆ (◆ (◆ .snd (𝒰 ⇨ 𝒰 ⇨ .prod ’1 ’1 ⇨ ’1) α 𝒰) (𝒰 ⇨ .prod α ’1 ⇨ ’1) β 𝒰) (.prod α β ⇨ β) p (.prod α β)

/-- A ∧ B → B ∧ A -/
def ab_imp_ba := (λ (and (snd ₸0 ₸1 ’0) ₸1 (fst ₸0 ₸1 ’0) ₸0) (.prod ₸1 ₸0), .prod ₸0 ₸1 ⇨ .prod ₸1 ₸0)

#guard check [] ab_imp_ba.1 ab_imp_ba.2

/-- Convenience wrapper around `.inl` -/
def inl α β a := ◆ (◆ (◆ .inl (𝒰 ⇨ 𝒰 ⇨ ’1 ⇨ .sum ’2 ’1) α 𝒰) (𝒰 ⇨ α ⇨ .sum α ’1) β 𝒰) (α ⇨ .sum α β) a α

/-- ¬(A ∨ B) → ¬A -/
def not_ab_imp_not_a := (λ (λ (◆ ’1 (.sum ₸0 ₸1 ⇨ ⊥) (inl ₸0 ₸1 ’0) (.sum ₸0 ₸1)) ⊥) (₸0 ⇨ ⊥), (.sum ₸0 ₸1 ⇨ ⊥) ⇨ ₸0 ⇨ ⊥)

#guard check [] not_ab_imp_not_a.1 not_ab_imp_not_a.2

/-- A → ¬¬A -/
def a_imp_not_not_a := (λ (λ (◆ ’0 (₸0 ⇨ ⊥) ’1 ₸0) ⊥) ((₸0 ⇨ ⊥) ⇨ ⊥), ₸0 ⇨ (₸0 ⇨ ⊥) ⇨ ⊥)

#guard check [] a_imp_not_not_a.1 a_imp_not_not_a.2

/-- ¬¬¬A → ¬A -/
def not_not_not_a_imp_not_a := (λ (λ (◆ ’1 (((₸0 ⇨ ⊥) ⇨ ⊥) ⇨ ⊥) (◆ a_imp_not_not_a.1 a_imp_not_not_a.2 ’0 ₸0) ((₸0 ⇨ ⊥) ⇨ ⊥)) ⊥) (₸0 ⇨ ⊥), (((₸0 ⇨ ⊥) ⇨ ⊥) ⇨ ⊥) ⇨ ₸0 ⇨ ⊥)

#guard check [] not_not_not_a_imp_not_a.1 not_not_not_a_imp_not_a.2

/-- Convenience wrapper around `.rfl` -/
def rfl' a α := ◆ (◆ .rfl (𝒰 ⇨ ’0 ⇨ .eq ’0 ’0 ’1) α 𝒰) (α ⇨ .eq ’0 ’0 α) a α

/-- ∀ a : A, a = a -/
def a_eq_a := (λ (rfl' ’0 ₸0) (.eq ’0 ’0 ₸0), ₸0 ⇨ .eq ’0 ’0 ₸0)

#guard check [] a_eq_a.1 a_eq_a.2

/-- Convenience wrapper around `.succ` -/
def succ n := ◆ .succ (ℕ ⇨ ℕ) n .nat

-- /-- 2 exists (yeah I know this is not super exciting) -/
def two := (succ (succ .zero), ℕ)

#guard check [] two.1 two.2

/-- 4 exists -/
def four := (succ (succ two.1), ℕ)

#guard check [] four.1 four.2

#check Nat.rec

/-- `.nat_rec` where the motive always returns `ℕ` -/
def nat_rec_nat z f := ◆ (◆ (◆ .nat_rec ((ℕ ⇨ 𝒰) ⇨ ◆ ’0 (ℕ ⇨ 𝒰) .zero ℕ ⇨ (ℕ ⇨ ◆ ’2 (ℕ ⇨ 𝒰) ’0 ℕ ⇨ ◆ ’3 (ℕ ⇨ 𝒰) (◆ .succ (ℕ ⇨ ℕ) ’1 ℕ) ℕ) ⇨ ℕ ⇨ ◆ ’0 ℕ ’3 (ℕ ⇨ 𝒰)) (λ ℕ 𝒰) (ℕ ⇨ 𝒰)) (ℕ ⇨ (ℕ ⇨ ℕ ⇨ ℕ) ⇨ ℕ ⇨ ℕ) z ℕ) ((ℕ ⇨ ℕ ⇨ ℕ) ⇨ ℕ ⇨ ℕ) f (ℕ ⇨ ℕ ⇨ ℕ)

#check Nat.rec

/-- Addition -/
def add := (λ (nat_rec_nat ’0 (λ (λ (succ ’0) (ℕ ⇨ ℕ)) ℕ)) (ℕ ⇨ ℕ), ℕ ⇨ ℕ ⇨ ℕ)

#guard check [] add.1 add.2

-- def two_plus_two := (◆ (◆ add.1 add.2 two.1 two.2) (.fn ℕ ℕ) two.1 two.2, Termℕ)

-- #guard check [] two_plus_two.1 two_plus_two.2

-- /-- 2 + 2 = 4 -/
-- def two_plus_two_eq_four := (Term.fls, Term.eq two_plus_two.1 four.1 ℕ)

-- #guard check [] two_plus_two_eq_four.1 two_plus_two_eq_four.2
-- -/
