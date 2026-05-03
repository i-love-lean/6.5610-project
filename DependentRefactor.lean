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
  | .prod α β =>
    .prod (incr d α) (incr d β)
  | .sum α β =>
    .sum (incr d α) (incr d β)
  | .eq a a' α =>
    .eq (incr d a) (incr d a') (incr d α)
  | x => x

/-- Substitute `s` at index `n` in a term -/
def sub (n : Nat) (s : Term) : Term → Term
  | .var x =>
    if x == n then s else .var (if n < x then x - 1 else x)
  | .lam b β =>
    .lam (sub (n + 1) (incr 0 s) b) (sub (n + 1) (incr 0 s) β)
  | .app f φ a α =>
    .app (sub n s f) (sub n s φ) (sub n s a) (sub n s α)
  | .fn α β =>
    .fn (sub n s α) (sub n s β)
  | .prod α β =>
    .prod (sub n s α) (sub n s β)
  | .sum α β =>
    .sum (sub n s α) (sub n s β)
  | .eq a a' α =>
    .eq (sub n s a) (sub n s a') (sub n s α)
  | x => x

notation "𝒰" => Term.typ
notation "ℕ" => Term.nat
-- `infixr` doesn't work?
notation l " →ₘ " r => Term.fn l r
-- The `max` fixes some precedence issues when parsing or something
notation:max "’" r:max => Term.var r

mutual
-- /-- -/
-- def defeq (env : List Term) a a' α :=
--   check env a α && check env a' α' && eval env a α == eval env a' α'

-- TODO: A lot of the `==`s here should use defeq
/-- Janky type checker -/
def check (env : List Term) : Term → Term → Bool
  | .var x, α =>
    if _ : x < env.length then env[x] == α else false
  | .lam b β, α →ₘ β' =>
    β' == β && (β == 𝒰 || check (α :: env) β 𝒰) && check (α :: env) b β
  | .app f (α →ₘ β) a α', β' =>
    α' == α && β' == β && check env f (α →ₘ β) && check env a α
  | .new x, 𝒰
  | .nat, 𝒰
  | .fls, 𝒰 =>
    true
  | .fn α β, 𝒰
  | .prod α β, 𝒰
  | .sum α β, 𝒰 =>
    check env α 𝒰 && check env β 𝒰
  | .eq a a' α, 𝒰 =>
    check env a α && check env a' α && check env α 𝒰
  | .and, 𝒰 →ₘ 𝒰 →ₘ ’1 →ₘ ’1 →ₘ .prod ’3 ’2
  | .fst, 𝒰 →ₘ 𝒰 →ₘ .prod ’1 ’0 →ₘ ’2
  | .snd, 𝒰 →ₘ 𝒰 →ₘ .prod ’1 ’0 →ₘ ’1
  | .inl, 𝒰 →ₘ 𝒰 →ₘ ’1 →ₘ .sum ’2 ’1
  | .inr, 𝒰 →ₘ 𝒰 →ₘ ’0 →ₘ .sum ’2 ’1
  | .rfl, 𝒰 →ₘ ’0 →ₘ .eq ’0 ’0 ’1
  -- https://lean-lang.org/theorem_proving_in_lean4/Inductive-Types/#inductive-families
  | .eq_rec, 𝒰 →ₘ ’0 →ₘ (’1 →ₘ .eq ’1 ’0 ’2 →ₘ 𝒰) →ₘ .app (.app ’0 (’2 →ₘ .eq ’2 ’0 ’3 →ₘ 𝒰) ’1 ’2) (.eq ’1 ’1 ’2 →ₘ 𝒰) (.app (.app .rfl (𝒰 →ₘ ’0 →ₘ .eq ’0 ’0 ’1) ’2 𝒰) (’2 →ₘ .eq ’0 ’0 ’3) ’2 ’3) (.eq ’1 ’1 ’2) →ₘ ’3 →ₘ .eq ’3 ’0 ’4 →ₘ .app (.app ’3 (’5 →ₘ .eq ’5 ’0 ’6 →ₘ 𝒰) ’1 ’5) (.eq ’4 ’1 ’5) ’0 (.eq ’4 ’1 ’5)
  | .nat_rec, (ℕ →ₘ 𝒰) →ₘ .app ’0 (ℕ →ₘ 𝒰) .zero ℕ →ₘ (ℕ →ₘ .app ’2 (ℕ →ₘ 𝒰) ’0 ℕ →ₘ .app ’3 (ℕ →ₘ 𝒰) (.app .succ (ℕ →ₘ ℕ) ’1 ℕ) ℕ)
  | .zero, ℕ
  | .succ, .fn ℕ ℕ
  | .fls_rec, .fn .fls _ =>
    true
  | _, _ =>
    false

end

/-- A → A -/
def a_imp_a := (Term.lam ’0 (.new 0), .new 0 →ₘ .new 0)

#guard check [] a_imp_a.1 a_imp_a.2

def and a α b β := Term.app (.app (.app (.app .and (𝒰 →ₘ 𝒰 →ₘ ’1 →ₘ ’1 →ₘ .prod ’3 ’2) α 𝒰) (𝒰 →ₘ α →ₘ ’1 →ₘ .prod α ’2) β 𝒰) (α →ₘ β →ₘ .prod α β) a α) (β →ₘ .prod α β) b β

/-- A → B → A ∧ B -/
def a_imp_b_imp_ab := (Term.app (.app .and (𝒰 →ₘ 𝒰 →ₘ ’1 →ₘ ’1 →ₘ .prod ’3 ’2) (.new 0) 𝒰) (𝒰 →ₘ (.new 0) →ₘ ’1 →ₘ .prod (.new 0) ’2) (.new 1) 𝒰, .new 0 →ₘ .new 1 →ₘ .prod (.new 0) (.new 1))

example : check [] a_imp_b_imp_ab.1 a_imp_b_imp_ab.2 = true := by
  unfold check a_imp_b_imp_ab
  simp only [BEq.rfl, Bool.true_and, Bool.and_eq_true, beq_iff_eq]




#guard check [] a_imp_b_imp_ab.1 a_imp_b_imp_ab.2


/-- A → B → B ∧ A -/
def a_imp_b_imp_ba := (Term.lam (.lam (and ’0 (.new 1) ’1 (.new 0)) (.prod (.new 1) (.new 0))) (.new 1 →ₘ .prod (.new 1) (.new 0)), .new 0 →ₘ .new 1 →ₘ .prod (.new 1) (.new 0))

-- example : check [] a_imp_b_imp_ba.1 a_imp_b_imp_ba.2 = true := by
--   unfold check a_imp_b_imp_ba
--   simp
--   have : check [Term.new 0] (Term.new 1 →ₘ (Term.new 1).prod (Term.new 0)) 𝒰 = true := by decide
--   simp [this]
--   unfold check
--   simp
--   have : check [Term.new 1, Term.new 0] ((Term.new 1).prod (Term.new 0)) 𝒰 = true := by decide
--   simp [this]
--   unfold _root_.and check
--   simp
--   have : check [Term.new 1, Term.new 0] (’1) (Term.new 0) = true := by decide
--   simp [this]
--   unfold check
--   simp
--   have : check [Term.new 1, Term.new 0] (’0) (Term.new 1) = true := by decide
--   simp [this]
--   unfold check






#eval a_imp_b_imp_ba.1

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
def add := (Term.lam (.nat_rec .nat .zero .nat (.var 0) .nat (.lam (.lam (.succ (.var 2) .nat) .nat) (.fn .nat .nat)) (.fn .nat (.fn .nat .nat))) (.fn .nat .nat), Term.fn .nat (.fn .nat .nat))

#guard check [] add.1 add.2

def two_plus_two := (Term.app (.app add.1 add.2 two.1 two.2) (.fn .nat .nat) two.1 two.2, Term.nat)

#guard check [] two_plus_two.1 two_plus_two.2

/-- 2 + 2 = 4 -/
def two_plus_two_eq_four := (Term.fls, Term.eq two_plus_two.1 four.1 .nat)

#guard check [] two_plus_two_eq_four.1 two_plus_two_eq_four.2
