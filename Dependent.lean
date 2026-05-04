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
  /-- Dependent function type -/
  | fn (α β : Term)
  -- Inductive types
  /-- Dependent product type -/
  | prod (α β : Term)
  /-- Constructor for product -/
  | pair
  /-- Recursor for product -/
  | prod_rec
  /-- Sum type -/
  | sum (α β : Term)
  /-- Left constructor for sum -/
  | inl
  /-- Right constructor for sum -/
  | inr
  /-- Recursor for sum -/
  | sum_rec
  /-- Equality type -/
  | eq (a a' α : Term)
  /-- Constructor for equality -/
  | rfl
  /-- Recursor for equality -/
  | eq_rec
  /-- Natural number type -/
  | nat
  /-- Zero constructor for nats -/
  | zero
  /-- Successor constructor for nats -/
  | succ
  /-- Recursor for nats -/
  | nat_rec
  /-- False (empty type) -/
  | fls
  /-- Recursor for false -/
  | fls_rec
  /-- New named variable -/
  | new (s : String) (t : Term)
  /-- Use of named variable -/
  | name (s : String)
deriving BEq, ReflBEq, LawfulBEq

open Term

def Term.toString : Term → String
  | var x => s!"(list 0n {x})"
  | lam b β => s!"(list 1n {toString b} {toString β})"
  | app f φ a α => s!"(list 2n {toString f} {toString φ} {toString a} {toString α})"
  | typ => "'(3n)"
  | fn α β => s!"(list 4n {toString α} {toString β})"
  | prod α β => s!"(list 5n {toString α} {toString β})"
  | pair => "'(6n)"
  | prod_rec => "'(7n)"
  | sum α β => s!"(list 8n {toString α} {toString β})"
  | inl => "'(9n)"
  | inr => "'(10n)"
  | sum_rec => "'(11n)"
  | eq a a' α => s!"(list 12n {toString a} {toString a'} {toString α})"
  | rfl => "'(13n)"
  | eq_rec => "'(14n)"
  | nat => "'(15n)"
  | zero => "'(16n)"
  | succ => "'(17n)"
  | nat_rec => "'(18n)"
  | fls => "'(19n)"
  | fls_rec => "'(20n)"
  | _ => "bad"

-- instance : ToString Term := ⟨Term.toString⟩

-- instance : ToString (Term × Term) := ⟨fun p ↦ s!"(cons {p.1} {p.2})"⟩

-- `infixr` doesn't work at compile time or something
notation α " ⇨ " β => fn α β -- \he
notation "𝒰" => typ -- \McU
notation "⊥" => fls -- \bo
notation "ℕ" => nat -- \N
-- `max` fixes some precedence issues when parsing
syntax:max "’" ident : term -- \rq
macro_rules
  | `(’$s:ident) => `(name $(Lean.Syntax.mkStrLit s.getId.toString))
syntax ident "◆" term:max : term -- \di
macro_rules
  | `($s:ident ◆ $t) => `(new $(Lean.Syntax.mkStrLit s.getId.toString) $t)

/-- Increment free variables by 1 -/
def incr (d : Nat) : Term → Term
  | var x =>
    var (if d ≤ x then x + 1 else x)
  | lam b β =>
    lam (incr (d + 1) b) (incr (d + 1) β)
  | app f φ a α =>
    app (incr d f) (incr d φ) (incr d a) (incr d α)
  | α ⇨ β =>
    incr d α ⇨ incr (d + 1) β
  | prod α β =>
    prod (incr d α) (incr (d + 1) β)
  | sum α β =>
    sum (incr d α) (incr d β)
  | eq a a' α =>
    eq (incr d a) (incr d a') (incr d α)
  | t => t

/-- Substitute `s` at index `n` in a term -/
def sub (n : Nat) (s : Term) : Term → Term
  | var x =>
    if x == n then s else var (if n < x then x - 1 else x)
  | lam b β =>
    lam (sub (n + 1) (incr 0 s) b) (sub (n + 1) (incr 0 s) β)
  | app f φ a α =>
    app (sub n s f) (sub n s φ) (sub n s a) (sub n s α)
  | α ⇨ β =>
    sub n s α ⇨ sub (n + 1) (incr 0 s) β
  | prod α β =>
    prod (sub n s α) (sub (n + 1) (incr 0 s) β)
  | sum α β =>
    sum (sub n s α) (sub n s β)
  | eq a a' α =>
    eq (sub n s a) (sub n s a') (sub n s α)
  | t => t

/-- Convenience wrapper around `lam` with currying -/
def la (b : Term) : Term → Nat → Term
  | .new s _ ⇨ β, n + 1 => lam (.new s (la b β n)) (.new s β)
  | _, _ => b

/-- Bundle the type with `la` -/
def la' b β n := (la b β n, β)

/-- Convenience wrapper around `app` with currying -/
def ap (f : Term) : Term → List Term → Term
  -- Need to eval both these guys?
  | α ⇨ β, x :: xs => ap (app f (α ⇨ β) x α) (sub 0 x β) xs
  | _, _ => f

/-- Convert from variable names to de Bruijn indices -/
def debruijn (names : List String) : Term → Term
  | name s =>
    var (names.idxOf s)
  | new s t =>
    debruijn (s :: names) t
  | lam b β =>
    lam (debruijn names b) (debruijn names β)
  | app f φ a α =>
    app (debruijn names f) (debruijn names φ) (debruijn names a) (debruijn names α)
  | new s α ⇨ β =>
    debruijn names α ⇨ debruijn (s :: names) β
  | α ⇨ β =>
    debruijn names α ⇨ debruijn ("" :: names) β
  | prod (new s α) β =>
    prod (debruijn names α) (debruijn (s :: names) β)
  | prod α β =>
    prod (debruijn names α) (debruijn ("" :: names) β)
  | sum α β =>
    sum (debruijn names α) (debruijn names β)
  | eq a a' α =>
    eq (debruijn names a) (debruijn names a') (debruijn names α)
  | t => t

#guard debruijn [] (α◆𝒰 ⇨ β◆𝒰 ⇨ ’α ⇨ ’β ⇨ prod ’α ’β) == 𝒰 ⇨ 𝒰 ⇨ var 1 ⇨ var 1 ⇨ prod (var 3) (var 3)

/-- Get type of built-in functions -/
def Term.btype (t : Term) :=
  match t with
  | pair =>
    α◆𝒰 ⇨ β◆𝒰 ⇨ ’α ⇨ ’β ⇨ prod ’α ’β
  | prod_rec =>
    let μ := prod ’α ’β ⇨ 𝒰
    α◆𝒰 ⇨ β◆𝒰 ⇨ m◆μ ⇨ (a◆’α ⇨ b◆’β ⇨ ap ’m μ [ap pair pair.btype [’a, ’b]]) ⇨ p◆(prod ’α ’β) ⇨ ap ’m μ [’p]
  | inl =>
    α◆𝒰 ⇨ β◆𝒰 ⇨ ’α ⇨ sum ’α ’β
  | inr =>
    α◆𝒰 ⇨ β◆𝒰 ⇨ ’β ⇨ sum ’α ’β
  | sum_rec =>
    let μ := sum ’α ’β ⇨ 𝒰
    α◆𝒰 ⇨ β◆𝒰 ⇨ m◆μ ⇨ (a◆’α ⇨ ap ’m μ [ap inl inl.btype [’a]]) ⇨ (b◆’β ⇨ ap ’m μ [ap inr inr.btype [’b]]) ⇨ s◆(sum ’α ’β) ⇨ ap ’m μ [’s]
  | rfl =>
    α◆𝒰 ⇨ a◆’α ⇨ eq ’a ’a ’α
  | eq_rec =>
    let μ := x◆’α ⇨ eq ’a ’x ’α ⇨ 𝒰
    α◆𝒰 ⇨ a◆’α ⇨ m◆μ ⇨ ap ’m μ [’a, ap rfl rfl.btype [’α, ’a]] ⇨ b◆’α ⇨ h◆(eq ’a ’b ’α) ⇨ ap ’m μ [’b, ’h]
  | zero =>
    ℕ
  | succ =>
    ℕ ⇨ ℕ
  | nat_rec =>
    let μ := ℕ ⇨ 𝒰
    m◆μ ⇨ z◆(ap ’m μ [zero]) ⇨ s◆(n◆ℕ ⇨ ap ’m μ [’n] ⇨ ap ’m μ [ap succ succ.btype [’n]]) ⇨ t◆ℕ ⇨ ap ’m μ [’t]
  | fls_rec =>
    m◆(fls ⇨ 𝒰) ⇨ f◆fls ⇨ ap ’m (fls ⇨ 𝒰) [’f]
  | _ =>
    name "bad"
termination_by
  match t with
  | prod_rec | sum_rec | eq_rec | nat_rec => 1
  | _ => 0

/-- `t` should be well-typed or bad things will happen! -/
partial def eval (t : Term) : Term :=
  match t with
  | lam b β =>
    lam (eval b) (eval β)
  -- | app (app (app .fst _ _ _) _ _ _) _ (app (app (app (app .and _ _ _) _ _ _) _ a _) _ _ _) _ =>
    -- eval a
  -- | app (app (app .snd _ _ _) _ _ _) _ (app (app (app (app .and _ _ _) _ _ _) _ _ _) _ b _) _ =>
    -- eval b
  | app (app (app (app .nat_rec _ m _) _ z _) _ f φ) _ n _ =>
    match n with
    | zero => eval z
    -- TODO replace ν with the type of .nat_rec
    | app succ _ n _ => eval (ap f φ [n, ap .nat_rec Term.nat_rec.btype [m, z, f, n]])
    | _ => t
  -- eq_rec seems useless?
  -- | app (app (app (app (app (app eq_rec ε α _) _ a _) _ m _) _ r _) _ a' _) _ h _ =>
  | app f φ a α =>
    -- TODO handle dependent funcs
    let a' := eval a
    match eval f with
    | lam b _ => eval (sub 0 (incr 0 a') b)
    | x => app x φ a' α -- Probably want to eval again here
  | α ⇨ β =>
    eval α ⇨ eval β
  | prod α β =>
    prod (eval α) (eval β)
  | sum α β =>
    sum (eval α) (eval β)
  | eq a a' α =>
    eq (eval a) (eval a') (eval α)
  | t =>
    t

-- /-- -/
-- def defeq (env : List Term) a a' α :=
--   check env a α && check env a' α' && eval env a α == eval env a' α'

-- TODO: A lot of the `==`s here should use defeq
/-- Janky type checker -/
def check (env : List Term) : Term → Term → Bool
  | var x, α =>
    if _ : x < env.length then env[x] == α else false
  | lam b β, α ⇨ β' =>
    β' == β && check (incr 0 <$> (α :: env)) b β
    -- β' == β && (β == 𝒰 || check (incr 0 <$> (α :: env)) β 𝒰) && check (incr 0 <$> (α :: env)) b β
  | app f (α ⇨ β) a α', β' =>
    α' == α && β' == sub 0 a β && check env f (α ⇨ β) && check env a α
  | .nat, 𝒰
  | ⊥, 𝒰 =>
    true
  | α ⇨ β, 𝒰 =>
    check env α 𝒰 && check (incr 0 <$> (α :: env)) β 𝒰
  | prod α β, 𝒰
  | sum α β, 𝒰 =>
    check env α 𝒰 && check env β 𝒰
  | eq a a' α, 𝒰 =>
    check env a α && check env a' α && check env α 𝒰
  | t, τ =>
    debruijn [] t.btype == τ

def check' (t : Term × Term) :=
  check [] (debruijn [] t.1) (debruijn [] t.2)

/-- A → A -/
def a_imp_a := la' ’a (α◆𝒰 ⇨ a◆’α ⇨ ’α) 2

#guard check' a_imp_a

/-- A → B → A ∧ B -/
def a_imp_b_imp_ab := la' (ap pair pair.btype [’α, ’β]) (α◆𝒰 ⇨ β◆𝒰 ⇨ ’α ⇨ ’β ⇨ prod ’α ’β) 2

#guard check' a_imp_b_imp_ab

/-- A → B → B ∧ A -/
def a_imp_b_imp_ba := la' (ap pair pair.btype [’β, ’α, ’b, ’a]) (α◆𝒰 ⇨ β◆𝒰 ⇨ a◆’α ⇨ b◆’β ⇨ prod ’β ’α) 4

#guard check' a_imp_b_imp_ba

/-- Get first element of product -/
def fst α β p := ap prod_rec prod_rec.btype [α, β, la α (prod α β ⇨ 𝒰) 1, la ’a (new "a" α ⇨ β ⇨ α) 2, p]

/-- Get second element of product -/
def snd α β p := ap prod_rec prod_rec.btype [α, β, la β (prod α β ⇨ 𝒰) 1, la ’b (α ⇨ new "b" β ⇨ β) 2, p]

/-- A ∧ B → B ∧ A -/
def ab_imp_ba := la' (and (snd ₸0 ₸1 ’0) ₸1 (fst ₸0 ₸1 ’0) ₸0) (prod ₸0 ₸1 ⇨ prod ₸1 ₸0) 1

#guard check [] ab_imp_ba.1 ab_imp_ba.2

/-- Convenience wrapper around `.inl` -/
def inl α β a := app .inl (𝒰 ⇨ 𝒰 ⇨ ’1 ⇨ sum ’2 ’1) [α, β, a]

/-- ¬(A ∨ B) → ¬A -/
def not_ab_imp_not_a := la' (app ’1 (sum ₸0 ₸1 ⇨ ⊥) [inl ₸0 ₸1 ’0]) ((sum ₸0 ₸1 ⇨ ⊥) ⇨ ₸0 ⇨ ⊥) 2

#guard check [] not_ab_imp_not_a.1 not_ab_imp_not_a.2

/-- A → ¬¬A -/
def a_imp_not_not_a := la' (app ’0 (₸0 ⇨ ⊥) [’1]) (₸0 ⇨ (₸0 ⇨ ⊥) ⇨ ⊥) 2

#guard check [] a_imp_not_not_a.1 a_imp_not_not_a.2

/-- ¬¬¬A → ¬A -/
def not_not_not_a_imp_not_a := la' (app ’1 (((₸0 ⇨ ⊥) ⇨ ⊥) ⇨ ⊥) [app a_imp_not_not_a.1 a_imp_not_not_a.2 [’0]]) ((((₸0 ⇨ ⊥) ⇨ ⊥) ⇨ ⊥) ⇨ ₸0 ⇨ ⊥) 2

#guard check [] not_not_not_a_imp_not_a.1 not_not_not_a_imp_not_a.2

/-- Alternative proof of ¬¬¬A → ¬A -/
def not_not_not_a_imp_not_a' := la' (app ’1 (((₸0 ⇨ ⊥) ⇨ ⊥) ⇨ ⊥) [lam (app ’0 (₸0 ⇨ ⊥) [’1]) ⊥]) ((((₸0 ⇨ ⊥) ⇨ ⊥) ⇨ ⊥) ⇨ ₸0 ⇨ ⊥) 2

#guard check [] not_not_not_a_imp_not_a'.1 not_not_not_a_imp_not_a'.2

/-- Convenience wrapper around `.rfl` -/
def rfl' a α := app .rfl (𝒰 ⇨ ’0 ⇨ eq ’0 ’0 ’1) [α, a]

/-- ∀ a : A, a = a -/
def a_eq_a := la' (rfl' ’0 ₸0) (₸0 ⇨ eq ’0 ’0 ₸0) 1

#guard check [] a_eq_a.1 a_eq_a.2

/-- Convenience wrapper around `.succ` -/
def succ n := app .succ (ℕ ⇨ ℕ) [n]

-- /-- 2 exists (yeah I know this is not super exciting) -/
def two := (succ (succ zero), ℕ)

#guard check [] two.1 two.2

/-- 4 exists -/
def four := (succ (succ two.1), ℕ)

#guard check [] four.1 four.2

#check Nat.rec

/-- `.nat_rec` where the motive always returns `ℕ` -/
def nat_rec_nat z f := Termapp (app (app .nat_rec ((ℕ ⇨ 𝒰) ⇨ app ’0 (ℕ ⇨ 𝒰) zero ℕ ⇨ (ℕ ⇨ app ’2 (ℕ ⇨ 𝒰) ’0 ℕ ⇨ app ’3 (ℕ ⇨ 𝒰) (app .succ (ℕ ⇨ ℕ) ’1 ℕ) ℕ) ⇨ ℕ ⇨ app ’0 ℕ ’3 (ℕ ⇨ 𝒰)) (lam ℕ 𝒰) (ℕ ⇨ 𝒰)) (ℕ ⇨ (ℕ ⇨ ℕ ⇨ ℕ) ⇨ ℕ ⇨ ℕ) z ℕ) ((ℕ ⇨ ℕ ⇨ ℕ) ⇨ ℕ ⇨ ℕ) f (ℕ ⇨ ℕ ⇨ ℕ)

#eval nat_rec_nat ₸0 ₸1

def nat_rec_nat' z f := app .nat_rec ((ℕ ⇨ 𝒰) ⇨ app ’0 (ℕ ⇨ 𝒰) zero ℕ ⇨ (ℕ ⇨ app ’2 (ℕ ⇨ 𝒰) ’0 ℕ ⇨ app ’3 (ℕ ⇨ 𝒰) (app .succ (ℕ ⇨ ℕ) ’1 ℕ) ℕ) ⇨ ℕ ⇨ app ’0 ℕ ’3 (ℕ ⇨ 𝒰)) [lam ℕ 𝒰, z, f]

#eval nat_rec_nat' ₸0 ₸1

#check Nat.rec

/-- Addition -/
def add := la' (nat_rec_nat ’0 (lam (succ ’0) (ℕ ⇨ ℕ) 1)) (ℕ ⇨ ℕ ⇨ ℕ) 1

#guard check [] add.1 add.2

def zero_plus_zero := app add.1 add.2 [zero, zero]

#eval eval (eval zero_plus_zero)

def zero_plus_one := app add.1 add.2 [zero, succ zero]

#eval eval (eval zero_plus_one)

-- example : eval zero_plus_zero.1 = zero := by
--   unfold zero_plus_zero add
--   simp
--   unfold nat_rec_nat

def two_plus_two := app add.1 add.2 [two.1, two.1]

#eval eval (eval two_plus_two) == four.1


def eq_rec_type := 𝒰 ⇨ ’0 ⇨ (’1 ⇨ eq ’1 ’0 ’2 ⇨ 𝒰) ⇨ app ’0 (’2 ⇨ eq ’2 ’0 ’3 ⇨ 𝒰) [’1, app .rfl (𝒰 ⇨ ’0 ⇨ eq ’0 ’0 ’1) [’2, ’2]] ⇨ ’3 ⇨ eq ’3 ’0 ’4 ⇨ app ’3 (’5 ⇨ eq ’5 ’0 ’6 ⇨ 𝒰) [’1, ’0]

def rw := lam (app eq_rec eq_rec_type [’5, ’4, lam (app ’5 (’7 ⇨ 𝒰) [’1]) (’5 ⇨ (eq ’5 ’0 ’6) ⇨ 𝒰) 2]) (𝒰 ⇨ ’0 ⇨ ’1 ⇨ (’2 ⇨ 𝒰) ⇨ eq ’2 ’1 ’3 ⇨ app ’1 (’4 ⇨ 𝒰) [’3] ⇨ app ’2 (’5 ⇨ 𝒰) [’3]) 6

-- #guard check [] two_plus_two.1 two_plus_two.2

-- /-- 2 + 2 = 4 -/
-- def two_plus_two_eq_four := (Term.fls, Termeq two_plus_two.1 four.1 ℕ)

-- #guard check [] two_plus_two_eq_four.1 two_plus_two_eq_four.2
-- -/
