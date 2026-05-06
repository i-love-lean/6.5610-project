/-
# μLean

A very simple proof assistant based on the calculus of constructions with a few inductive types!

μLean is largely based on Lean (obviously) but without general inductive types. Also, unlike Lean, μLean only has two cumulative universes, since stuff above `Type 1` is rarely used in practice anyways. To avoid paradoxes, `Type 1` in μLean does not have a type. Propositions in μLean live in `Type` instead of a dedicated `Prop` universe, which also avoids a lot of Lean's `Prop` weirdness. Lastly, μLean does not have the law of excluded middle.

## Basic definitions
-/

inductive Term
  -- Lambda calculus stuff
  /-- Variable with de Bruijn index -/
  | var (x : Nat)
  /-- Lambda -/
  | lam (b β : Term)
  /-- Function application -/
  | app (f φ a α : Term)
  -- Types
  /-- Type universes -/
  | typ (u : Fin 2)
  /-- Dependent function type -/
  | fn (α β : Term)
  -- Inductive types
  /-- Dependent product type -/
  | prod (α β : Term)
  /-- Constructor for product -/
  | pmk
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
  | refl
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
  /-- Unit type -/
  | unit
  /-- Constructor for unit (no recursor because it's silly) -/
  | intro
  /-- False (empty type) -/
  | fls
  /-- Recursor for false -/
  | fls_rec
  -- Special stuff for handling variable names
  /-- New named variable -/
  | new (s : String) (t : Term)
  /-- Using named variable -/
  | name (s : String)
-- These let us compare terms
deriving BEq, ReflBEq, LawfulBEq

open Term

/-
## De Bruijn index manipulation
-/

/-- Helper function for recursing over terms -/
def term_rec (s : α) (on_dep : α → α) (on_var : α → Nat → Term) :=
  let rec term_rec' s
  | var x =>
    on_var s x
  | lam b β =>
    lam (term_rec' (on_dep s) b) (term_rec' (on_dep s) β)
  | app f φ a α =>
    app (term_rec' s f) (term_rec' s φ) (term_rec' s a) (term_rec' s α)
  | fn α β =>
    fn (term_rec' s α) (term_rec' (on_dep s) β)
  | prod α β =>
    prod (term_rec' s α) (term_rec' s β)
  | sum α β =>
    sum (term_rec' s α) (term_rec' s β)
  | eq a a' α =>
    eq (term_rec' s a) (term_rec' s a') (term_rec' s α)
  | t =>
    t
  term_rec' s

/-- Increment free variables by 1 -/
def incr :=
  term_rec 0 (· + 1) fun d x ↦ var (if d ≤ x then x + 1 else x)

/-- Substitute `t'` at index 0 in a term -/
def sub (t' : Term) :=
  term_rec (0, t') (fun (d, t') ↦ (d + 1, incr t')) fun (d, t') x ↦ if x == d then t' else var (if d < x then x - 1 else x)

/-
## Syntactic sugar yay

μLean satisfies the de Bruijn criterion, which means that we use Lean as a metalanguage and write proofs in a high-level vernacular that gets desugared down to a low-level AST for the type checker. This keeps the type checker itself simple.
-/

-- `infixr` doesn't work at compile time or something oof
notation α " ⇨ " β => fn α β -- \hey
notation "𝒰" => typ 0 -- \McU
notation "𝒰₁" => typ 1 -- \McU\1
notation "ℕ" => nat -- \N
notation "⊥" => fls -- \bo
-- `max` fixes some precedence issues when parsing
syntax ident "◆" term:max : term -- \di
macro_rules
  | `($s:ident ◆ $t) => `(new $(Lean.Syntax.mkStrLit s.getId.toString) $t)
syntax:max "’" ident : term -- \rq
macro_rules
  | `(’$s:ident) => `(name $(Lean.Syntax.mkStrLit s.getId.toString))

/-- Convenience wrapper around `lam` with currying -/
def la (b : Term) : Term → Nat → Term
  | α ⇨ β, n + 1 =>
    let s :=
      match α with
      | new s _ => s
      | _ => ""
    lam (new s (la b β n)) (new s β)
  | _, _ =>
    b

/-- Bundle the type with `la` (generally primed functions return pairs)-/
def la' b β n := (la b β n, β)

/-- Substitute `t'` for variable name `s` in a term (oops I just ignored my convention) -/
def sub' (s : String) (t' : Term) : Term → Term
  | name s' =>
    if s' == s then t' else name s'
  | new s' t =>
    if s' == s then new s' t else new s' (sub' s t' t)
  | lam b β =>
    lam (sub' s t' b) (sub' s t' β)
  | app f φ a α =>
    app (sub' s t' f) (sub' s t' φ) (sub' s t' a) (sub' s t' α)
  | α ⇨ β =>
    sub' s t' α ⇨ sub' s t' β
  | prod α β =>
    prod (sub' s t' α) (sub' s t' β)
  | sum α β =>
    sum (sub' s t' α) (sub' s t' β)
  | eq a a' α =>
    eq (sub' s t' a) (sub' s t' a') (sub' s t' α)
  | t =>
    t

/-- Convenience wrapper around `app` with currying -/
def ap (f : Term) : Term → List Term → Term
  | α ⇨ β, x :: xs =>
    let (α', β') :=
      match α with
      | new s α' => (α', sub' s x β)
      | α => (α, sub x β)
    ap (app f (α ⇨ β) x α') β' xs
  | _, _ =>
    f

/-- Convert from variable names to de Bruijn indices -/
def dbify (names : List String) : Term → Term
  | name s =>
    -- Panicking is usually bad but helpful here for debugging
    var (names.idxOf? s).get!
  | new s t =>
    dbify (s :: names) t
  | lam b β =>
    lam (dbify names b) (dbify names β)
  | app f φ a α =>
    app (dbify names f) (dbify names φ) (dbify names a) (dbify names α)
  | new s α ⇨ β =>
    dbify names α ⇨ dbify (s :: names) β
  | α ⇨ β =>
    dbify names α ⇨ dbify ("" :: names) β
  | prod α β =>
    prod (dbify names α) (dbify names β)
  | sum α β =>
    sum (dbify names α) (dbify names β)
  | eq a a' α =>
    eq (dbify names a) (dbify names a') (dbify names α)
  | t =>
    t

/-
## The type checker

Now for the fun part!
-/

/-- Get type of built-in functions (much nicer to write these in the vernacular!) -/
-- TODO: Generate these at compile time
def Term.btype (t : Term) :=
  dbify [] <|
    match t with
    | 𝒰 =>
      𝒰₁
    | pmk =>
      α◆𝒰 ⇨ β◆(’α ⇨ 𝒰) ⇨ a◆’α ⇨ ap ’β (’α ⇨ 𝒰) [’a] ⇨ prod ’α ’β
    | prod_rec =>
      let μ := prod ’α ’β ⇨ 𝒰
      α◆𝒰 ⇨ β◆(’α ⇨ 𝒰) ⇨ m◆μ ⇨ (a◆’α ⇨ b◆(ap ’β (’α ⇨ 𝒰) [’a]) ⇨ ap ’m μ [ap pmk pmk.btype [’α, ’β, ’a, ’b]]) ⇨ p◆(prod ’α ’β) ⇨ ap ’m μ [’p]
    | inl =>
      α◆𝒰 ⇨ β◆𝒰 ⇨ ’α ⇨ sum ’α ’β
    | inr =>
      α◆𝒰 ⇨ β◆𝒰 ⇨ ’β ⇨ sum ’α ’β
    | sum_rec =>
      let μ := sum ’α ’β ⇨ 𝒰
      α◆𝒰 ⇨ β◆𝒰 ⇨ m◆μ ⇨ (a◆’α ⇨ ap ’m μ [ap inl inl.btype [’α, ’β, ’a]]) ⇨ (b◆’β ⇨ ap ’m μ [ap inr inr.btype [’α, ’β, ’b]]) ⇨ s◆(sum ’α ’β) ⇨ ap ’m μ [’s]
    | refl =>
      α◆𝒰 ⇨ a◆’α ⇨ eq ’a ’a ’α
    | eq_rec =>
      let μ := x◆’α ⇨ eq ’a ’x ’α ⇨ 𝒰
      α◆𝒰 ⇨ a◆’α ⇨ m◆μ ⇨ ap ’m μ [’a, ap refl refl.btype [’α, ’a]] ⇨ b◆’α ⇨ h◆(eq ’a ’b ’α) ⇨ ap ’m μ [’b, ’h]
    | ℕ =>
      𝒰
    | zero =>
      ℕ
    | succ =>
      ℕ ⇨ ℕ
    | nat_rec =>
      let μ := ℕ ⇨ 𝒰
      m◆μ ⇨ z◆(ap ’m μ [zero]) ⇨ s◆(n◆ℕ ⇨ ap ’m μ [’n] ⇨ ap ’m μ [ap succ succ.btype [’n]]) ⇨ t◆ℕ ⇨ ap ’m μ [’t]
    | unit =>
      𝒰
    | intro =>
      unit
    | ⊥ =>
      𝒰
    | fls_rec =>
      m◆(⊥ ⇨ 𝒰) ⇨ f◆⊥ ⇨ ap ’m (⊥ ⇨ 𝒰) [’f]
    | _ =>
      t
-- We need a termination proof here because Lean is stupid
termination_by
  match t with
  | prod_rec | sum_rec | eq_rec | nat_rec => 1
  | _ => 0

/-- The input should be well-typed or bad things will happen! -/
partial def eval : Term → Term
  | lam b β =>
    lam (eval b) (eval β)
  | app f φ a α =>
    let f' := eval f
    -- Apparently this works? 🤷
    match f', eval a with
    | lam b _, a' =>
      eval (sub a' b)
    | app (app (app (app prod_rec _ _ _) _ _ _) _ _ _) _ g (α ⇨ γ), app (app (app (app pmk _ _ _) _ _ _) _ a _) _ b β =>
      eval (app (app g (α ⇨ γ) a α) (sub a γ) b β)
    | app (app (app (app (app sum_rec _ _ _) _ _ _) _ _ _) _ g γ) _ _ _, app (app (app inl _ _ _) _ _ _) _ a α =>
      eval (app g γ a α)
    | app (app (app (app (app sum_rec _ _ _) _ _ _) _ _ _) _ _ _) _ g γ, app (app (app inr _ _ _) _ _ _) _ b β =>
      eval (app g γ b β)
    -- TODO: handle eq_rec
    | app (app (app nat_rec _ _ _) _ z _) _ _ _, zero =>
      eval z
    | app (app (app nat_rec _ m _) _ _ _) _ g (ℕ ⇨ γ), app succ (ℕ ⇨ ℕ) n ℕ =>
      eval (app (app g (ℕ ⇨ γ) n ℕ) (sub n γ) (app f' φ n ℕ) (app m (ℕ ⇨ 𝒰) n ℕ))
    | x, a' =>
      app x (eval φ) a' (eval α)
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

/-- Equality, where cumulative universes are considered equal -/
def cumeq a a' :=
  (a == 𝒰 && a' == 𝒰₁) || a == eval a'

/-- Only pass in trusted input for the second term! -/
def check (env : List Term) : Term → Term → Bool
  | var x, α =>
    if _ : x < env.length then
      -- If `α == 𝒰₁`, then we must have previously ran `check env α 𝒰₁` (ACTUALLY THIS MIGHT BE UNSOUND)
      -- The types in `env` have not been `eval`ed so we need to do that here
      α == 𝒰₁ || cumeq (eval env[x]) α
    else
      false
  | lam b β, α ⇨ β' =>
    check (incr <$> (α :: env)) b β && eval β == eval β'
  | app f (α ⇨ β) a α', β' =>
    check env f (α ⇨ β) && check env a α && eval α == eval α' && cumeq (eval (sub a β)) β'
  | α ⇨ β, typ u =>
    check env α (typ u) && check (incr <$> (α :: env)) β (typ u)
  | prod α β, typ u =>
    -- Dependent products are special so we use `α ⇨ 𝒰` instead of `typ u`
    check env α (typ u) && check env β (α ⇨ 𝒰)
  | sum α β, typ u =>
    check env α (typ u) && check env β (typ u)
  | eq a a' α, typ u =>
    check env a α && check env a' α && check env α (typ u)
  | t, τ =>
    cumeq t.btype τ

-- A few test cases
#guard check [] pmk.btype 𝒰₁

#guard check [] prod_rec.btype 𝒰₁

#guard check [] inl.btype 𝒰₁

#guard check [] inr.btype 𝒰₁

#guard check [] sum_rec.btype 𝒰₁

#guard check [] refl.btype 𝒰₁

#guard check [] eq_rec.btype 𝒰₁

#guard check [] nat_rec.btype 𝒰₁

#guard check [] fls_rec.btype 𝒰₁

/-- User-facing type checker -/
def ch (p : Term × Term) :=
  let t := dbify [] p.1
  let τ := dbify [] p.2
  check [] τ 𝒰₁ && check [] t τ

/-- Apply built-in function -/
def apb f := ap f f.btype

/-
## Exporting proofs

The type checker itself is simple enough to be easily ported to other programming languages, so we provide a way to export proofs in an s-exp format for parsing by external checkers.
-/

/-- Serialize term to s-exp -/
def Term.toString : Term → String
  | var x => s!"(0n {x})"
  | lam b β => s!"(1n {toString b} {toString β})"
  | app f φ a α => s!"(2n {toString f} {toString φ} {toString a} {toString α})"
  | typ u => s!"(3n {u})"
  | fn α β => s!"(4n {toString α} {toString β})"
  | prod α β => s!"(5n {toString α} {toString β})"
  | pmk => "(6n)"
  | prod_rec => "(7n)"
  | sum α β => s!"(8n {toString α} {toString β})"
  | inl => "(9n)"
  | inr => "(10n)"
  | sum_rec => "(11n)"
  | eq a a' α => s!"(12n {toString a} {toString a'} {toString α})"
  | refl => "(13n)"
  | eq_rec => "(14n)"
  | nat => "(15n)"
  | zero => "(16n)"
  | succ => "(17n)"
  | nat_rec => "(18n)"
  | unit => "(19n)"
  | intro => "(20n)"
  | fls => "(21n)"
  | fls_rec => "(22n)"
  | _ => panic "You should call dbify before using toString!"

/-- Serialize a term-type pair -/
def serialize (p : Term × Term) :=
  s!"'({dbify [] p.1 |>.toString} . {dbify [] p.2 |>.toString})"

/-
## Proving some stuff

Now let's do some math!
-/

/-- A → A -/
def a_imp_a := la'
  ’a
  (α◆𝒰 ⇨ a◆’α ⇨ ’α)
  2

#guard ch a_imp_a

/-- A → B → A ∧ B -/
def a_imp_b_imp_ab := la'
  (apb pmk [’α, la ’β (’α ⇨ 𝒰) 1])
  (α◆𝒰 ⇨ β◆𝒰 ⇨ ’α ⇨ ’β ⇨ prod ’α (la ’β (’α ⇨ 𝒰) 1))
  2

#guard ch a_imp_b_imp_ab

/-- A → B → B ∧ A -/
def a_imp_b_imp_ba := la'
  (apb pmk [’β, la ’α (’β ⇨ 𝒰) 1, ’b, ’a])
  (α◆𝒰 ⇨ β◆𝒰 ⇨ a◆’α ⇨ b◆’β ⇨ prod ’β (la ’α (’β ⇨ 𝒰) 1))
  4

#guard ch a_imp_b_imp_ba

/-- Get first element of product -/
def fst := la'
  (apb prod_rec [’α, ’β, la ’α (prod ’α ’β ⇨ 𝒰) 1, la ’a (a◆’α ⇨ (ap ’β (’α ⇨ 𝒰) [’a]) ⇨ ’α) 2, ’p])
  (α◆𝒰 ⇨ β◆(’α ⇨ 𝒰) ⇨ p◆(prod ’α ’β) ⇨ ’α)
  3

#guard ch fst

/-- ¬(A ∨ B) → ¬A -/
def not_ab_imp_not_a := la'
  (ap ’f (sum ’α ’β ⇨ ⊥) [apb inl [’α, ’β, ’a]])
  (α◆𝒰 ⇨ β◆𝒰 ⇨ f◆(sum ’α ’β ⇨ ⊥) ⇨ a◆’α ⇨ ⊥)
  4

#guard ch not_ab_imp_not_a

/-- A → ¬¬A -/
def a_imp_not_not_a := la'
  (ap ’f (’α ⇨ ⊥) [’a])
  (α◆𝒰 ⇨ a◆’α ⇨ f◆(’α ⇨ ⊥) ⇨ ⊥)
  3

#guard ch a_imp_not_not_a

/-- ¬¬¬A → ¬A -/
def not_not_not_a_imp_not_a := la'
  (ap ’f (((’α ⇨ ⊥) ⇨ ⊥) ⇨ ⊥) [la (ap ’f (’α ⇨ ⊥) [’a])
  (f◆(’α ⇨ ⊥) ⇨ ⊥) 1]) (α◆𝒰 ⇨ f◆(((’α ⇨ ⊥) ⇨ ⊥) ⇨ ⊥) ⇨ a◆’α ⇨ ⊥)
  3

#guard ch not_not_not_a_imp_not_a

/-- ∃ n : ℕ, n = 0 -/
def exists_n_eq_zero :=
  (apb pmk [ℕ, la (eq ’n zero ℕ) (n◆ℕ ⇨ 𝒰) 1, zero, apb refl [ℕ, zero]],
    prod ℕ (la (eq ’n zero ℕ) (n◆ℕ ⇨ 𝒰) 1))

#guard ch exists_n_eq_zero

/-- ∀ a : A, ∃ b : A, b = a -/
def forall_a_exists_b_eq_a := la'
  (apb pmk [’α, la (eq ’b ’a ’α) (b◆’α ⇨ 𝒰) 1, ’a, apb refl [’α, ’a]])
  (α◆𝒰 ⇨ a◆’α ⇨ prod ’α (la (eq ’b ’a ’α) (b◆’α ⇨ 𝒰) 1))
  2

#guard ch forall_a_exists_b_eq_a

/-- Convenience wrapper around `succ` -/
def suc n := ap succ (ℕ ⇨ ℕ) [n]

/-- 1 exists (yeah I know this is not super exciting) -/
def one := suc zero

#guard ch (one, ℕ)

/-- 2 exists -/
def two := suc one

#guard ch (two, ℕ)

/-- 4 exists -/
def four := suc (suc two)

#guard ch (four, ℕ)

/-- Addition -/
def add' := la'
  (apb nat_rec [la ℕ (ℕ ⇨ 𝒰) 1, ’n, la (suc ’m) (ℕ ⇨ m◆ℕ ⇨ ℕ) 2])
  (n◆ℕ ⇨ ℕ ⇨ ℕ)
  1

#guard ch add'

def add n m := ap add'.1 add'.2 [n, m]

/-- 0 + 0 = 0 -/
def zero_plus_zero_eq_zero :=
  (apb refl [ℕ, zero],
    eq (add zero zero) zero ℕ)

#guard ch zero_plus_zero_eq_zero

/-- 0 + 1 = 0 -/
def zero_plus_one_eq_one :=
  (apb refl [ℕ, one],
    eq (add zero one) one ℕ)

#guard ch zero_plus_one_eq_one

/-- 2 + 0 = 2 -/
def two_plus_zero_eq_two :=
  (apb refl [ℕ, two],
    eq (add two zero) two ℕ)

#guard ch two_plus_zero_eq_two

/-- 2 + 2 = 4 -/
def two_plus_two_eq_four :=
  (apb refl [ℕ, four],
    eq (add two two) four ℕ)

#guard ch two_plus_two_eq_four

/-- Boolean -/
def bool' := sum unit unit

/-- If statement -/
def if' := la'
  (apb sum_rec [unit, unit, la ’α (bool' ⇨ 𝒰) 1, la ’a (unit ⇨ ’α) 1, la ’a' (unit ⇨ ’α) 1, ’b])
  (α◆𝒰 ⇨ b◆bool' ⇨ a◆’α ⇨ a'◆’α ⇨ ’α)
  4

#guard ch if'

/-- ⊥ implies anything -/
def false_elim := la'
  (apb fls_rec [la ’α (⊥ ⇨ 𝒰) 1])
  (α◆𝒰 ⇨ ⊥ ⇨ ’α)
  1

#guard ch false_elim

/-- Rewrite with an equality -/
def rw := la'
  (apb eq_rec [’α, ’a, la (ap ’p (’α ⇨ 𝒰) [’x]) (x◆’α ⇨ (eq ’a ’x ’α) ⇨ 𝒰) 2, ’ha, ’b, ’h])
  (α◆𝒰 ⇨ a◆’α ⇨ b◆’α ⇨ p◆(’α ⇨ 𝒰) ⇨ h◆(eq ’a ’b ’α) ⇨ ha◆(ap ’p (’α ⇨ 𝒰) [’a]) ⇨ ap ’p (’α ⇨ 𝒰) [’b])
  6

#guard ch rw

/-- n + (m + 1) = (n + m) + 1 -/
def add_one_assoc := la'
  (apb refl [ℕ, add ’n (add ’m one)]) (n◆ℕ ⇨ m◆ℕ ⇨ eq (add ’n (add ’m one))
  (add (add ’n ’m) one) ℕ)
  2

#guard ch add_one_assoc

/-- n = 0 + n -/
def zero_add := la'
  (apb nat_rec [la (eq ’n (add zero ’n) ℕ) (n◆ℕ ⇨ 𝒰) 1, apb refl [ℕ, zero], la
    (ap rw.1 rw.2 [ℕ, ’n, add zero ’n, la (eq (add ’n one) (add ’m one) ℕ) (m◆ℕ ⇨ 𝒰) 1, ’h, apb refl [ℕ, add ’n one]])
  (n◆ℕ ⇨ h◆(eq ’n (add zero ’n) ℕ) ⇨ eq (add ’n one) (add zero (add ’n one)) ℕ) 2, ’n])
  (n◆ℕ ⇨ eq ’n (add zero ’n) ℕ)
  1

#guard ch zero_add

/-- n + 0 = 0 + n -/
def add_zero_eq_zero_add := la'
  (ap zero_add.1 zero_add.2 [’n])
  (n◆ℕ ⇨ eq (add ’n zero) (add zero ’n) ℕ)
  1

#guard ch add_zero_eq_zero_add

/-- n + m = m + n -/
def add_comm := la'
  sorry
  (n◆ℕ ⇨ m◆ℕ ⇨ eq (add ’n ’m) (add ’m ’n) ℕ)
  2

#guard ch add_comm

/-- n + (m + k) = (n + m) + k -/
def add_assoc := la'
  sorry
  (n◆ℕ ⇨ m◆ℕ ⇨ k◆ℕ ⇨ eq (add ’n (add ’m ’k)) (add (add ’n ’m) ’k) ℕ)
  2

#guard ch add_assoc

/-- Multiplication -/
def mul' := la'
  (apb nat_rec [la ℕ (ℕ ⇨ 𝒰) 1, zero, la (add ’n ’m) (ℕ ⇨ m◆ℕ ⇨ ℕ) 2])
  (n◆ℕ ⇨ ℕ ⇨ ℕ)
  1

#guard ch mul'

def mul n m := ap mul'.1 mul'.2 [n, m]

def mul_comm := la'
  sorry
  (n◆ℕ ⇨ m◆ℕ ⇨ eq (mul ’n ’m) (mul ’m ’n) ℕ)
  2

#guard ch mul_comm

/-- 16 exists -/
def sixteen :=
  suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc four)))))))))))

#guard ch (sixteen, ℕ)

/-- 4 × 4 = 16 -/
def four_times_four_eq_sixteen :=
  (apb refl [ℕ, sixteen],
    eq (mul four four) sixteen ℕ)

#guard ch four_times_four_eq_sixteen

/-- Factorial function -/
def fac := la'
  (apb nat_rec [la ℕ (ℕ ⇨ 𝒰) 1, one, la (mul (add one ’n) ’fn)
  (n◆ℕ ⇨ fn◆ℕ ⇨ ℕ) 2, ’n])
  (n◆ℕ ⇨ ℕ)
  1

#guard ch fac

/-- 4 + 2 = 3! -/
def four_plus_two_eq_three_factorial :=
  (apb refl [ℕ, add four two],
    eq (ap fac.1 fac.2 [suc two]) (add four two) ℕ)

#eval ch four_plus_two_eq_three_factorial

/-- Exponentiation -/
def pow' := la'
  (apb nat_rec [la ℕ (ℕ ⇨ 𝒰) 1, one, la (mul ’n ’m)
  (ℕ ⇨ m◆ℕ ⇨ ℕ) 2])
  (n◆ℕ ⇨ ℕ ⇨ ℕ)
  1

#guard ch pow'

def pow n m := ap pow'.1 pow'.2 [n, m]

/-- 2⁴ = 16 -/
def two_to_the_four_eq_sixteen :=
  (apb refl [ℕ, sixteen],
    eq (pow two four) sixteen ℕ)

#guard ch two_to_the_four_eq_sixteen

/-- Fermat's last theorem -/
def fermat := la'
  sorry
  (a◆ℕ ⇨ b◆ℕ ⇨ c◆ℕ ⇨ n◆ℕ ⇨ (eq ’a zero ℕ ⇨ ⊥) ⇨ (eq ’b zero ℕ ⇨ ⊥) ⇨ (eq ’c zero ℕ ⇨ ⊥) ⇨ (eq ’n zero ℕ ⇨ ⊥) ⇨ (eq ’n one ℕ ⇨ ⊥) ⇨ (eq ’n two ℕ ⇨ ⊥) ⇨ eq (add (pow ’a ’n) (pow ’b ’n)) (pow ’c ’n) ℕ ⇨ ⊥)
  10

-- You can skip this one lol
#guard ch fermat
