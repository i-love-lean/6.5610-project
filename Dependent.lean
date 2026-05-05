-- μLean, a very simple proof assistant based on the calculus of constructions!

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
  /-- Type of type of types -/
  | typ1
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
  | typ1 => "'(4n)"
  | fn α β => s!"(list 5n {toString α} {toString β})"
  | prod α β => s!"(list 6n {toString α} {toString β})"
  | pair => "'(7n)"
  | prod_rec => "'(8n)"
  | sum α β => s!"(list 9n {toString α} {toString β})"
  | inl => "'(10n)"
  | inr => "'(11n)"
  | sum_rec => "'(12n)"
  | eq a a' α => s!"(list 13n {toString a} {toString a'} {toString α})"
  | refl => "'(14n)"
  | eq_rec => "'(15n)"
  | nat => "'(16n)"
  | zero => "'(17n)"
  | succ => "'(18n)"
  | nat_rec => "'(19n)"
  | fls => "'(20n)"
  | fls_rec => "'(21n)"
  | _ => panic "You should call dbify before using toString!"

-- instance : ToString Term := ⟨Term.toString⟩

-- instance : ToString (Term × Term) := ⟨fun p ↦ s!"(cons {p.1} {p.2})"⟩

-- `infixr` doesn't work at compile time or something
notation α " ⇨ " β => fn α β -- \hey
notation "𝒰" => typ -- \McU
notation "𝒰₁" => typ1 -- \McU\1
notation "ℕ" => nat -- \N
notation "⊥" => fls -- \bo
-- `max` fixes some precedence issues when parsing
syntax ident "◆" term:max : term -- \di
macro_rules
  | `($s:ident ◆ $t) => `(new $(Lean.Syntax.mkStrLit s.getId.toString) $t)
syntax:max "’" ident : term -- \rq
macro_rules
  | `(’$s:ident) => `(name $(Lean.Syntax.mkStrLit s.getId.toString))

/-- Helper function for recursing over terms -/
def term_rec (s : α) (on_dep : α → α) (on_var : α → Nat → Term) :=
  let rec term_rec' s
  | var x =>
    on_var s x
  | lam b β =>
    lam (term_rec' (on_dep s) b) (term_rec' (on_dep s) β)
  | app f φ a α =>
    app (term_rec' s f) (term_rec' s φ) (term_rec' s a) (term_rec' s α)
  | α ⇨ β =>
    term_rec' s α ⇨ term_rec' (on_dep s) β
  | prod α β =>
    prod (term_rec' s α) (term_rec' (on_dep s) β)
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

/-- Bundle the type with `la` -/
def la' b β n := (la b β n, β)

/-- Substitute `t'` for variable name `s` in a term -/
-- TODO: Is this necessary?
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
    let β' :=
      match α with
      | new s _ => sub' s x β
      | _ => sub x β
    -- TODO: Need to eval both these guys?
    ap (app f (α ⇨ β) x α) β' xs
  | _, _ =>
    f

/-- Convert from variable names to de Bruijn indices -/
def dbify (names : List String) : Term → Term
  | name s =>
    var (names.idxOf? s).get! -- Panicking is usually bad but helpful here for debugging
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
  | prod (new s α) β =>
    prod (dbify names α) (dbify (s :: names) β)
  | prod α β =>
    prod (dbify names α) (dbify ("" :: names) β)
  | sum α β =>
    sum (dbify names α) (dbify names β)
  | eq a a' α =>
    eq (dbify names a) (dbify names a') (dbify names α)
  | t =>
    t

/-- Get type of built-in functions -/
def Term.btype (t : Term) :=
  dbify [] <|
    match t with
    | 𝒰 =>
      𝒰₁
    | pair =>
      α◆𝒰 ⇨ β◆𝒰 ⇨ ’α ⇨ ’β ⇨ prod ’α ’β
    | prod_rec =>
      let μ := prod ’α ’β ⇨ 𝒰
      α◆𝒰 ⇨ β◆𝒰 ⇨ m◆μ ⇨ (a◆’α ⇨ b◆’β ⇨ ap ’m μ [ap pair pair.btype [’α, ’β, ’a, ’b]]) ⇨ p◆(prod ’α ’β) ⇨ ap ’m μ [’p]
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
    | ⊥ =>
      𝒰
    | fls_rec =>
      m◆(⊥ ⇨ 𝒰) ⇨ f◆⊥ ⇨ ap ’m (⊥ ⇨ 𝒰) [’f]
    | _ =>
      t
termination_by
  match t with
  | prod_rec | sum_rec | eq_rec | nat_rec => 1
  | _ => 0

/-- The input should be well-typed or bad things will happen! -/
partial def eval : Term → Term
  | lam b β =>
    lam (eval b) (eval β)
  | app f φ a α =>
    match eval f, eval a with
    | lam b _, a' =>
      eval (sub (incr a') b)
    | app (app (app (app prod_rec _ _ _) _ _ _) _ _ _) _ g γ, app (app (app (app pair _ _ _) _ _ _) _ a _) _ b _ =>
      eval (ap g (eval γ) [a, b])
    | app (app (app (app (app sum_rec _ _ _) _ _ _) _ _ _) _ g γ) _ _ _, app (app (app inl _ _ _) _ _ _) _ a _ =>
      eval (ap g (eval γ) [a])
    | app (app (app (app (app sum_rec _ _ _) _ _ _) _ _ _) _ _ _) _ g γ, app (app (app inr _ _ _) _ _ _) _ b _ =>
      eval (ap g (eval γ) [b])
    | app (app (app nat_rec _ _ _) _ z _) _ _ _, zero =>
      eval z
    | app (app (app nat_rec _ m _) _ z _) _ g γ, app succ _ n _ =>
      eval (ap g (eval γ) [n, ap nat_rec nat_rec.btype [m, z, g, n]])
    | x, a' => app x (eval φ) a' (eval α)
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

/-- Definitional equality -/
-- TODO: is this eval really needed???
def defeq a a' := eval a == eval a'

/-- Definitional equality, where cumulative universes are equal -/
-- TODO: is this eval really needed???
def cumeq a a' :=
  let a'' := eval a
  (a'' == 𝒰 && a' == 𝒰₁) || a'' == eval a'

/-- Only pass in trusted input for the second term! -/
def check (env : List Term) : Term → Term → Bool
  | var x, α =>
    if _ : x < env.length then cumeq env[x] α else false
  | lam b β, α ⇨ β' =>
    defeq β β' && check (incr <$> (α :: env)) b β
  | app f (α ⇨ β) a α', β' =>
    defeq α α' && cumeq (eval (sub a β)) β' && check env f (α ⇨ β) && check env a α
  | α ⇨ β, 𝒰₁
  | prod α β, 𝒰₁ =>
    check env α 𝒰₁ && check (incr <$> (α :: env)) β 𝒰₁
  | sum α β, 𝒰₁ =>
    check env α 𝒰₁ && check env β 𝒰₁
  | eq a a' α, 𝒰₁ =>
    check env a α && check env a' α && check env α 𝒰₁
  | t, τ =>
    cumeq t.btype τ

#guard check [] pair.btype 𝒰₁

#guard check [] prod_rec.btype 𝒰₁

#guard check [] inl.btype 𝒰₁

#guard check [] inr.btype 𝒰₁

#guard check [] sum_rec.btype 𝒰₁

#guard check [] refl.btype 𝒰₁

#eval eq_rec.btype

#guard check [] eq_rec.btype 𝒰₁

#guard check [] nat_rec.btype 𝒰₁

#guard check [] fls_rec.btype 𝒰₁

/-- The type checker! -/
def ch (p : Term × Term) :=
  let t := dbify [] p.1
  let τ := dbify [] p.2
  check [] τ 𝒰₁ && check [] t τ

/-- A → A -/
def a_imp_a := la' ’a (α◆𝒰 ⇨ a◆’α ⇨ ’α) 2

#guard ch a_imp_a

/-- A → B → A ∧ B -/
def a_imp_b_imp_ab := la' (ap pair pair.btype [’α, ’β]) (α◆𝒰 ⇨ β◆𝒰 ⇨ ’α ⇨ ’β ⇨ prod ’α ’β) 2

#guard ch a_imp_b_imp_ab

/-- A → B → B ∧ A -/
def a_imp_b_imp_ba := la' (ap pair pair.btype [’β, ’α, ’b, ’a]) (α◆𝒰 ⇨ β◆𝒰 ⇨ a◆’α ⇨ b◆’β ⇨ prod ’β ’α) 4

#guard ch a_imp_b_imp_ba

/-- Get first element of product -/
def fst := la' (ap prod_rec prod_rec.btype [’α, ’β, la ’α (prod ’α ’β ⇨ 𝒰) 1, la ’a (a◆’α ⇨ ’β ⇨ ’α) 2, ’p]) (α◆𝒰 ⇨ β◆𝒰 ⇨ p◆(prod ’α ’β) ⇨ ’α) 3

#guard ch fst

/-- Get second element of product -/
def snd := la' (ap prod_rec prod_rec.btype [’α, ’β, la ’β (prod ’α ’β ⇨ 𝒰) 1, la ’b (’α ⇨ b◆’β ⇨ ’β) 2, ’p]) (α◆𝒰 ⇨ β◆𝒰 ⇨ p◆(prod ’α ’β) ⇨ ’β) 3

#guard ch snd

/-- A ∧ B → B ∧ A -/
def ab_imp_ba := la' (ap pair pair.btype [’β, ’α, ap snd.1 snd.2 [’α, ’β, ’p], ap fst.1 fst.2 [’α, ’β, ’p]]) (α◆𝒰 ⇨ β◆𝒰 ⇨ p◆(prod ’α ’β) ⇨ prod ’β ’α) 3

#guard ch ab_imp_ba

/-- ¬(A ∨ B) → ¬A -/
def not_ab_imp_not_a := la' (ap ’f (sum ’α ’β ⇨ ⊥) [ap inl inl.btype [’α, ’β, ’a]]) (α◆𝒰 ⇨ β◆𝒰 ⇨ f◆(sum ’α ’β ⇨ ⊥) ⇨ a◆’α ⇨ ⊥) 4

#guard ch not_ab_imp_not_a

/-- A → ¬¬A -/
def a_imp_not_not_a := la' (ap ’f (’α ⇨ ⊥) [’a]) (α◆𝒰 ⇨ a◆’α ⇨ f◆(’α ⇨ ⊥) ⇨ ⊥) 3

#guard ch a_imp_not_not_a

/-- ¬¬¬A → ¬A -/
def not_not_not_a_imp_not_a := la' (ap ’f (((’α ⇨ ⊥) ⇨ ⊥) ⇨ ⊥) [la (ap ’f (’α ⇨ ⊥) [’a]) (f◆(’α ⇨ ⊥) ⇨ ⊥) 1]) (α◆𝒰 ⇨ f◆(((’α ⇨ ⊥) ⇨ ⊥) ⇨ ⊥) ⇨ a◆’α ⇨ ⊥) 3

#guard ch not_not_not_a_imp_not_a

/-- Convenience wrapper around `succ` -/
def succ' n := ap succ (ℕ ⇨ ℕ) [n]

/-- 1 exists (yeah I know this is not super exciting) -/
def one := succ' zero

#guard ch (one, ℕ)

/-- 2 exists -/
def two := succ' one

#guard ch (two, ℕ)

/-- 4 exists -/
def four := succ' (succ' two)

#guard ch (four, ℕ)

/-- Addition -/
def add := la' (ap nat_rec nat_rec.btype [la ℕ (ℕ ⇨ 𝒰) 1, ’n, la (succ' ’m) (ℕ ⇨ m◆ℕ ⇨ ℕ) 2]) (n◆ℕ ⇨ ℕ ⇨ ℕ) 1

#guard ch add

/-- 0 + 0 = 0 -/
def zero_plus_zero_eq_zero := (ap refl refl.btype [ℕ, zero], eq (ap add.1 add.2 [zero, zero]) zero ℕ)

#guard ch zero_plus_zero_eq_zero

/-- 0 + 1 = 0 -/
def zero_plus_one_eq_one := (ap refl refl.btype [ℕ, one], eq (ap add.1 add.2 [zero, one]) one ℕ)

#guard ch zero_plus_one_eq_one

/-- 2 + 0 = 2 -/
def two_plus_zero_eq_two := (ap refl refl.btype [ℕ, two], eq (ap add.1 add.2 [two, zero]) two ℕ)

#guard ch two_plus_zero_eq_two

/-- 2 + 2 = 4 -/
def two_plus_two_eq_four := (ap refl refl.btype [ℕ, four], eq (ap add.1 add.2 [two, two]) four ℕ)

#guard ch two_plus_two_eq_four

def rw := la' (ap eq_rec eq_rec.btype [’α, ’a, la (ap ’p (’α ⇨ 𝒰) [’x]) (x◆’α ⇨ (eq ’a ’x ’α) ⇨ 𝒰) 2]) (α◆𝒰 ⇨ a◆’α ⇨ b◆’α ⇨ p◆(’α ⇨ 𝒰) ⇨ eq ’a ’b ’α ⇨ ap ’p (’α ⇨ 𝒰) [’a] ⇨ ap ’p (’α ⇨ 𝒰) [’b]) 6

#guard ch rw

/-
TODO

n + 0 = 0 + n

n + m = m + n

define mul, exp

state fermat
-/
