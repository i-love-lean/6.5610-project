import Lean.Elab
import Std.Data.ExtHashSet

/-
# μLean

From 0 to √2 is irrational in less than 2000 lines of code! Includes an type checker, syntactic sugar, and lots of example proofs.

μLean's type system is based on the calculus of constructions and very similar to Lean (obviously), but with fewer features to make the implementation simpler. μLean does not have general inductive types and instead has a few hardcoded inductive types such as the natural numbers. Additionally, μLean has cumulative universes rather than noncumulative universes and propositions in μLean live in `Type` instead of a dedicated `Prop` universe, which avoids a lot of Lean's `Prop` weirdness.

## Basic definitions
-/

inductive Term
  -- Lambda calculus stuff
  /-- Variable with de Bruijn index -/
  | var (x : Nat)
  /-- Lambda -/
  | lam (b : Term)
  /-- Function application -/
  | app (f φ a : Term)
  -- Types
  /-- Type universes -/
  | typ (u : Nat)
  /-- Dependent function type -/
  | fn (α β : Term)
  -- Inductive types
  /-- Dependent product type -/
  | prod (α β : Term)
  /-- Constructor for product (pronounced "make", the "p" is silent) -/
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
  /-- Variable with name -/
  | name (s : String)
  /-- Lambda with named variable -/
  | vlam (s : String) (b : Term)
  /-- Dependent function with named first type -/
  | vfn (s : String) (α β : Term)
-- These let us compare terms
deriving BEq, ReflBEq, LawfulBEq, Lean.ToExpr

open Term

/-
## Syntactic sugar

μLean satisfies the de Bruijn criterion, which means that we use Lean as a metalanguage and write proofs in a high-level vernacular that gets desugared down to a low-level AST for the type checker. This keeps the type checker itself simple.
-/

-- Some helpful macros
-- `infixr` doesn't work at compile time or something oof
notation:40 α " ⇨ " β => fn α β -- \hey (stands for \heyting because you will be heyting your life when you write μLean)
notation "𝒰" => typ 0 -- \McU
notation "𝒰₁" => typ 1 -- \McU\1
notation "ℕ" => nat -- \N
notation "⊥" => fls -- \bo
-- Higher precedence than `⇨` but lower precedence than arithmetic
notation:50 n:51 " =ₙ " m:51 => eq n m ℕ -- =\_n P
-- `max` fixes some precedence issues when parsing
syntax ident "◆" term:max " ⇨ " term : term -- \di
macro_rules
  | `($s:ident ◆ $α ⇨ $β) => `(vfn $(Lean.Syntax.mkStrLit s.getId.toString) $α $β)
syntax:max "’" ident : term -- \rq
macro_rules
  | `(’$s:ident) => `(name $(Lean.Syntax.mkStrLit s.getId.toString))

/-- Convenience wrapper around `lam` with currying -/
def la (names : List Term) (b : Term) :=
  match names with
  | name s :: names =>
    vlam s (la names b)
  | _ =>
    b

/-
### Capture-avoiding substitution

The type checker only understands de Bruijn indices, so we have support in the vernacular for variable names for user sanity reasons, which are translated to de Bruijn indices using `dbify`. This means that we have to implement capture-avoiding substitution for the vernacular, while the `sub` function in the type checker is much simpler.

The code below is based on https://courses.cs.cornell.edu/cs3110/2021sp/textbook/interp/lambda-subst/main.ml
-/

/-- Check if a name appears free in a term and not shadowed by a binding -/
def free (s : String) : Term → Bool
  | lam b =>
    free s b
  | app f φ a =>
    free s f || free s φ || free s a
  | α ⇨ β
  | prod α β
  | sum α β =>
    free s α || free s β
  | eq a a' α =>
    free s a || free s a' || free s α
  | name s' =>
    s' == s
  | vlam s' b =>
    s' != s && free s b
  | vfn s' α β =>
    free s α || (s' != s && free s β)
  | _ =>
    false

/-- Generate a name not free in `t` or `t'` -/
def gensym (s : String) (t t' : Term) : Id String := do
  let mut i := 0
  -- This heuristic seems pretty fast in practice
  while let s' := s ++ toString i; free s' t || free s' t' do
    i := i + 1
  return s ++ toString i

/-- Rename free occurrences of `s₁` to `s₂`, respecting scoping -/
def rename (s₁ s₂ : String) : Term → Term
  | lam b =>
    lam (rename s₁ s₂ b)
  | app f φ a =>
    app (rename s₁ s₂ f) (rename s₁ s₂ φ) (rename s₁ s₂ a)
  | α ⇨ β =>
    rename s₁ s₂ α ⇨ rename s₁ s₂ β
  | prod α β =>
    prod (rename s₁ s₂ α) (rename s₁ s₂ β)
  | sum α β =>
    sum (rename s₁ s₂ α) (rename s₁ s₂ β)
  | eq a a' α =>
    eq (rename s₁ s₂ a) (rename s₁ s₂ a') (rename s₁ s₂ α)
  | name s =>
    name (if s == s₁ then s₂ else s)
  | vlam s b =>
    vlam s (if s == s₁ then b else rename s₁ s₂ b)
  | vfn s α β =>
    vfn s (rename s₁ s₂ α) (if s == s₁ then β else rename s₁ s₂ β)
  | t =>
    t

/-- The default `SizeOf` instance is kinda janky and includes string lengths so let's write our own -/
def Term.sizeOf : Term → Nat
  | lam b
  | vlam _ b =>
    1 + b.sizeOf
  | app f φ a =>
    1 + f.sizeOf + φ.sizeOf + a.sizeOf
  | α ⇨ β
  | vfn _ α β
  | prod α β
  | sum α β =>
    1 + α.sizeOf + β.sizeOf
  | eq a a' α =>
    1 + a.sizeOf + a'.sizeOf + α.sizeOf
  | _ =>
    1

/-- `rename` doesn't change the size of a term -/
theorem rename_size (s₁ s₂ t) : t.sizeOf = (rename s₁ s₂ t).sizeOf := by
  induction t <;> grind [rename, Term.sizeOf]

/-- Capture-avoiding substitution of `t'` for variable name `s` -/
def subca (s : String) (t' t : Term) :=
  match t with
  | lam b =>
    lam (subca s t' b)
  | app f φ a =>
    app (subca s t' f) (subca s t' φ) (subca s t' a)
  | α ⇨ β =>
    subca s t' α ⇨ subca s t' β
  | prod α β =>
    prod (subca s t' α) (subca s t' β)
  | sum α β =>
    sum (subca s t' α) (subca s t' β)
  | eq a a' α =>
    eq (subca s t' a) (subca s t' a') (subca s t' α)
  | name s' =>
    if s' == s then t' else name s'
  | vlam s' b =>
    if s' == s then
      vlam s' b
    else if free s' t' then
      let fresh := gensym s b t'
      vlam fresh (subca s t' (rename s' fresh b))
    else
      vlam s' (subca s t' b)
  | vfn s' α β =>
    if s' == s then
      vfn s' (subca s t' α) β
    else if free s' t' then
      let fresh := gensym s β t'
      vfn fresh (subca s t' α) (subca s t' (rename s' fresh β))
    else
      vfn s' (subca s t' α) (subca s t' β)
  | t =>
    t
termination_by t.sizeOf
decreasing_by
  all_goals grind [Term.sizeOf, rename_size]

/-- Convenience wrapper around `app` with currying -/
def ap (f : Term) : Term → List Term → Term
  | α ⇨ β, x :: xs =>
    ap (app f (α ⇨ β) x) β xs
  | vfn s α β, x :: xs =>
    ap (app f (vfn s α β) x) (subca s x β) xs
  | _, _ =>
    f

/-- Apply a function and type pair -/
def ar (p : Term × Term) := ap p.1 p.2

/-- Lambda that returns a constant -/
def const b := la [’unused] b

/-- Convert from variable names to de Bruijn indices -/
def dbify (names : List String) : Term → Term
  | lam b =>
    lam (dbify ("" :: names) b)
  | app f φ a =>
    app (dbify names f) (dbify names φ) (dbify names a)
  | α ⇨ β =>
    dbify names α ⇨ dbify ("" :: names) β
  | prod α β =>
    prod (dbify names α) (dbify names β)
  | sum α β =>
    sum (dbify names α) (dbify names β)
  | eq a a' α =>
    eq (dbify names a) (dbify names a') (dbify names α)
  | name s =>
    -- Panicking is usually bad but helpful here for debugging
    var (names.idxOf? s).get!
  | vlam s b =>
    lam (dbify (s :: names) b)
  | vfn s α β =>
    dbify names α ⇨ dbify (s :: names) β
  | t =>
    t

/-
## Built-in functions

Now that are vernacular is ready, we'll generate the types of the built-in functions such as `pmk` at compile time.
-/

/-- Get type of built-in functions (basically a direct translation of the type signatures of the equivalent functions in Lean) -/
def Term.btype (t : Term) :=
  match t with
  | typ u =>
    typ (u + 1)
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
    -- We use `𝒰₁` instead of `𝒰` to allow for large elimination (used by `succ_ne_zero`)
    let μ := ℕ ⇨ 𝒰₁
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

open Lean Elab Term in
/-- Compute `dbtype` at compile-time -/
elab "precompute_dbtypes" : term => do
  return toExpr <|
    [pmk, prod_rec, inl, inr, sum_rec, refl, eq_rec, ℕ, zero, succ, nat_rec, unit, intro, ⊥, fls_rec].map (dbify [] ·.btype)

def dbtypes := precompute_dbtypes

/-- Yeah I know this is inelegant but idk the dark arts of metaprogramming -/
def Term.dbtype
  | typ u => typ (u + 1)
  | pmk => dbtypes[0]
  | prod_rec => dbtypes[1]
  | inl => dbtypes[2]
  | inr => dbtypes[3]
  | sum_rec => dbtypes[4]
  | refl => dbtypes[5]
  | eq_rec => dbtypes[6]
  | ℕ => dbtypes[7]
  | zero => dbtypes[8]
  | succ => dbtypes[9]
  | nat_rec => dbtypes[10]
  | unit => dbtypes[11]
  | intro => dbtypes[12]
  | ⊥ => dbtypes[13]
  | fls_rec => dbtypes[14]
  | t => name "bad"

/-- Apply built-in function -/
def ab f := ap f f.btype

/-
## The type checker

Time for the fun part!
-/

/-- Helper function for recursing over terms -/
def term_rec (fvar : Nat → Nat → Term) :=
  let rec g d
    | var x =>
      fvar d x
    | lam b =>
      lam (g (d + 1) b)
    | app f φ a =>
      app (g d f) (g d φ) (g d a)
    | α ⇨ β =>
      g d α ⇨ g (d + 1) β
    | prod α β =>
      prod (g d α) (g d β)
    | sum α β =>
      sum (g d α) (g d β)
    | eq a a' α =>
      eq (g d a) (g d a') (g d α)
    | t =>
      t
  g 0

/-- Increment free variables by `k` -/
def incr k :=
  term_rec fun d x ↦ var (if d ≤ x then x + k else x)

/-- Substitute `t'` at index 0 in a term -/
def sub (t' : Term) :=
  term_rec fun d x ↦ if x == d then incr d t' else var (if d < x then x - 1 else x)

/-- The janky evaluator (the input should be well-typed or bad things will happen) -/
partial def eval : Term → Term
  | lam b =>
    lam (eval b)
  | app f φ a =>
    let f' := eval f
    match f', eval a with
    | lam b, a' =>
      eval (sub a' b)
    | app (app (app (app prod_rec _ _) _ _) _ _) ((α ⇨ γ) ⇨ _) g, app (app (app (app pmk _ _) _ _ ) _ a) _ b =>
      eval (app (app g (α ⇨ γ) a) (sub a γ) b)
    | app (app (app (app (app sum_rec _ _) _ _) _ _) (γ ⇨ _) g) _ _, app (app (app inl _ _) _ _) _ a =>
      eval (app g γ a)
    | app (app (app (app (app sum_rec _ _) _ _) _ _) _ _) (γ ⇨ _) g, app (app (app inr _ _) _ _) _ b =>
      eval (app g γ b)
    | app (app (app (app (app eq_rec _ _) _ _) _ _) _ ha) _ _, app (app refl _ _) _ _ =>
      eval ha
    | app (app (app nat_rec _ _) _ z) _ _, zero =>
      eval z
    | app (app (app nat_rec _ _) _ _) ((ℕ ⇨ γ) ⇨ _) g, app succ (ℕ ⇨ ℕ) n =>
      eval (app (app g (ℕ ⇨ γ) n) (sub n γ) (app f' φ n))
    | x, a' =>
      app x (eval φ) a'
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
def cumeq : Term → Term → Bool
  | typ u, typ u' => u ≤ u'
  | a, a' => a == eval a'

/-- And finally, the type checker! (the second input term should be well-typed) -/
partial def check (env : List Term) : Term → Term → Bool
  | var x, α =>
    -- The types in `env` have not been `eval`ed so we need to do that here
    if _ : x < env.length then cumeq (eval (incr (x + 1) env[x])) α else false
  | lam b, α ⇨ β =>
    check (α :: env) b β
  | app f (α ⇨ β) a, β' =>
    check env f (α ⇨ β) && check env a α && cumeq (eval (sub a β)) β'
  | α ⇨ β, typ u =>
    check env α (typ u) && check (α :: env) β (typ u)
  | prod α β, typ u =>
    -- Dependent products are special so we use `α ⇨ 𝒰` instead of `typ u`
    check env α (typ u) && check env β (α ⇨ 𝒰)
  | sum α β, typ u =>
    check env α (typ u) && check env β (typ u)
  | eq a a' α, typ u =>
    check env a α && check env a' α && check env α (typ u)
  | t, τ =>
    -- Try evaluating `τ` to see if it reduces to a matchable form
    let τ' := eval τ
    if τ' != τ then
      check env t τ'
    else
      cumeq t.dbtype τ

-- A few test cases
#guard check [] pmk.dbtype 𝒰₁

#guard check [] prod_rec.dbtype 𝒰₁

#guard check [] inl.dbtype 𝒰₁

#guard check [] inr.dbtype 𝒰₁

#guard check [] sum_rec.dbtype 𝒰₁

#guard check [] refl.dbtype 𝒰₁

#guard check [] eq_rec.dbtype 𝒰₁

#guard check [] nat_rec.dbtype (typ 2)

#guard check [] fls_rec.dbtype 𝒰₁

-- Former soundness bugs
#guard !check [] 𝒰₁ 𝒰₁

#guard !check [] 𝒰₁ 𝒰

#guard !check [] (prod 𝒰 𝒰) (prod 𝒰 𝒰)

/-- User-facing type checker (don't use `check` directly!) -/
def checkuser (p : Term × Term) :=
  let t := dbify [] p.1
  let τ := dbify [] p.2
  -- We don't really care about universes above 2 so just hardcode this for simplicity
  check [] τ (typ 2) && check [] t τ

/-
## Exporting proofs

The type checker itself is simple enough to be easily ported to other programming languages, so we provide a way to export proofs in an s-exp format for parsing by external checkers.
-/

/-- Serialize term to s-exp -/
def Term.toString : Term → String
  | var x => s!"(0n {x})"
  | lam b => s!"(1n {toString b})"
  | app f φ a => s!"(2n {toString f} {toString φ} {toString a})"
  | typ u => s!"(3n {u})"
  | α ⇨ β => s!"(4n {toString α} {toString β})"
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
  | ℕ => "(15n)"
  | zero => "(16n)"
  | succ => "(17n)"
  | nat_rec => "(18n)"
  | unit => "(19n)"
  | intro => "(20n)"
  | ⊥ => "(21n)"
  | fls_rec => "(22n)"
  | _ => panic "You should call dbify before using toString!"

/-- Serialize a term-type pair -/
def serialize (p : Term × Term) :=
  s!"'({dbify [] p.1 |>.toString} . {dbify [] p.2 |>.toString})"

-- Hardcode this into external proof checkers
-- #eval toString <$> dbtypes

/-
## Proving some stuff

Now let's try out μLean and do some math!

### Basic logic
-/

/-- A → A -/
def a_imp_a :=
  (la [’α, ’a] ’a,
    α◆𝒰 ⇨ a◆’α ⇨ ’α)

/-- A → B → A ∧ B -/
def a_imp_b_imp_ab :=
  (la [’α, ’β]
    (ab pmk [’α, const ’β]),
    α◆𝒰 ⇨ β◆𝒰 ⇨ ’α ⇨ ’β ⇨ prod ’α (const ’β))

/-- A → B → B ∧ A -/
def a_imp_b_imp_ba :=
  (la [’α, ’β, ’a, ’b]
    (ab pmk [’β, const ’α, ’b, ’a]),
    α◆𝒰 ⇨ β◆𝒰 ⇨ a◆’α ⇨ b◆’β ⇨ prod ’β (const ’α))

/-- Get first element of product -/
def fst :=
  (la [’α, ’β, ’p]
    (ab prod_rec [
      ’α, ’β, const ’α, la [’a, ’b] ’a, ’p
    ]),
    α◆𝒰 ⇨ β◆(’α ⇨ 𝒰) ⇨ p◆(prod ’α ’β) ⇨ ’α)

/-- ¬(A ∨ B) → ¬A -/
def not_ab_imp_not_a :=
  (la [’α, ’β, ’f, ’a]
    (ap ’f (sum ’α ’β ⇨ ⊥) [
      ab inl [’α, ’β, ’a]
    ]),
    α◆𝒰 ⇨ β◆𝒰 ⇨ f◆(sum ’α ’β ⇨ ⊥) ⇨ a◆’α ⇨ ⊥)

/-- A → ¬¬A -/
def a_imp_not_not_a :=
  (la [’α, ’a, ’f]
    (ap ’f (’α ⇨ ⊥) [’a]),
    α◆𝒰 ⇨ a◆’α ⇨ f◆(’α ⇨ ⊥) ⇨ ⊥)

/-- ¬¬¬A → ¬A -/
def not_not_not_a_imp_not_a :=
  (la [’α, ’f, ’a]
    (ap ’f (((’α ⇨ ⊥) ⇨ ⊥) ⇨ ⊥) [
      la [’f] (ap ’f (’α ⇨ ⊥) [’a])
    ]),
    α◆𝒰 ⇨ f◆(((’α ⇨ ⊥) ⇨ ⊥) ⇨ ⊥) ⇨ a◆’α ⇨ ⊥)

/-- ∀ a : A, ∃ b : A, b = a -/
def forall_a_exists_b_eq_a :=
  (la [’α, ’a]
    (ab pmk [
      ’α, la [’b] (eq ’b ’a ’α), ’a, ab refl [’α, ’a]
    ]),
    α◆𝒰 ⇨ a◆’α ⇨ prod ’α (la [’b] (eq ’b ’a ’α)))

/-- Boolean -/
def bool' := sum unit unit

/-- If statement -/
def if' :=
  (la [’α, ’b, ’a, ’a']
    (ab sum_rec [
      unit, unit, const ’α, const ’a, const ’a', ’b
    ]),
    α◆𝒰 ⇨ b◆bool' ⇨ a◆’α ⇨ a'◆’α ⇨ ’α)

/-- ⊥ implies anything -/
def false_elim :=
  (la [’α]
    (ab fls_rec [const ’α]),
    α◆𝒰 ⇨ ⊥ ⇨ ’α)

/-- Rewrite with an equality -/
def rw :=
  (la [’α, ’a, ’b, ’p, ’h, ’ha]
    (ab eq_rec [
      ’α, ’a,
      la [’x, ’h] (ap ’p (’α ⇨ 𝒰) [’x]),
      ’ha, ’b, ’h
    ]),
    α◆𝒰 ⇨ a◆’α ⇨ b◆’α ⇨ p◆(’α ⇨ 𝒰) ⇨ h◆(eq ’a ’b ’α) ⇨ ha◆(ap ’p (’α ⇨ 𝒰) [’a]) ⇨ ap ’p (’α ⇨ 𝒰) [’b])

/-- a = b → b = a -/
def eq_symm :=
  (la [’α, ’a, ’b, ’h]
    (ab eq_rec [
      ’α, ’a,
      la [’x, ’h] (eq ’x ’a ’α),
      ab refl [’α, ’a], ’b, ’h
    ]),
    α◆𝒰 ⇨ a◆’α ⇨ b◆’α ⇨ h◆(eq ’a ’b ’α) ⇨ eq ’b ’a ’α)

/-- a = b → b = c → a = c -/
def eq_trans :=
  (la [’α, ’a, ’b, ’c, ’hab, ’hbc]
    (ab eq_rec [
      ’α, ’b,
      la [’x, ’h] (eq ’a ’x ’α),
      ’hab, ’c, ’hbc
    ]),
    α◆𝒰 ⇨ a◆’α ⇨ b◆’α ⇨ c◆’α ⇨ hab◆(eq ’a ’b ’α) ⇨ hbc◆(eq ’b ’c ’α) ⇨ eq ’a ’c ’α)

/-
### Natural numbers and arithmetic
-/

instance : Zero Term := ⟨zero⟩

/-- ∃ n : ℕ, n = 0 -/
def exists_n_eq_zero :=
  (ab pmk [
    ℕ, la [’n] (’n =ₙ 0), 0, ab refl [ℕ, 0]
  ],
    prod ℕ (la [’n] (’n =ₙ 0)))

/-- Convenience wrapper around `succ` -/
def suc n := ap succ (ℕ ⇨ ℕ) [n]

/-- 1 exists (yeah I know this is not super exciting) -/
def one := suc 0

instance : One Term := ⟨one⟩

/-- 2 exists -/
def two := suc 1

/-- 4 exists -/
def four := suc (suc two)

/-- Addition -/
def add' :=
  (la [’n]
    (ab nat_rec [
      const ℕ, ’n, la [’k, ’m] (suc ’m)
    ]),
    n◆ℕ ⇨ ℕ ⇨ ℕ)

def add n m := ar add' [n, m]

instance : Add Term := ⟨add⟩

/-- 0 + 0 = 0 -/
def zero_plus_zero_eq_zero :=
  (ab refl [ℕ, 0],
    0 + 0 =ₙ 0)

/-- 0 + 1 = 0 -/
def zero_plus_one_eq_one :=
  (ab refl [ℕ, 1],
    0 + 1 =ₙ 1)

/-- 2 + 2 = 4 -/
def two_plus_two_eq_four :=
  (ab refl [ℕ, four],
    two + two =ₙ four)

/-- n = m → suc n = suc m -/
def cong_suc :=
  (la [’n, ’m, ’h]
    (ar rw [
      ℕ, ’n, ’m,
      la [’x] (suc ’n =ₙ suc ’x),
      ’h, ab refl [ℕ, suc ’n]
    ]),
    n◆ℕ ⇨ m◆ℕ ⇨ h◆(’n =ₙ ’m) ⇨ suc ’n =ₙ suc ’m)

/-- n = m → k + n = k + m -/
def cong_add_l :=
  (la [’n, ’m, ’k, ’h]
    (ar rw [
      ℕ, ’n, ’m,
      la [’x] (’k + ’n =ₙ ’k + ’x),
      ’h, ab refl [ℕ, ’k + ’n]
    ]),
    n◆ℕ ⇨ m◆ℕ ⇨ k◆ℕ ⇨ h◆(’n =ₙ ’m) ⇨ ’k + ’n =ₙ ’k + ’m)

/-- n = m → n + k = m + k -/
def cong_add_r :=
  (la [’n, ’m, ’k, ’h]
    (ar rw [
      ℕ, ’n, ’m,
      la [’x] (’n + ’k =ₙ ’x + ’k),
      ’h, ab refl [ℕ, ’n + ’k]
    ]),
    n◆ℕ ⇨ m◆ℕ ⇨ k◆ℕ ⇨ h◆(’n =ₙ ’m) ⇨ ’n + ’k =ₙ ’m + ’k)

/-- n = 0 + n -/
def zero_add :=
  (la [’n]
    (ab nat_rec [
      la [’n] (’n =ₙ 0 + ’n), ab refl [ℕ, 0],
      la [’n, ’h]
        (ar rw [
          ℕ, ’n, 0 + ’n,
          la [’m] (’n + 1 =ₙ ’m + 1),
          ’h, ab refl [ℕ, ’n + 1]
        ]),
      ’n
    ]),
    n◆ℕ ⇨ ’n =ₙ 0 + ’n)

/-- n + 0 = 0 + n -/
def add_zero_eq_zero_add :=
  (la [’n]
    (ar zero_add [’n]),
    n◆ℕ ⇨ ’n + 0 =ₙ 0 + ’n)

/-- succ (m + n) = (succ m) + n -/
def succ_add :=
  (la [’m, ’n]
    (ab nat_rec [
      la [’n] (suc (’m + ’n) =ₙ suc ’m + ’n),
      ab refl [ℕ, suc ’m],
      la [’n, ’h]
        (ar rw [
          ℕ, suc (’m + ’n), suc ’m + ’n,
          la [’x] (suc (suc (’m + ’n)) =ₙ suc ’x),
          ’h, ab refl [ℕ, suc (suc (’m + ’n))]
        ]),
      ’n
    ]),
    m◆ℕ ⇨ n◆ℕ ⇨ suc (’m + ’n) =ₙ suc ’m + ’n)

/-- n + m = m + n -/
def add_comm :=
  (la [’n, ’m]
    (ab nat_rec [
      la [’m] (’n + ’m =ₙ ’m + ’n),
      ar add_zero_eq_zero_add [’n],
      la [’m, ’h]
        (ar rw [
          ℕ, suc (’m + ’n), suc ’m + ’n,
          la [’x] (suc (’n + ’m) =ₙ ’x),
          ar succ_add [’m, ’n],
          ar rw [
            ℕ, ’n + ’m, ’m + ’n,
            la [’x] (suc (’n + ’m) =ₙ suc ’x),
            ’h, ab refl [ℕ, suc (’n + ’m)]
          ]
        ]),
      ’m
    ]),
    n◆ℕ ⇨ m◆ℕ ⇨ ’n + ’m =ₙ ’m + ’n)

/-- n + (m + k) = (n + m) + k -/
def add_assoc :=
  (la [’n, ’m, ’k]
    (ab nat_rec [
      la [’k] (’n + (’m + ’k) =ₙ (’n + ’m) + ’k),
      ab refl [ℕ, ’n + ’m],
      la [’k, ’h]
        (ar rw [
          ℕ, ’n + (’m + ’k), (’n + ’m) + ’k,
          la [’x] (suc (’n + (’m + ’k)) =ₙ suc ’x),
          ’h, ab refl [ℕ, suc (’n + (’m + ’k))]
        ]),
      ’k
    ]),
    n◆ℕ ⇨ m◆ℕ ⇨ k◆ℕ ⇨ ’n + (’m + ’k) =ₙ (’n + ’m) + ’k)

/-- Predecessor -/
def pred :=
  (ab nat_rec [const ℕ, 0, la [’n, ’m] ’n],
    n◆ℕ ⇨ ℕ)

/-- Subtraction -/
def subt' :=
  (la [’n]
    (ab nat_rec [
      const ℕ, ’n, la [’k, ’m] (ar pred [’m])
    ]),
    n◆ℕ ⇨ ℕ ⇨ ℕ)

def subt n m := ar subt' [n, m]

instance : Sub Term := ⟨subt⟩

/-- 4 - 2 = 2 -/
def four_minus_two_eq_two :=
  (ab refl [ℕ, two],
    four - two =ₙ two)

/-- 2 - 4 = 0 -/
def two_minus_four_eq_zero :=
  (ab refl [ℕ, 0],
    two - four =ₙ 0)

/-- Multiplication -/
def mul' :=
  (la [’n]
    (ab nat_rec [
      const ℕ, 0, la [’k, ’m] (’n + ’m)
    ]),
    n◆ℕ ⇨ ℕ ⇨ ℕ)

def mul n m := ar mul' [n, m]

instance : Mul Term := ⟨mul⟩

/-- 16 exists -/
def sixteen :=
  suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc four)))))))))))

/-- 4 * 4 = 16 -/
def four_times_four_eq_sixteen :=
  (ab refl [ℕ, sixteen],
    four * four =ₙ sixteen)

/-- 0 * n = 0 -/
def zero_mul :=
  (la [’n]
    (ab nat_rec [
      la [’n] (0 * ’n =ₙ 0),
      ab refl [ℕ, 0],
      la [’n, ’h]
        (ar rw [
          ℕ, 0, 0 * ’n,
          la [’m] (0 + ’m =ₙ 0),
          ar eq_symm [ℕ, 0 * ’n, 0, ’h], ab refl [ℕ, 0]
        ]),
      ’n
    ]),
    n◆ℕ ⇨ 0 * ’n =ₙ 0)

/-- (succ m) * n = n + m * n -/
def succ_mul :=
  (la [’m, ’n]
    (ab nat_rec [
      la [’n] (suc ’m * ’n =ₙ ’n + ’m * ’n),
      ab refl [ℕ, 0],
      la [’n, ’ih]
        (ar eq_trans [
          ℕ, suc ’m + (suc ’m * ’n),
          suc ’m + (’n + ’m * ’n),
          suc ’n + (’m + ’m * ’n),
          ar cong_add_l [
            suc ’m * ’n, ’n + ’m * ’n, suc ’m, ’ih
          ],
          ar eq_trans [
            ℕ, suc ’m + (’n + ’m * ’n),
            (suc ’m + ’n) + ’m * ’n,
            suc ’n + (’m + ’m * ’n),
            ar add_assoc [suc ’m, ’n, ’m * ’n],
            ar eq_trans [
              ℕ, (suc ’m + ’n) + ’m * ’n,
              suc (’m + ’n) + ’m * ’n,
              suc ’n + (’m + ’m * ’n),
              ar cong_add_r [
                suc ’m + ’n, suc (’m + ’n), ’m * ’n,
                ar eq_symm [
                  ℕ, suc (’m + ’n), suc ’m + ’n, ar succ_add [’m, ’n]
                ]
              ],
              ar eq_trans [
                ℕ, suc (’m + ’n) + ’m * ’n,
                suc (’n + ’m) + ’m * ’n,
                suc ’n + (’m + ’m * ’n),
                ar cong_add_r [
                  suc (’m + ’n), suc (’n + ’m), ’m * ’n,
                  ar cong_suc [
                    ’m + ’n, ’n + ’m, ar add_comm [’m, ’n]
                  ]
                ],
                ar eq_trans [
                  ℕ, suc (’n + ’m) + ’m * ’n,
                  (suc ’n + ’m) + ’m * ’n,
                  suc ’n + (’m + ’m * ’n),
                  ar cong_add_r [
                    suc (’n + ’m), suc ’n + ’m, ’m * ’n, ar succ_add [’n, ’m]
                  ],
                  ar eq_symm [
                    ℕ, suc ’n + (’m + ’m * ’n),
                    (suc ’n + ’m) + ’m * ’n,
                    ar add_assoc [suc ’n, ’m, ’m * ’n]
                  ]
                ]
              ]
            ]
          ]
        ]),
      ’n
    ]),
    m◆ℕ ⇨ n◆ℕ ⇨ suc ’m * ’n =ₙ ’n + ’m * ’n)

/-- n * m = m * n -/
def mul_comm :=
  (la [’n, ’m]
    (ab nat_rec [
      la [’m] (’n * ’m =ₙ ’m * ’n),
      ar eq_symm [ℕ, 0 * ’n, 0, ar zero_mul [’n]],
      la [’m, ’ih]
        (ar eq_trans [
          ℕ, ’n + ’n * ’m, ’n + ’m * ’n, suc ’m * ’n,
          ar cong_add_l [’n * ’m, ’m * ’n, ’n, ’ih],
          ar eq_symm [
            ℕ, suc ’m * ’n, ’n + ’m * ’n, ar succ_mul [’m, ’n]
          ]
        ]),
      ’m
    ]),
    n◆ℕ ⇨ m◆ℕ ⇨ ’n * ’m =ₙ ’m * ’n)

/-- Factorial function -/
def fac :=
  (la [’n]
    (ab nat_rec [
      const ℕ, 1,
      la [’n, ’nf] ((’n + 1) * ’nf), ’n
    ]),
    n◆ℕ ⇨ ℕ)

/-- 4 + 2 = 3! -/
def four_plus_two_eq_three_factorial :=
  (ab refl [ℕ, four + two],
    ar fac [suc two] =ₙ four + two)

def nat_pair := prod ℕ (const ℕ)

/-- Get second element of `nat_pair` -/
def nat_snd :=
  (la [’p]
    (ab prod_rec [
      ℕ, const ℕ, const ℕ, la [’a, ’b] ’b, ’p
    ]),
    p◆nat_pair ⇨ ℕ)

/-- Fibonacci function -/
def fib :=
  (la [’n]
    (ar fst [
      ℕ, const ℕ,
      ab nat_rec [
        const nat_pair, ab pmk [ℕ, const ℕ, 0, 1],
        la [’n, ’nf]
          (ab pmk [
            ℕ, const ℕ,
            ar nat_snd [’nf],
            ar fst [ℕ, const ℕ, ’nf] + ar nat_snd [’nf]
          ]),
        ’n
      ]
    ]),
    n◆ℕ ⇨ ℕ)

/-- fib (4 + 2) = 4 * 2 -/
def fib_four_plus_two_eq_four_times_two :=
  (ab refl [ℕ, four + four],
    ar fib [four + two] =ₙ four * two)

/-
### Irrationality of √2
-/

/-- Zero is not a successor of any number (uses the large elimination "discriminator trick") -/
def succ_ne_zero :=
  (la [’n, ’h]
    (ar rw [
      ℕ, suc ’n, 0,
      ab nat_rec [const 𝒰, ⊥, la [’k, ’v] unit],
      ’h, intro
    ]),
    n◆ℕ ⇨ h◆(suc ’n =ₙ 0) ⇨ ⊥)

/-- Successor is injective -/
def suc_inj :=
  (la [’n, ’m, ’h]
    (ar rw [
      ℕ, suc ’n, suc ’m,
      la [’x] (’n =ₙ ar pred [’x]),
      ’h, ab refl [ℕ, ’n]
    ]),
    n◆ℕ ⇨ m◆ℕ ⇨ h◆(suc ’n =ₙ suc ’m) ⇨ ’n =ₙ ’m)

/-- even n := ∃ k, n = k + k -/
def even n :=
  prod ℕ (la [’k'] (n =ₙ ’k' + ’k'))

/-- odd n := ∃ k, n = suc (k + k) -/
def odd n :=
  prod ℕ (la [’k'] (n =ₙ suc (’k' + ’k')))

/-- 0 is even -/
def even_zero :=
  (ab pmk [
    ℕ, la [’k] (0 =ₙ ’k + ’k), 0, ab refl [ℕ, 0]
  ],
    even 0)

/-- If n is even, then succ n is odd -/
def even_imp_succ_odd :=
  (la [’n, ’h]
    (ab prod_rec [
      ℕ, la [’k] (’n =ₙ ’k + ’k), const (odd (suc ’n)),
      la [’k, ’hk]
        (ab pmk [
          ℕ, la [’j] (suc ’n =ₙ suc (’j + ’j)), ’k,
          ar cong_suc [’n, ’k + ’k, ’hk]
        ]),
      ’h
    ]),
    n◆ℕ ⇨ even ’n ⇨ odd (suc ’n))

/-- If n is odd, then succ n is even -/
def odd_imp_succ_even :=
  (la [’n, ’h]
    (ab prod_rec [
      ℕ, la [’k] (’n =ₙ suc (’k + ’k)), const (even (suc ’n)),
      la [’k, ’hk]
        (ab pmk [
          ℕ, la [’j] (suc ’n =ₙ ’j + ’j),
          suc ’k,
          ar eq_trans [
            ℕ, suc ’n, suc (suc (’k + ’k)), suc ’k + suc ’k,
            ar cong_suc [’n, suc (’k + ’k), ’hk],
            ar eq_trans [
              ℕ, suc (suc (’k + ’k)), suc (suc ’k + ’k), suc ’k + suc ’k,
              ar cong_suc [suc (’k + ’k), suc ’k + ’k, ar succ_add [’k, ’k]],
              ab refl [ℕ, suc ’k + suc ’k]
            ]
          ]
        ]),
      ’h
    ]),
    n◆ℕ ⇨ odd ’n ⇨ even (suc ’n))

/-- Every number is even or odd -/
def even_or_odd :=
  (la [’n]
    (ab nat_rec [
      la [’n] (sum (even ’n) (odd ’n)),
      ab inl [even 0, odd 0, even_zero.1],
      la [’n, ’ih]
        (ab sum_rec [
          even ’n, odd ’n,
          const (sum (even (suc ’n)) (odd (suc ’n))),
          la [’he] (ab inr [even (suc ’n), odd (suc ’n), ar even_imp_succ_odd [’n, ’he]]),
          la [’ho] (ab inl [even (suc ’n), odd (suc ’n), ar odd_imp_succ_even [’n, ’ho]]),
          ’ih
        ]),
      ’n
    ]),
    n◆ℕ ⇨ sum (even ’n) (odd ’n))

/-- two * n = n + n -/
def mul_two_eq_add :=
  (la [’n]
    (ar mul_comm [two, ’n]),
    n◆ℕ ⇨ two * ’n =ₙ ’n + ’n)

/-- k + k ≠ succ (j + j) -/
def even_ne_odd_base :=
  (la [’k]
    (ab nat_rec [
      la [’k] (j◆ℕ ⇨ ’k + ’k =ₙ suc (’j + ’j) ⇨ ⊥),
      la [’j, ’h]
        (ar succ_ne_zero [
          ’j + ’j,
          ar eq_symm [ℕ, 0 + 0, suc (’j + ’j), ’h]
        ]),
      la [’k, ’ih, ’j, ’h]
        (ap (ab nat_rec [
          la [’j] (’j + ’j =ₙ suc (’k + ’k) ⇨ ⊥),
          la [’hh]
            (ar succ_ne_zero [
              ’k + ’k,
              ar eq_symm [ℕ, 0 + 0, suc (’k + ’k), ’hh]
            ]),
          la [’j2, ’ih2, ’hh]
            (ap ’ih (j◆ℕ ⇨ ’k + ’k =ₙ suc (’j + ’j) ⇨ ⊥) [
              ’j2,
              ar eq_symm [
                ℕ, suc (’j2 + ’j2), ’k + ’k,
                ar eq_trans [
                  ℕ, suc (’j2 + ’j2), suc ’j2 + ’j2, ’k + ’k,
                  ar succ_add [’j2, ’j2],
                  ar suc_inj [suc ’j2 + ’j2, ’k + ’k, ’hh]
                ]
              ]
            ]),
          ’j
        ]) (’j + ’j =ₙ suc (’k + ’k) ⇨ ⊥) [
          ar eq_symm [
            ℕ, suc (’k + ’k), ’j + ’j,
            ar eq_trans [
              ℕ, suc (’k + ’k), suc ’k + ’k, ’j + ’j,
              ar succ_add [’k, ’k],
              ar suc_inj [suc ’k + ’k, ’j + ’j, ’h]
            ]
          ]
        ]),
      ’k
    ]),
    k◆ℕ ⇨ j◆ℕ ⇨ ’k + ’k =ₙ suc (’j + ’j) ⇨ ⊥)

/-- even n → odd n → ⊥ -/
def even_ne_odd :=
  (la [’n, ’he, ’ho]
    (ab prod_rec [
      ℕ, la [’k] (’n =ₙ ’k + ’k), const ⊥,
      la [’k, ’hk]
        (ab prod_rec [
          ℕ, la [’j] (’n =ₙ suc (’j + ’j)), const ⊥,
          la [’j, ’hj]
            (ar even_ne_odd_base [’k, ’j,
              ar eq_trans [
                ℕ, ’k + ’k, ’n, suc (’j + ’j),
                ar eq_symm [ℕ, ’n, ’k + ’k, ’hk],
                ’hj
              ]
            ]),
          ’ho
        ]),
      ’he
    ]),
    n◆ℕ ⇨ even ’n ⇨ odd ’n ⇨ ⊥)

/-- (a + a) * (b + b) = (a + b) + (a + b) -/
def double_sum :=
  (la [’a, ’b]
    (ar eq_symm [
      ℕ,
      (’a + ’b) + (’a + ’b),
      (’a + ’a) + (’b + ’b),
      ar eq_trans [
        ℕ, (’a + ’b) + (’a + ’b),
        ’a + (’b + (’a + ’b)),
        (’a + ’a) + (’b + ’b),
        ar eq_symm [ℕ, ’a + (’b + (’a + ’b)), (’a + ’b) + (’a + ’b),
          ar add_assoc [’a, ’b, ’a + ’b]
        ],
        ar eq_trans [
          ℕ, ’a + (’b + (’a + ’b)),
          ’a + (’a + (’b + ’b)),
          (’a + ’a) + (’b + ’b),
          ar cong_add_l [
            ’b + (’a + ’b), ’a + (’b + ’b), ’a,
            ar eq_trans [
              ℕ, ’b + (’a + ’b),
              (’b + ’a) + ’b,
              ’a + (’b + ’b),
              ar add_assoc [’b, ’a, ’b],
              ar eq_trans [
                ℕ, (’b + ’a) + ’b,
                (’a + ’b) + ’b,
                ’a + (’b + ’b),
                ar cong_add_r [
                  ’b + ’a, ’a + ’b, ’b,
                  ar add_comm [’b, ’a]
                ],
                ar eq_symm [
                  ℕ, ’a + (’b + ’b), (’a + ’b) + ’b,
                  ar add_assoc [’a, ’b, ’b]
                ]
              ]
            ]
          ],
          ar add_assoc [’a, ’a, ’b + ’b]
        ]
      ]
    ]),
    a◆ℕ ⇨ b◆ℕ ⇨ (’a + ’a) + (’b + ’b) =ₙ (’a + ’b) + (’a + ’b))

/-- n + n = m + m → n = m -/
def double_inj :=
  (la [’n]
    (ab nat_rec [
      la [’n] (m◆ℕ ⇨ ’n + ’n =ₙ ’m + ’m ⇨ ’n =ₙ ’m),
      la [’m]
        (ab nat_rec [
          la [’p] (0 + 0 =ₙ ’p + ’p ⇨ 0 =ₙ ’p),
          la [’h] (ab refl [ℕ, 0]),
          la [’p, ’ih2, ’h]
            (ar false_elim [
              0 =ₙ suc ’p,
              ar succ_ne_zero [
                suc ’p + ’p,
                ar eq_symm [ℕ, 0 + 0, suc ’p + suc ’p, ’h]
              ]
            ]),
          ’m
        ]),
      la [’n, ’ih, ’m]
        (ab nat_rec [
          la [’p] (suc ’n + suc ’n =ₙ ’p + ’p ⇨ suc ’n =ₙ ’p),
          la [’h]
            (ar false_elim [
              suc ’n =ₙ 0,
              ar succ_ne_zero [suc ’n + ’n, ’h]
            ]),
          la [’p, ’ih2, ’h]
            (ar cong_suc [
              ’n, ’p,
              ap ’ih (m◆ℕ ⇨ ’n + ’n =ₙ ’m + ’m ⇨ ’n =ₙ ’m) [
                ’p,
                ar suc_inj [
                  ’n + ’n, ’p + ’p,
                  ar eq_trans [
                    ℕ, suc (’n + ’n), suc ’p + ’p, suc (’p + ’p),
                    ar eq_trans [
                      ℕ, suc (’n + ’n), suc ’n + ’n, suc ’p + ’p,
                      ar succ_add [’n, ’n],
                      ar suc_inj [suc ’n + ’n, suc ’p + ’p, ’h]
                    ],
                    ar eq_symm [ℕ, suc (’p + ’p), suc ’p + ’p,
                      ar succ_add [’p, ’p]]
                  ]
                ]
              ]
            ]),
          ’m
        ]),
      ’n
    ]),
    n◆ℕ ⇨ m◆ℕ ⇨ ’n + ’n =ₙ ’m + ’m ⇨ ’n =ₙ ’m)

/-- (a + a) * m is even -/
def mul_even_even :=
  (la [’m, ’a]
    (ab nat_rec [
      la [’a] (even ((’a + ’a) * ’m)),
      ab pmk [
        ℕ, la [’k] (0 * ’m =ₙ ’k + ’k),
        0,
        ar zero_mul [’m]
      ],
      la [’a, ’ih]
        (ab prod_rec [
          ℕ, la [’j] ((’a + ’a) * ’m =ₙ ’j + ’j),
          const (even ((suc ’a + suc ’a) * ’m)),
          la [’j, ’hj]
            (ar rw [
              ℕ, suc (’a + ’a), suc ’a + ’a,
              la [’x] (even (suc ’x * ’m)),
              ar succ_add [’a, ’a],
              ab pmk [
                ℕ, la [’w] (suc (suc (’a + ’a)) * ’m =ₙ ’w + ’w),
                ’m + ’j,
                ar eq_trans [
                  ℕ, suc (suc (’a + ’a)) * ’m,
                  ’m + (’m + (’j + ’j)),
                  (’m + ’j) + (’m + ’j),
                  ar eq_trans [
                    ℕ, suc (suc (’a + ’a)) * ’m,
                    ’m + (suc (’a + ’a) * ’m),
                    ’m + (’m + (’j + ’j)),
                    ar succ_mul [suc (’a + ’a), ’m],
                    ar cong_add_l [
                      suc (’a + ’a) * ’m,
                      ’m + (’j + ’j),
                      ’m,
                      ar eq_trans [
                        ℕ, suc (’a + ’a) * ’m,
                        ’m + ((’a + ’a) * ’m),
                        ’m + (’j + ’j),
                        ar succ_mul [’a + ’a, ’m],
                        ar cong_add_l [
                          (’a + ’a) * ’m, ’j + ’j, ’m, ’hj
                        ]
                      ]
                    ]
                  ],
                  ar eq_trans [
                    ℕ, ’m + (’m + (’j + ’j)),
                    (’m + ’m) + (’j + ’j),
                    (’m + ’j) + (’m + ’j),
                    ar add_assoc [’m, ’m, ’j + ’j],
                    ar double_sum [’m, ’j]
                  ]
                ]
              ]
            ]),
          ’ih
        ]),
      ’a
    ]),
    m◆ℕ ⇨ a◆ℕ ⇨ even ((’a + ’a) * ’m))

/-- odd n → odd (n * n) -/
def odd_sq_odd :=
  (la [’n, ’h]
    (ab prod_rec [
      ℕ, la [’k] (’n =ₙ suc (’k + ’k)), const (odd (’n * ’n)),
      la [’k, ’hk]
        (ar rw [
          ℕ, suc (’k + ’k), ’n,
          la [’x] (odd (’x * ’x)),
          ar eq_symm [ℕ, ’n, suc (’k + ’k), ’hk],
          ab prod_rec [
            ℕ,
            la [’j] ((’k + ’k) * suc (’k + ’k) =ₙ ’j + ’j),
            const (odd (suc (’k + ’k) * suc (’k + ’k))),
            la [’j, ’hj]
              (ab pmk [
                ℕ, la [’w] (suc (’k + ’k) * suc (’k + ’k) =ₙ suc (’w + ’w)),
                ’k + ’j,
                ar eq_trans [
                  ℕ, suc (’k + ’k) * suc (’k + ’k),
                  suc (’k + ’k) + (’j + ’j),
                  suc ((’k + ’j) + (’k + ’j)),
                  ar eq_trans [
                    ℕ, suc (’k + ’k) * suc (’k + ’k),
                    suc (’k + ’k) + (suc (’k + ’k) * (’k + ’k)),
                    suc (’k + ’k) + (’j + ’j),
                    ab refl [ℕ, suc (’k + ’k) + (suc (’k + ’k) * (’k + ’k))],
                    ar cong_add_l [
                      suc (’k + ’k) * (’k + ’k),
                      ’j + ’j,
                      suc (’k + ’k),
                      ar eq_trans [
                        ℕ, suc (’k + ’k) * (’k + ’k),
                        (’k + ’k) * suc (’k + ’k),
                        ’j + ’j,
                        ar mul_comm [suc (’k + ’k), ’k + ’k],
                        ’hj
                      ]
                    ]
                  ],
                  ar eq_trans [
                    ℕ, suc (’k + ’k) + (’j + ’j),
                    suc ((’k + ’k) + (’j + ’j)),
                    suc ((’k + ’j) + (’k + ’j)),
                    ar eq_symm [ℕ, suc ((’k + ’k) + (’j + ’j)),
                      suc (’k + ’k) + (’j + ’j),
                      ar succ_add [’k + ’k, ’j + ’j]],
                    ar cong_suc [
                      (’k + ’k) + (’j + ’j),
                      (’k + ’j) + (’k + ’j),
                      ar double_sum [’k, ’j]
                    ]
                  ]
                ]
              ]),
            ar mul_even_even [suc (’k + ’k), ’k]
          ]
        ]),
      ’h
    ]),
    n◆ℕ ⇨ odd ’n ⇨ odd (’n * ’n))

/-- even (n * n) → even n -/
def even_sq_imp_even :=
  (la [’n, ’h]
    (ab sum_rec [
      even ’n, odd ’n,
      const (even ’n),
      la [’he] ’he,
      la [’ho]
        (ar false_elim [
          even ’n,
          ar even_ne_odd [’n * ’n, ’h, ar odd_sq_odd [’n, ’ho]]
        ]),
      ar even_or_odd [’n]
    ]),
    n◆ℕ ⇨ even (’n * ’n) ⇨ even ’n)

/-- j + d = 0 → j = 0 -/
def add_eq_zero_l :=
  (la [’j, ’d]
    (ab nat_rec [
      la [’x] (’j + ’x =ₙ 0 ⇨ ’j =ₙ 0),
      la [’h] ’h,
      la [’x, ’xr, ’h]
        (ar false_elim [’j =ₙ 0, ar succ_ne_zero [’j + ’x, ’h]]),
      ’d
    ]),
    j◆ℕ ⇨ d◆ℕ ⇨ ’j + ’d =ₙ 0 ⇨ ’j =ₙ 0)

/-- (a * a) + b = (a * b) + (a * b) -/
def double_mul :=
  (la [’a, ’b]
    (ab nat_rec [
      la [’a] ((’a + ’a) * ’b =ₙ ’a * ’b + ’a * ’b),
      ar rw [
        ℕ, 0, 0 * ’b,
        la [’x] (0 * ’b =ₙ ’x + ’x),
        ar eq_symm [ℕ, 0 * ’b, 0, ar zero_mul [’b]],
        ar zero_mul [’b]
      ],
      la [’a, ’ih]
        (ar eq_trans [
          ℕ, (suc ’a + suc ’a) * ’b,
          ’b + (’b + ((’a + ’a) * ’b)),
          suc ’a * ’b + suc ’a * ’b,
          ar eq_trans [
            ℕ, (suc ’a + suc ’a) * ’b,
            ’b + ((suc ’a + ’a) * ’b),
            ’b + (’b + ((’a + ’a) * ’b)),
            ar succ_mul [suc ’a + ’a, ’b],
            ar cong_add_l [
              (suc ’a + ’a) * ’b,
              ’b + ((’a + ’a) * ’b),
              ’b,
              ar eq_trans [
                ℕ, (suc ’a + ’a) * ’b,
                suc (’a + ’a) * ’b,
                ’b + ((’a + ’a) * ’b),
                ar rw [
                  ℕ, suc ’a + ’a, suc (’a + ’a),
                  la [’x] ((suc ’a + ’a) * ’b =ₙ ’x * ’b),
                  ar eq_symm [ℕ, suc (’a + ’a), suc ’a + ’a,
                    ar succ_add [’a, ’a]
                  ],
                  ab refl [ℕ, (suc ’a + ’a) * ’b]
                ],
                ar succ_mul [’a + ’a, ’b]
              ]
            ]
          ],
          ar eq_trans [
            ℕ, ’b + (’b + ((’a + ’a) * ’b)),
            ’b + (’b + (’a * ’b + ’a * ’b)),
            suc ’a * ’b + suc ’a * ’b,
            ar cong_add_l [
              ’b + ((’a + ’a) * ’b),
              ’b + (’a * ’b + ’a * ’b),
              ’b,
              ar cong_add_l [
                (’a + ’a) * ’b, ’a * ’b + ’a * ’b, ’b, ’ih
              ]
            ],
            ar eq_trans [
              ℕ, ’b + (’b + (’a * ’b + ’a * ’b)),
              (’b + ’b) + (’a * ’b + ’a * ’b),
              suc ’a * ’b + suc ’a * ’b,
              ar add_assoc [’b, ’b, ’a * ’b + ’a * ’b],
              ar eq_trans [
                ℕ, (’b + ’b) + (’a * ’b + ’a * ’b),
                (’b + ’a * ’b) + (’b + ’a * ’b),
                suc ’a * ’b + suc ’a * ’b,
                ar double_sum [’b, ’a * ’b],
                ar eq_trans [
                  ℕ, (’b + ’a * ’b) + (’b + ’a * ’b),
                  suc ’a * ’b + (’b + ’a * ’b),
                  suc ’a * ’b + suc ’a * ’b,
                  ar cong_add_r [
                    ’b + ’a * ’b, suc ’a * ’b, ’b + ’a * ’b,
                    ar eq_symm [
                      ℕ, suc ’a * ’b, ’b + ’a * ’b,
                      ar succ_mul [’a, ’b]
                    ]
                  ],
                  ar cong_add_l [
                    ’b + ’a * ’b, suc ’a * ’b, suc ’a * ’b,
                    ar eq_symm [
                      ℕ, suc ’a * ’b, ’b + ’a * ’b,
                      ar succ_mul [’a, ’b]
                    ]
                  ]
                ]
              ]
            ]
          ]
        ]),
      ’a
    ]),
    a◆ℕ ⇨ b◆ℕ ⇨ (’a + ’a) * ’b =ₙ ’a * ’b + ’a * ’b)

/-- From 2n² = (2l)², derive n² = 2l² -/
def sq_half :=
  (la [’n, ’l, ’h]
    (ar eq_trans [
      ℕ, ’n * ’n, ’l * (’l + ’l), ’l * ’l + ’l * ’l,
      ar double_inj [
        ’n * ’n, ’l * (’l + ’l),
        ar eq_trans [
          ℕ, ’n * ’n + ’n * ’n,
          (’l + ’l) * (’l + ’l),
          ’l * (’l + ’l) + ’l * (’l + ’l),
          ar eq_trans [
            ℕ, ’n * ’n + ’n * ’n,
            two * (’n * ’n),
            (’l + ’l) * (’l + ’l),
            ar eq_symm [
              ℕ, two * (’n * ’n), ’n * ’n + ’n * ’n,
              ar mul_two_eq_add [’n * ’n]
            ],
            ’h
          ],
          ar double_mul [’l, ’l + ’l]
        ]
      ],
      ar eq_trans [
        ℕ, ’l * (’l + ’l), (’l + ’l) * ’l,
        ’l * ’l + ’l * ’l,
        ar mul_comm [’l, ’l + ’l],
        ar double_mul [’l, ’l]
      ]
    ]),
    n◆ℕ ⇨ l◆ℕ ⇨ two * (’n * ’n) =ₙ (’l + ’l) * (’l + ’l) ⇨ ’n * ’n =ₙ ’l * ’l + ’l * ’l)

/-- From n² = 2l² and n = 2i, derive 2i² = l² -/
def half_sq :=
  (la [’i, ’l, ’n, ’hnn, ’hn]
    (ar eq_trans [
      ℕ, two * (’i * ’i), ’i * ’i + ’i * ’i, ’l * ’l,
      ar mul_two_eq_add [’i * ’i],
      ar eq_trans [
        ℕ, ’i * ’i + ’i * ’i, (’i + ’i) * ’i, ’l * ’l,
        ar eq_symm [
          ℕ, (’i + ’i) * ’i, ’i * ’i + ’i * ’i,
          ar double_mul [’i, ’i]
        ],
        ar eq_trans [
          ℕ, (’i + ’i) * ’i, ’i * (’i + ’i), ’l * ’l,
          ar mul_comm [’i + ’i, ’i],
          ar double_inj [
            ’i * (’i + ’i), ’l * ’l,
            ar eq_trans [
              ℕ, ’i * (’i + ’i) + ’i * (’i + ’i),
              (’i + ’i) * (’i + ’i),
              ’l * ’l + ’l * ’l,
              ar eq_symm [
                ℕ, (’i + ’i) * (’i + ’i),
                ’i * (’i + ’i) + ’i * (’i + ’i),
                ar double_mul [’i, ’i + ’i]
              ],
              ar rw [
                ℕ, ’n, ’i + ’i,
                la [’x] (’x * ’x =ₙ ’l * ’l + ’l * ’l),
                ’hn, ’hnn
              ]
            ]
          ]
        ]
      ]
    ]),
    i◆ℕ ⇨ l◆ℕ ⇨ n◆ℕ ⇨ ’n * ’n =ₙ ’l * ’l + ’l * ’l ⇨ ’n =ₙ ’i + ’i ⇨ two * (’i * ’i) =ₙ ’l * ’l)

/-- Strong induction lemma for √2 irrationality -/
def strong_sqrt_two :=
  (la [’t]
    (ab nat_rec [
      la [’t] (j◆ℕ ⇨ d◆ℕ ⇨ n◆ℕ ⇨ ’j + ’d =ₙ ’t ⇨ (’j =ₙ 0 ⇨ ⊥) ⇨ two * (’n * ’n) =ₙ ’j * ’j ⇨ ⊥),
      la [’j, ’d, ’n, ’hjd, ’hj, ’h]
        (ap ’hj (’j =ₙ 0 ⇨ ⊥) [
          ar add_eq_zero_l [’j, ’d, ’hjd]
        ]),
      la [’t, ’ih, ’j, ’d, ’n, ’hjd, ’hj, ’h]
        (ap
          (ab nat_rec [
            la [’d2] (’j + ’d2 =ₙ suc ’t ⇨ ⊥),
            la [’hjd0]
              (ab prod_rec [
                ℕ, la [’k'] (’j =ₙ ’k' + ’k'), const ⊥,
                la [’l, ’hl]
                  (ap
                    (ab nat_rec [
                      la [’w] (’j =ₙ ’w + ’w ⇨ ⊥),
                      la [’hlz]
                        (ar succ_ne_zero [
                          ’t,
                          ar eq_trans [
                            ℕ, suc ’t, ’j, 0,
                            ar eq_symm [ℕ, ’j, suc ’t, ’hjd0],
                            ’hlz
                          ]
                        ]),
                      la [’w2, ’recL, ’hlw]
                        (ab prod_rec [
                          ℕ, la [’k'] (’n =ₙ ’k' + ’k'), const ⊥,
                          la [’i, ’hi]
                            (ap ’ih
                              (j◆ℕ ⇨ d◆ℕ ⇨ n◆ℕ ⇨ ’j + ’d =ₙ ’t ⇨ (’j =ₙ 0 ⇨ ⊥) ⇨ two * (’n * ’n) =ₙ ’j * ’j ⇨ ⊥) [
                              suc ’w2, ’w2, ’i,
                              ar suc_inj [
                                suc ’w2 + ’w2, ’t,
                                ar eq_trans [
                                  ℕ, suc ’w2 + suc ’w2, ’j, suc ’t,
                                  ar eq_symm [ℕ, ’j, suc ’w2 + suc ’w2, ’hlw],
                                  ’hjd0
                                ]
                              ],
                              la [’h0] (ar succ_ne_zero [’w2, ’h0]),
                              ar half_sq [
                                ’i, suc ’w2, ’n,
                                ar sq_half [
                                  ’n, suc ’w2,
                                  ar rw [
                                    ℕ, ’j, suc ’w2 + suc ’w2,
                                    la [’x] (two * (’n * ’n) =ₙ ’x * ’x),
                                    ’hlw, ’h
                                  ]
                                ],
                                ’hi
                              ]
                            ]),
                          ar even_sq_imp_even [
                            ’n,
                            ab pmk [
                              ℕ, la [’k'] (’n * ’n =ₙ ’k' + ’k'),
                              suc ’w2 * suc ’w2,
                              ar sq_half [
                                ’n, suc ’w2,
                                ar rw [
                                  ℕ, ’j, suc ’w2 + suc ’w2,
                                  la [’x] (two * (’n * ’n) =ₙ ’x * ’x),
                                  ’hlw, ’h
                                ]
                              ]
                            ]
                          ]
                        ]),
                      ’l
                    ])
                    (’j =ₙ ’l + ’l ⇨ ⊥) [’hl]),
                ar even_sq_imp_even [
                  ’j,
                  ab pmk [
                    ℕ, la [’k'] (’j * ’j =ₙ ’k' + ’k'),
                    ’n * ’n,
                    ar eq_trans [
                      ℕ, ’j * ’j, two * (’n * ’n),
                      ’n * ’n + ’n * ’n,
                      ar eq_symm [
                        ℕ, two * (’n * ’n), ’j * ’j, ’h
                      ],
                      ar mul_two_eq_add [’n * ’n]
                    ]
                  ]
                ]
              ]),
            la [’d2, ’recD, ’hjd2]
              (ap ’ih (j◆ℕ ⇨ d◆ℕ ⇨ n◆ℕ ⇨ ’j + ’d =ₙ ’t ⇨ (’j =ₙ 0 ⇨ ⊥) ⇨ two * (’n * ’n) =ₙ ’j * ’j ⇨ ⊥) [
                ’j, ’d2, ’n,
                ar suc_inj [’j + ’d2, ’t, ’hjd2],
                ’hj, ’h
              ]),
            ’d
          ])
          (’j + ’d =ₙ suc ’t ⇨ ⊥) [’hjd]),
      ’t
    ]),
    t◆ℕ ⇨ j◆ℕ ⇨ d◆ℕ ⇨ n◆ℕ ⇨ ’j + ’d =ₙ ’t ⇨ (’j =ₙ 0 ⇨ ⊥) ⇨ two * (’n * ’n) =ₙ ’j * ’j ⇨ ⊥)

/-- √2 is irrational -/
def sqrt_two_irrational :=
  (la [’n, ’m, ’hm, ’h]
    (ar strong_sqrt_two [
      ’m, ’m, 0, ’n, ab refl [ℕ, ’m], ’hm, ’h
    ]),
    n◆ℕ ⇨ m◆ℕ ⇨ hm◆(’m =ₙ 0 ⇨ ⊥) ⇨ h◆(two * (’n * ’n) =ₙ ’m * ’m) ⇨ ⊥)

/-- Exponentiation -/
def pow' :=
  (la [’n]
    (ab nat_rec [
      const ℕ, 1, la [’k, ’m] (’n * ’m)
    ]),
    n◆ℕ ⇨ ℕ ⇨ ℕ)

def pow n m := ar pow' [n, m]

instance : Pow Term Term := ⟨pow⟩

/-- 2 ^ 4 = 16 -/
def two_to_the_four_eq_sixteen :=
  (ab refl [ℕ, sixteen],
    two ^ four =ₙ sixteen)

/-- Fermat's last theorem -/
def fermat :=
  (name "sorry",
    a◆ℕ ⇨ b◆ℕ ⇨ c◆ℕ ⇨ n◆ℕ ⇨ (’a =ₙ 0 ⇨ ⊥) ⇨ (’b =ₙ 0 ⇨ ⊥) ⇨ (’c =ₙ 0 ⇨ ⊥) ⇨ (’n =ₙ 0 ⇨ ⊥) ⇨ (’n =ₙ 1 ⇨ ⊥) ⇨ (’n =ₙ two ⇨ ⊥) ⇨ ’a ^ ’n + ’b ^ ’n =ₙ ’c ^ ’n ⇨ ⊥)

def tests := Std.HashMap.ofList [
  ("a_imp_a", a_imp_a),
  ("a_imp_b_imp_ab", a_imp_b_imp_ab),
  ("a_imp_b_imp_ba", a_imp_b_imp_ba),
  ("not_ab_imp_not_a", not_ab_imp_not_a),
  ("a_imp_not_not_a", a_imp_not_not_a),
  ("not_not_not_a_imp_not_a", not_not_not_a_imp_not_a),
  ("forall_a_exists_b_eq_a", forall_a_exists_b_eq_a),
  ("if'", if'),
  ("false_elim", false_elim),
  ("rw", rw),
  ("eq_symm", eq_symm),
  ("eq_trans", eq_trans),
  ("exists_n_eq_zero", exists_n_eq_zero),
  ("add'", add'),
  ("zero_plus_zero_eq_zero", zero_plus_zero_eq_zero),
  ("zero_plus_one_eq_one", zero_plus_one_eq_one),
  ("two_plus_two_eq_four", two_plus_two_eq_four),
  ("add_zero_eq_zero_add", add_zero_eq_zero_add),
  ("succ_add", succ_add),
  ("add_comm", add_comm),
  ("add_assoc", add_assoc),
  ("pred", pred),
  ("subt'", subt'),
  ("four_minus_two_eq_two", four_minus_two_eq_two),
  ("two_minus_four_eq_zero", two_minus_four_eq_zero),
  ("mul'", mul'),
  ("four_times_four_eq_sixteen", four_times_four_eq_sixteen),
  ("succ_mul", succ_mul),
  ("mul_comm", mul_comm),
  ("fac", fac),
  ("four_plus_two_eq_three_factorial", four_plus_two_eq_three_factorial),
  ("fib", fib),
  ("fib_four_plus_two_eq_four_times_two", fib_four_plus_two_eq_four_times_two),
  ("succ_ne_zero", succ_ne_zero),
  ("sqrt_two_irrational", sqrt_two_irrational),
  ("pow'", pow'),
  ("two_to_the_four_eq_sixteen", two_to_the_four_eq_sixteen),
]

def run_test (name : String) (tpair : Term × Term) : IO Unit := do
  let start ← IO.monoNanosNow
  let res := if checkuser tpair then "✅" else "❌"
  IO.println s!"{res} {name} {((← IO.monoNanosNow) - start) / 1000}μs"

def main (args : List String) : IO Unit := do
  if h : 0 < args.length then
    if h : args[0] ∈ tests then
      run_test args[0] tests[args[0]]
    else
      IO.println s!"Test {args[0]} not found"
  else
    tests.forM run_test
