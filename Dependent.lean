import Lean.Elab
import Std.Data.ExtHashSet

/-
# μLean

A very simple proof assistant in 1000 lines of code!

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
notation α " ⇨ " β => fn α β -- \hey (stands for \heyting because you will be heyting your life when you write μLean)
notation "𝒰" => typ 0 -- \McU
notation "𝒰₁" => typ 1 -- \McU\1
notation "ℕ" => nat -- \N
notation "⊥" => fls -- \bo
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

/-- Collect all names used in a term -/
def names : Term → Std.ExtHashSet String
  | lam b =>
    names b
  | app f φ a =>
    names f ∪ names φ ∪ names a
  | α ⇨ β
  | prod α β
  | sum α β =>
    names α ∪ names β
  | eq a a' α =>
    names a ∪ names a' ∪ names α
  | name s =>
    {s}
  | vlam s b =>
    {s} ∪ names b
  | vfn s α β =>
    {s} ∪ names α ∪ names β
  | _ =>
    ∅

/-- Generate a name not in a set -/
def gensym (S : Std.ExtHashSet String) := Id.run do
  for i in List.range (S.size + 1) do
    if toString i ∉ S then
      return toString i
  return ""

open Std Do ExtHashSet in
/-- `gensym` returns a string not in its input set -/
theorem gensym_correct : gensym S ∉ S := by
  generalize h : gensym S = x
  apply Id.of_wp_run_eq h
  mvcgen invariants
  · Invariant.withEarlyReturn
      (onReturn := fun ret _ ↦ ⌜ret ∉ S⌝)
      (onContinue := fun xs _ ↦ ⌜∀ i < xs.prefix.length, toString i ∈ S⌝)
  with (expose_names; try grind)
  · left
    simp_all
    intro i hi
    by_cases h : i = pref.length
    · grind [congrArg (·[pref.length]?) h_1]
    · exact h_3.2 i (by grind)
  · let T := List.range (List.range (S.size + 1) |>.length) |>.map toString
    have : S ∪ ofList T = S := by
      ext i -- This is why we need `ExtHashSet` instead of just `HashSet`
      constructor
      · simp_all
        grind
      · simp_all
    have : (ofList T).size = T.length := size_ofList (by simp [List.pairwise_iff_getElem, T]; grind)
    grind [size_right_le_size_union]

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
      let fresh := gensym (names t' ∪ names b ∪ {s})
      vlam fresh (subca s t' (rename s' fresh b))
    else
      vlam s' (subca s t' b)
  | vfn s' α β =>
    if s' == s then
      vfn s' (subca s t' α) β
    else if free s' t' then
      let fresh := gensym (names β ∪ names t' ∪ {s})
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
def apr (p : Term × Term) := ap p.1 p.2

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
def apb f := ap f f.btype

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

/-- User-facing type checker -/
def ch (p : Term × Term) :=
  let t := dbify [] p.1
  let τ := dbify [] p.2
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
#eval toString <$> dbtypes

/-
## Proving some stuff

Now let's try out μLean and do some math!
-/

/-- A → A -/
def a_imp_a :=
  (la [’α, ’a] ’a,
    α◆𝒰 ⇨ a◆’α ⇨ ’α)

/-- A → B → A ∧ B -/
def a_imp_b_imp_ab :=
  (la [’α, ’β]
    (apb pmk [’α, const ’β]),
    α◆𝒰 ⇨ β◆𝒰 ⇨ ’α ⇨ ’β ⇨ prod ’α (const ’β))

/-- A → B → B ∧ A -/
def a_imp_b_imp_ba :=
  (la [’α, ’β, ’a, ’b]
    (apb pmk [’β, const ’α, ’b, ’a]),
    α◆𝒰 ⇨ β◆𝒰 ⇨ a◆’α ⇨ b◆’β ⇨ prod ’β (const ’α))

/-- Get first element of product -/
def fst :=
  (la [’α, ’β, ’p]
    (apb prod_rec [
      ’α, ’β, const ’α, la [’a, ’b] ’a, ’p
    ]),
    α◆𝒰 ⇨ β◆(’α ⇨ 𝒰) ⇨ p◆(prod ’α ’β) ⇨ ’α)

/-- ¬(A ∨ B) → ¬A -/
def not_ab_imp_not_a :=
  (la [’α, ’β, ’f, ’a]
    (ap ’f (sum ’α ’β ⇨ ⊥) [
      apb inl [’α, ’β, ’a]
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

/-- ∃ n : ℕ, n = 0 -/
def exists_n_eq_zero :=
  (apb pmk [
    ℕ, la [’n] (eq ’n zero ℕ), zero, apb refl [ℕ, zero]
  ],
    prod ℕ (la [’n] (eq ’n zero ℕ)))

/-- ∀ a : A, ∃ b : A, b = a -/
def forall_a_exists_b_eq_a :=
  (la [’α, ’a]
    (apb pmk [
      ’α, la [’b] (eq ’b ’a ’α), ’a, apb refl [’α, ’a]
    ]),
    α◆𝒰 ⇨ a◆’α ⇨ prod ’α (la [’b] (eq ’b ’a ’α)))

/-- Convenience wrapper around `succ` -/
def suc n := ap succ (ℕ ⇨ ℕ) [n]

/-- 1 exists (yeah I know this is not super exciting) -/
def one := suc zero

/-- 2 exists -/
def two := suc one

/-- 4 exists -/
def four := suc (suc two)

/-- Addition -/
def add' :=
  (la [’n]
    (apb nat_rec [
      const ℕ, ’n, la [’k, ’m] (suc ’m)
    ]),
    n◆ℕ ⇨ ℕ ⇨ ℕ)

def add n m := apr add' [n, m]

/-- 0 + 0 = 0 -/
def zero_plus_zero_eq_zero :=
  (apb refl [ℕ, zero],
    eq (add zero zero) zero ℕ)

/-- 0 + 1 = 0 -/
def zero_plus_one_eq_one :=
  (apb refl [ℕ, one],
    eq (add zero one) one ℕ)

/-- 2 + 2 = 4 -/
def two_plus_two_eq_four :=
  (apb refl [ℕ, four],
    eq (add two two) four ℕ)

/-- Boolean -/
def bool' := sum unit unit

/-- If statement -/
def if' :=
  (la [’α, ’b, ’a, ’a']
    (apb sum_rec [
      unit, unit, const ’α, const ’a, const ’a', ’b
    ]),
    α◆𝒰 ⇨ b◆bool' ⇨ a◆’α ⇨ a'◆’α ⇨ ’α)

/-- ⊥ implies anything -/
def false_elim :=
  (la [’α]
    (apb fls_rec [const ’α]),
    α◆𝒰 ⇨ ⊥ ⇨ ’α)

/-- Rewrite with an equality -/
def rw :=
  (la [’α, ’a, ’b, ’p, ’h, ’ha]
    (apb eq_rec [
      ’α, ’a,
      la [’x, ’h] (ap ’p (’α ⇨ 𝒰) [’x]),
      ’ha, ’b, ’h
    ]),
    α◆𝒰 ⇨ a◆’α ⇨ b◆’α ⇨ p◆(’α ⇨ 𝒰) ⇨ h◆(eq ’a ’b ’α) ⇨ ha◆(ap ’p (’α ⇨ 𝒰) [’a]) ⇨ ap ’p (’α ⇨ 𝒰) [’b])

/-- a = b → b = a -/
def eq_symm :=
  (la [’α, ’a, ’b, ’h]
    (apb eq_rec [
      ’α, ’a,
      la [’x, ’h] (eq ’x ’a ’α),
      apb refl [’α, ’a], ’b, ’h
    ]),
    α◆𝒰 ⇨ a◆’α ⇨ b◆’α ⇨ h◆(eq ’a ’b ’α) ⇨ eq ’b ’a ’α)

/-- a = b → b = c → a = c -/
def eq_trans :=
  (la [’α, ’a, ’b, ’c, ’hab, ’hbc]
    (apb eq_rec [
      ’α, ’b,
      la [’x, ’h] (eq ’a ’x ’α),
      ’hab, ’c, ’hbc
    ]),
    α◆𝒰 ⇨ a◆’α ⇨ b◆’α ⇨ c◆’α ⇨ hab◆(eq ’a ’b ’α) ⇨ hbc◆(eq ’b ’c ’α) ⇨ eq ’a ’c ’α)

/-- n = m → suc n = suc m -/
def cong_suc :=
  (la [’n, ’m, ’h]
    (apr rw [
      ℕ, ’n, ’m,
      la [’x] (eq (suc ’n) (suc ’x) ℕ),
      ’h, apb refl [ℕ, suc ’n]
    ]),
    n◆ℕ ⇨ m◆ℕ ⇨ h◆(eq ’n ’m ℕ) ⇨ eq (suc ’n) (suc ’m) ℕ)

/-- n = m → k + n = k + m -/
def cong_add_l :=
  (la [’n, ’m, ’k, ’h]
    (apr rw [
      ℕ, ’n, ’m,
      la [’x] (eq (add ’k ’n) (add ’k ’x) ℕ),
      ’h, apb refl [ℕ, add ’k ’n]
    ]),
    n◆ℕ ⇨ m◆ℕ ⇨ k◆ℕ ⇨ h◆(eq ’n ’m ℕ) ⇨ eq (add ’k ’n) (add ’k ’m) ℕ)

/-- n = m → n + k = m + k -/
def cong_add_r :=
  (la [’n, ’m, ’k, ’h]
    (apr rw [
      ℕ, ’n, ’m,
      la [’x] (eq (add ’n ’k) (add ’x ’k) ℕ),
      ’h, apb refl [ℕ, add ’n ’k]
    ]),
    n◆ℕ ⇨ m◆ℕ ⇨ k◆ℕ ⇨ h◆(eq ’n ’m ℕ) ⇨ eq (add ’n ’k) (add ’m ’k) ℕ)

/-- n = 0 + n -/
def zero_add :=
  (la [’n]
    (apb nat_rec [
      la [’n] (eq ’n (add zero ’n) ℕ), apb refl [ℕ, zero],
      la [’n, ’h]
        (apr rw [
          ℕ, ’n, add zero ’n,
          la [’m] (eq (add ’n one) (add ’m one) ℕ),
          ’h, apb refl [ℕ, add ’n one]
        ]),
      ’n
    ]),
    n◆ℕ ⇨ eq ’n (add zero ’n) ℕ)

/-- n + 0 = 0 + n -/
def add_zero_eq_zero_add :=
  (la [’n]
    (apr zero_add [’n]),
    n◆ℕ ⇨ eq (add ’n zero) (add zero ’n) ℕ)

/-- succ (m + n) = (succ m) + n -/
def succ_add :=
  (la [’m, ’n]
    (apb nat_rec [
      la [’n] (eq (suc (add ’m ’n)) (add (suc ’m) ’n) ℕ),
      apb refl [ℕ, suc ’m],
      la [’n, ’h]
        (apr rw [
          ℕ, suc (add ’m ’n), add (suc ’m) ’n,
          la [’x] (eq (suc (suc (add ’m ’n))) (suc ’x) ℕ),
          ’h, apb refl [ℕ, suc (suc (add ’m ’n))]
        ]),
      ’n
    ]),
    m◆ℕ ⇨ n◆ℕ ⇨ eq (suc (add ’m ’n)) (add (suc ’m) ’n) ℕ)

/-- n + m = m + n -/
def add_comm :=
  (la [’n, ’m]
    (apb nat_rec [
      la [’m] (eq (add ’n ’m) (add ’m ’n) ℕ),
      apr add_zero_eq_zero_add [’n],
      la [’m, ’h]
        (apr rw [
          ℕ, suc (add ’m ’n), add (suc ’m) ’n,
          la [’x] (eq (suc (add ’n ’m)) ’x ℕ),
          apr succ_add [’m, ’n],
          apr rw [
            ℕ, add ’n ’m, add ’m ’n,
            la [’x] (eq (suc (add ’n ’m)) (suc ’x) ℕ),
            ’h, apb refl [ℕ, suc (add ’n ’m)]
          ]
        ]),
      ’m
    ]),
    n◆ℕ ⇨ m◆ℕ ⇨ eq (add ’n ’m) (add ’m ’n) ℕ)

/-- n + (m + k) = (n + m) + k -/
def add_assoc :=
  (la [’n, ’m, ’k]
    (apb nat_rec [
      la [’k] (eq (add ’n (add ’m ’k)) (add (add ’n ’m) ’k) ℕ),
      apb refl [ℕ, add ’n ’m],
      la [’k, ’h]
        (apr rw [
          ℕ, add ’n (add ’m ’k), add (add ’n ’m) ’k,
          la [’x] (eq (suc (add ’n (add ’m ’k))) (suc ’x) ℕ),
          ’h, apb refl [ℕ, suc (add ’n (add ’m ’k))]
        ]),
      ’k
    ]),
    n◆ℕ ⇨ m◆ℕ ⇨ k◆ℕ ⇨ eq (add ’n (add ’m ’k)) (add (add ’n ’m) ’k) ℕ)

/-- Predecessor -/
def pred :=
  (apb nat_rec [const ℕ, zero, la [’n, ’m] ’n],
    n◆ℕ ⇨ ℕ)

/-- Subtraction -/
def subt :=
  (la [’n]
    (apb nat_rec [
      const ℕ, ’n, la [’k, ’m] (apr pred [’m])
    ]),
    n◆ℕ ⇨ ℕ ⇨ ℕ)

/-- 4 - 2 = 2 -/
def four_minus_two_eq_two :=
  (apb refl [ℕ, two],
    eq (apr subt [four, two]) two ℕ)

/-- 2 - 4 = 0 -/
def two_minus_four_eq_zero :=
  (apb refl [ℕ, zero],
    eq (apr subt [two, four]) zero ℕ)

/-- Multiplication -/
def mul' :=
  (la [’n]
    (apb nat_rec [
      const ℕ, zero, la [’k, ’m] (add ’n ’m)
    ]),
    n◆ℕ ⇨ ℕ ⇨ ℕ)

def mul n m := apr mul' [n, m]

/-- 16 exists -/
def sixteen :=
  suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc four)))))))))))

/-- 4 * 4 = 16 -/
def four_times_four_eq_sixteen :=
  (apb refl [ℕ, sixteen],
    eq (mul four four) sixteen ℕ)

/-- 0 * n = 0 -/
def zero_mul :=
  (la [’n]
    (apb nat_rec [
      la [’n] (eq (mul zero ’n) zero ℕ),
      apb refl [ℕ, zero],
      la [’n, ’h]
        (apr rw [
          ℕ, zero, mul zero ’n,
          la [’m] (eq (add zero ’m) zero ℕ),
          apr eq_symm [ℕ, mul zero ’n, zero, ’h], apb refl [ℕ, zero]
        ]),
      ’n
    ]),
    n◆ℕ ⇨ eq (mul zero ’n) zero ℕ)

/-- (succ m) * n = n + m * n -/
def succ_mul :=
  (la [’m, ’n]
    (apb nat_rec [
      la [’n] (eq (mul (suc ’m) ’n) (add ’n (mul ’m ’n)) ℕ),
      apb refl [ℕ, zero],
      la [’n, ’ih]
        (apr eq_trans [
          ℕ, add (suc ’m) (mul (suc ’m) ’n),
          add (suc ’m) (add ’n (mul ’m ’n)),
          add (suc ’n) (add ’m (mul ’m ’n)),
          apr cong_add_l [
            mul (suc ’m) ’n, add ’n (mul ’m ’n), suc ’m, ’ih
          ],
          apr eq_trans [
            ℕ, add (suc ’m) (add ’n (mul ’m ’n)),
            add (add (suc ’m) ’n) (mul ’m ’n),
            add (suc ’n) (add ’m (mul ’m ’n)),
            apr add_assoc [suc ’m, ’n, mul ’m ’n],
            apr eq_trans [
              ℕ, add (add (suc ’m) ’n) (mul ’m ’n),
              add (suc (add ’m ’n)) (mul ’m ’n),
              add (suc ’n) (add ’m (mul ’m ’n)),
              apr cong_add_r [
                add (suc ’m) ’n, suc (add ’m ’n), mul ’m ’n,
                apr eq_symm [
                  ℕ, suc (add ’m ’n), add (suc ’m) ’n, apr succ_add [’m, ’n]
                ]
              ],
              apr eq_trans [
                ℕ, add (suc (add ’m ’n)) (mul ’m ’n),
                add (suc (add ’n ’m)) (mul ’m ’n),
                add (suc ’n) (add ’m (mul ’m ’n)),
                apr cong_add_r [
                  suc (add ’m ’n), suc (add ’n ’m), mul ’m ’n,
                  apr cong_suc [
                    add ’m ’n, add ’n ’m, apr add_comm [’m, ’n]
                  ]
                ],
                apr eq_trans [
                  ℕ, add (suc (add ’n ’m)) (mul ’m ’n),
                  add (add (suc ’n) ’m) (mul ’m ’n),
                  add (suc ’n) (add ’m (mul ’m ’n)),
                  apr cong_add_r [
                    suc (add ’n ’m), add (suc ’n) ’m, mul ’m ’n, apr succ_add [’n, ’m]
                  ],
                  apr eq_symm [
                    ℕ, add (suc ’n) (add ’m (mul ’m ’n)),
                    add (add (suc ’n) ’m) (mul ’m ’n),
                    apr add_assoc [suc ’n, ’m, mul ’m ’n]
                  ]
                ]
              ]
            ]
          ]
        ]),
      ’n
    ]),
    m◆ℕ ⇨ n◆ℕ ⇨ eq (mul (suc ’m) ’n) (add ’n (mul ’m ’n)) ℕ)

def mul_comm :=
  (la [’n, ’m]
    (apb nat_rec [
      la [’m] (eq (mul ’n ’m) (mul ’m ’n) ℕ),
      apr eq_symm [ℕ, mul zero ’n, zero, apr zero_mul [’n]],
      la [’m, ’ih]
        (apr eq_trans [
          ℕ, add ’n (mul ’n ’m), add ’n (mul ’m ’n), mul (suc ’m) ’n,
          apr cong_add_l [mul ’n ’m, mul ’m ’n, ’n, ’ih],
          apr eq_symm [
            ℕ, mul (suc ’m) ’n, add ’n (mul ’m ’n), apr succ_mul [’m, ’n]
          ]
        ]),
      ’m
    ]),
    n◆ℕ ⇨ m◆ℕ ⇨ eq (mul ’n ’m) (mul ’m ’n) ℕ)

/-- Factorial function -/
def fac :=
  (la [’n]
    (apb nat_rec [
      const ℕ, one,
      la [’n, ’nf] (mul (add one ’n) ’nf), ’n
    ]),
    n◆ℕ ⇨ ℕ)

/-- 4 + 2 = 3! -/
def four_plus_two_eq_three_factorial :=
  (apb refl [ℕ, add four two],
    eq (apr fac [suc two]) (add four two) ℕ)

def nat_pair := prod ℕ (const ℕ)

/-- Get second element of `nat_pair` -/
def nat_snd :=
  (la [’p]
    (apb prod_rec [
      ℕ, const ℕ, const ℕ, la [’a, ’b] ’b, ’p
    ]),
    p◆nat_pair ⇨ ℕ)

/-- Fibonacci function -/
def fib :=
  (la [’n]
    (apr fst [
      ℕ, const ℕ,
      apb nat_rec [
        const nat_pair, apb pmk [ℕ, const ℕ, zero, one],
        la [’n, ’nf]
          (apb pmk [
            ℕ, const ℕ,
            apr nat_snd [’nf],
            add (apr fst [ℕ, const ℕ, ’nf]) (apr nat_snd [’nf])
          ]),
        ’n
      ]
    ]),
    n◆ℕ ⇨ ℕ)

/-- fib (4 + 2) = 4 * 2 -/
def fib_four_plus_two_eq_four_times_two :=
  (apb refl [ℕ, add four four],
    eq (apr fib [add four two]) (mul four two) ℕ)

/-- Zero is not a successor of any number -/
def succ_ne_zero :=
  (la [’n, ’h]
    (apr rw [
      ℕ, suc ’n, zero,
      apb nat_rec [const 𝒰, ⊥, la [’k, ’v] unit],
      ’h, intro
    ]),
    n◆ℕ ⇨ h◆(eq (suc ’n) zero ℕ) ⇨ ⊥)

/-- Successor is injective -/
def suc_inj :=
  (la [’n, ’m, ’h]
    (apr rw [
      ℕ, suc ’n, suc ’m,
      la [’x] (eq ’n (apr pred [’x]) ℕ),
      ’h, apb refl [ℕ, ’n]
    ]),
    n◆ℕ ⇨ m◆ℕ ⇨ h◆(eq (suc ’n) (suc ’m) ℕ) ⇨ eq ’n ’m ℕ)

/-- n + k = m + k → n = m -/
def add_right_cancel :=
  (la [’n, ’m, ’k]
    (apb nat_rec [
      la [’k] (eq (add ’n ’k) (add ’m ’k) ℕ ⇨ eq ’n ’m ℕ),
      la [’h] ’h,
      la [’k, ’ih, ’h]
        (ap ’ih (eq (add ’n ’k) (add ’m ’k) ℕ ⇨ eq ’n ’m ℕ) [
          apr suc_inj [add ’n ’k, add ’m ’k, ’h]
        ]),
      ’k
    ]),
    n◆ℕ ⇨ m◆ℕ ⇨ k◆ℕ ⇨ eq (add ’n ’k) (add ’m ’k) ℕ ⇨ eq ’n ’m ℕ)

/-- even n := ∃ k, n = k + k -/
def even n :=
  prod ℕ (la [’k] (eq n (add ’k ’k) ℕ))

/-- odd n := ∃ k, n = suc(k + k) -/
def odd n :=
  prod ℕ (la [’k] (eq n (suc (add ’k ’k)) ℕ))

/-- 0 is even -/
def even_zero :=
  (apb pmk [
    ℕ, la [’k] (eq zero (add ’k ’k) ℕ), zero, apb refl [ℕ, zero]
  ],
    even zero)

/-- If n is even, then succ n is odd -/
def even_imp_succ_odd :=
  (la [’n, ’h]
    (apb prod_rec [
      ℕ, la [’k] (eq ’n (add ’k ’k) ℕ), const (odd (suc ’n)),
      la [’k, ’hk]
        (apb pmk [
          ℕ, la [’j] (eq (suc ’n) (suc (add ’j ’j)) ℕ), ’k,
          apr cong_suc [’n, add ’k ’k, ’hk]
        ]),
      ’h
    ]),
    n◆ℕ ⇨ even ’n ⇨ odd (suc ’n))

/-- If n is odd, then succ n is even -/
def odd_imp_succ_even :=
  (la [’n, ’h]
    (apb prod_rec [
      ℕ, la [’k] (eq ’n (suc (add ’k ’k)) ℕ), const (even (suc ’n)),
      la [’k, ’hk]
        (apb pmk [
          ℕ, la [’j] (eq (suc ’n) (add ’j ’j) ℕ),
          suc ’k,
          apr eq_trans [
            ℕ, suc ’n, suc (suc (add ’k ’k)), add (suc ’k) (suc ’k),
            apr cong_suc [’n, suc (add ’k ’k), ’hk],
            apr eq_trans [
              ℕ, suc (suc (add ’k ’k)), suc (add (suc ’k) ’k), add (suc ’k) (suc ’k),
              apr cong_suc [suc (add ’k ’k), add (suc ’k) ’k, apr succ_add [’k, ’k]],
              apb refl [ℕ, add (suc ’k) (suc ’k)]
            ]
          ]
        ]),
      ’h
    ]),
    n◆ℕ ⇨ odd ’n ⇨ even (suc ’n))

/-- Every number is even or odd -/
def even_or_odd :=
  (la [’n]
    (apb nat_rec [
      la [’n] (sum (even ’n) (odd ’n)),
      apb inl [even zero, odd zero, apr even_zero []],
      la [’n, ’ih]
        (apb sum_rec [
          even ’n, odd ’n,
          const (sum (even (suc ’n)) (odd (suc ’n))),
          la [’he] (apb inr [even (suc ’n), odd (suc ’n), apr even_imp_succ_odd [’n, ’he]]),
          la [’ho] (apb inl [even (suc ’n), odd (suc ’n), apr odd_imp_succ_even [’n, ’ho]]),
          ’ih
        ]),
      ’n
    ]),
    n◆ℕ ⇨ sum (even ’n) (odd ’n))

/-- √2 is irrational -/
def sqrt_two_irrational :=
  (name "sorry",
    n◆ℕ ⇨ m◆ℕ ⇨ hm◆(eq ’m zero ℕ ⇨ ⊥) ⇨ h◆(eq (mul two (mul ’n ’n)) (mul ’m ’m) ℕ) ⇨ ⊥)

/-- Exponentiation -/
def pow' :=
  (la [’n]
    (apb nat_rec [
      const ℕ, one, la [’k, ’m] (mul ’n ’m)
    ]),
    n◆ℕ ⇨ ℕ ⇨ ℕ)

def pow n m := apr pow' [n, m]

/-- 2 ^ 4 = 16 -/
def two_to_the_four_eq_sixteen :=
  (apb refl [ℕ, sixteen],
    eq (pow two four) sixteen ℕ)

/-- Fermat's last theorem -/
def fermat :=
  (name "sorry",
    a◆ℕ ⇨ b◆ℕ ⇨ c◆ℕ ⇨ n◆ℕ ⇨ (eq ’a zero ℕ ⇨ ⊥) ⇨ (eq ’b zero ℕ ⇨ ⊥) ⇨ (eq ’c zero ℕ ⇨ ⊥) ⇨ (eq ’n zero ℕ ⇨ ⊥) ⇨ (eq ’n one ℕ ⇨ ⊥) ⇨ (eq ’n two ℕ ⇨ ⊥) ⇨ eq (add (pow ’a ’n) (pow ’b ’n)) (pow ’c ’n) ℕ ⇨ ⊥)

def tests := Std.HashMap.ofList [
  ("a_imp_a", a_imp_a),
  ("a_imp_b_imp_ab", a_imp_b_imp_ab),
  ("a_imp_b_imp_ba", a_imp_b_imp_ba),
  ("not_ab_imp_not_a", not_ab_imp_not_a),
  ("a_imp_not_not_a", a_imp_not_not_a),
  ("not_not_not_a_imp_not_a", not_not_not_a_imp_not_a),
  ("exists_n_eq_zero", exists_n_eq_zero),
  ("forall_a_exists_b_eq_a", forall_a_exists_b_eq_a),
  ("add'", add'),
  ("zero_plus_zero_eq_zero", zero_plus_zero_eq_zero),
  ("zero_plus_one_eq_one", zero_plus_one_eq_one),
  ("two_plus_two_eq_four", two_plus_two_eq_four),
  ("if'", if'),
  ("false_elim", false_elim),
  ("rw", rw),
  ("eq_symm", eq_symm),
  ("eq_trans", eq_trans),
  ("add_zero_eq_zero_add", add_zero_eq_zero_add),
  ("succ_add", succ_add),
  ("add_comm", add_comm),
  ("add_assoc", add_assoc),
  ("pred", pred),
  ("subt", subt),
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
  ("pow'", pow'),
  ("two_to_the_four_eq_sixteen", two_to_the_four_eq_sixteen),
]

def run_test (name : String) (tpair : Term × Term) : IO Unit := do
  let start ← IO.monoNanosNow
  let res := if ch tpair then "passed" else "FAILED"
  IO.println s!"{name} {res} {((← IO.monoNanosNow) - start) / 1000}μs"

def main (args : List String) : IO Unit := do
  if h : 0 < args.length then
    if h : args[0] ∈ tests then
      run_test args[0] tests[args[0]]
    else
      IO.println "Test name not found"
  else
    tests.forM run_test
