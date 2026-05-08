import Lean.Elab
import Std.Data.ExtHashSet

/-
# μLean

A very simple proof assistant in 1000 lines of code!

μLean's type system is based on the calculus of constructions and very similar to Lean (obviously), but with fewer features to make the implementation simpler. μLean does not have general inductive types and instead has a few hardcoded inductive types such as the natural numbers. Additionally, μLean only has two cumulative universes, since stuff above `Type 1` is rarely used in practice anyways. To avoid paradoxes, `Type 1` in μLean does not have a type. Propositions in μLean live in `Type` instead of a dedicated `Prop` universe, which avoids a lot of Lean's `Prop` weirdness.

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
  | vlam (s : String) (b β : Term)
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
notation α " ⇨ " β => fn α β -- \hey
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
def la (b : Term) : Term → Nat → Term
  | _ ⇨ β, n + 1 =>
    lam (la b β n) β
  | vfn s _ β, n + 1 =>
    vlam s (la b β n) β
  | _, _ =>
    b

/-- Bundle the type with `la` (generally primed functions return pairs) -/
def la' b β n := (la b β n, β)

/-
### Capture-avoiding substitution

The type checker only understands de Bruijn indices, so we have support in the vernacular for variable names for user sanity reasons, which are translated to de Bruijn indices using `dbify`. This means that we have to implement capture-avoiding substitution for the vernacular, while the `sub` function in the type checker is much simpler.

The code below is based on https://courses.cs.cornell.edu/cs3110/2021sp/textbook/interp/lambda-subst/main.ml
-/

/-- Check if a name appears free in a term and not shadowed by a binding -/
def free (s : String) : Term → Bool
  | lam b β =>
    free s b || free s β
  | app f φ a α =>
    free s f || free s φ || free s a || free s α
  | α ⇨ β
  | prod α β
  | sum α β =>
    free s α || free s β
  | eq a a' α =>
    free s a || free s a' || free s α
  | name s' =>
    s' == s
  | vlam s' b β =>
    s' != s && (free s b || free s β)
  | vfn s' α β =>
    free s α || (s' != s && free s β)
  | _ =>
    false

/-- Collect all names used in a term -/
def names : Term → Std.ExtHashSet String
  | lam b β =>
    names b ∪ names β
  | app f φ a α =>
    names f ∪ names φ ∪ names a ∪ names α
  | α ⇨ β
  | prod α β
  | sum α β =>
    names α ∪ names β
  | eq a a' α =>
    names a ∪ names a' ∪ names α
  | name s =>
    {s}
  | vlam s b β =>
    {s} ∪ names b ∪ names β
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
  | lam b β =>
    lam (rename s₁ s₂ b) (rename s₁ s₂ β)
  | app f φ a α =>
    app (rename s₁ s₂ f) (rename s₁ s₂ φ) (rename s₁ s₂ a) (rename s₁ s₂ α)
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
  | vlam s b β =>
    vlam s (if s == s₁ then b else rename s₁ s₂ b) (if s == s₁ then β else rename s₁ s₂ β)
  | vfn s α β =>
    vfn s (rename s₁ s₂ α) (if s == s₁ then β else rename s₁ s₂ β)
  | t =>
    t

/-- The default `SizeOf` instance is kinda janky and includes string lengths so let's write our own -/
def Term.sizeOf : Term → Nat
  | lam b β
  | vlam _ b β =>
    1 + b.sizeOf + β.sizeOf
  | app f φ a α =>
    1 + f.sizeOf + φ.sizeOf + a.sizeOf + α.sizeOf
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
  | lam b β =>
    lam (subca s t' b) (subca s t' β)
  | app f φ a α =>
    app (subca s t' f) (subca s t' φ) (subca s t' a) (subca s t' α)
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
  | vlam s' b β =>
    if s' == s then
      vlam s' b β
    else if free s' t' then
      let fresh := gensym (names t' ∪ names b ∪ names β ∪ {s})
      vlam fresh (subca s t' (rename s' fresh b)) (subca s t' (rename s' fresh β))
    else
      vlam s' (subca s t' b) (subca s t' β)
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
    ap (app f (α ⇨ β) x α) β xs
  | vfn s α β, x :: xs =>
    ap (app f (vfn s α β) x α) (subca s x β) xs
  | _, _ =>
    f

/-- Convert from variable names to de Bruijn indices -/
def dbify (names : List String) : Term → Term
  | lam b β =>
    lam (dbify ("" :: names) b) (dbify ("" :: names) β)
  | app f φ a α =>
    app (dbify names f) (dbify names φ) (dbify names a) (dbify names α)
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
  | vlam s b β =>
    lam (dbify (s :: names) b) (dbify (s :: names) β)
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

open Lean Elab Term in
/-- Compute `dbtype` at compile-time -/
elab "precompute_dbtypes" : term => do
  return toExpr <|
    [𝒰, pmk, prod_rec, inl, inr, sum_rec, refl, eq_rec, ℕ, zero, succ, nat_rec, unit, intro, ⊥, fls_rec].map (dbify [] ·.btype)

def dbtypes := precompute_dbtypes

/-- Yeah I know this is inelegant but metaprogramming is too dark magic for me -/
def Term.dbtype
  | 𝒰 => dbtypes[0]
  | pmk => dbtypes[1]
  | prod_rec => dbtypes[2]
  | inl => dbtypes[3]
  | inr => dbtypes[4]
  | sum_rec => dbtypes[5]
  | refl => dbtypes[6]
  | eq_rec => dbtypes[7]
  | ℕ => dbtypes[8]
  | zero => dbtypes[9]
  | succ => dbtypes[10]
  | nat_rec => dbtypes[11]
  | unit => dbtypes[12]
  | intro => dbtypes[13]
  | ⊥ => dbtypes[14]
  | fls_rec => dbtypes[15]
  | t => t

/-
## The type checker

Time for the fun part!
-/

/-- Helper function for recursing over terms -/
def term_rec (s : α) (fdep : α → α) (fvar : α → Nat → Term) :=
  let rec g s
    | var x =>
      fvar s x
    | lam b β =>
      lam (g (fdep s) b) (g (fdep s) β)
    | app f φ a α =>
      app (g s f) (g s φ) (g s a) (g s α)
    | α ⇨ β =>
      g s α ⇨ g (fdep s) β
    | prod α β =>
      prod (g s α) (g s β)
    | sum α β =>
      sum (g s α) (g s β)
    | eq a a' α =>
      eq (g s a) (g s a') (g s α)
    | t =>
      t
  g s

/-- Increment free variables by 1 -/
def incr :=
  term_rec 0 (· + 1) fun d x ↦ var (if d ≤ x then x + 1 else x)

/-- Substitute `t'` at index 0 in a term -/
def sub (t' : Term) :=
  term_rec (0, t') (fun (d, t') ↦ (d + 1, incr t')) fun (d, t') x ↦ if x == d then t' else var (if d < x then x - 1 else x)

/-- The janky evaluator (the input should be well-typed or bad things will happen) -/
partial def eval : Term → Term
  | lam b β =>
    lam (eval b) (eval β)
  | app f φ a α =>
    let f' := eval f
    match f', eval a with
    | lam b _, a' =>
      eval (sub a' b)
    | app (app (app (app prod_rec _ _ _) _ _ _) _ _ _) _ g (α ⇨ γ), app (app (app (app pmk _ _ _) _ _ _) _ a _) _ b β =>
      eval (app (app g (α ⇨ γ) a α) (sub a γ) b β)
    | app (app (app (app (app sum_rec _ _ _) _ _ _) _ _ _) _ g γ) _ _ _, app (app (app inl _ _ _) _ _ _) _ a α =>
      eval (app g γ a α)
    | app (app (app (app (app sum_rec _ _ _) _ _ _) _ _ _) _ _ _) _ g γ, app (app (app inr _ _ _) _ _ _) _ b β =>
      eval (app g γ b β)
    | app (app (app (app (app eq_rec _ _ _) _ _ _) _ _ _) _ ha _) _ _ _, app (app refl _ _ _) _ _ _ =>
      eval ha
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

/-- And finally, the type checker! (the second input term should be well-typed) -/
def check (env : List Term) : Term → Term → Bool
  | var x, α =>
    -- The types in `env` have not been `eval`ed so we need to do that here
    if _ : x < env.length then cumeq (eval env[x]) α else false
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
  | 𝒰₁, _ =>
    -- Prevent Girard's paradox
    false
  | t, τ =>
    cumeq t.dbtype τ

-- A few test cases
#guard check [] pmk.dbtype 𝒰₁

#guard check [] prod_rec.dbtype 𝒰₁

#guard check [] inl.dbtype 𝒰₁

#guard check [] inr.dbtype 𝒰₁

#guard check [] sum_rec.dbtype 𝒰₁

#guard check [] refl.dbtype 𝒰₁

#guard check [] eq_rec.dbtype 𝒰₁

#guard check [] nat_rec.dbtype 𝒰₁

#guard check [] fls_rec.dbtype 𝒰₁

#guard !check [] 𝒰₁ 𝒰₁

-- TODO: This should pass the type check?
-- #guard check [] (dbify [] (f◆(ℕ ⇨ ℕ ⇨ 𝒰) ⇨ n◆ℕ ⇨ (ap ’f (ℕ ⇨ ℕ ⇨ 𝒰) [’n]))) 𝒰₁

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
def a_imp_a := la'
  ’a
  (α◆𝒰 ⇨ a◆’α ⇨ ’α)
  2

#guard ch a_imp_a

/-- A → B → A ∧ B -/
def a_imp_b_imp_ab := la'
  (apb pmk
    [’α, la ’β (’α ⇨ 𝒰) 1])
  (α◆𝒰 ⇨ β◆𝒰 ⇨ ’α ⇨ ’β ⇨ prod ’α (la ’β (’α ⇨ 𝒰) 1))
  2

#guard ch a_imp_b_imp_ab

/-- A → B → B ∧ A -/
def a_imp_b_imp_ba := la'
  (apb pmk
    [’β, la ’α (’β ⇨ 𝒰) 1, ’b, ’a])
  (α◆𝒰 ⇨ β◆𝒰 ⇨ a◆’α ⇨ b◆’β ⇨ prod ’β (la ’α (’β ⇨ 𝒰) 1))
  4

#guard ch a_imp_b_imp_ba

/-- Get first element of product -/
def fst := la'
  (apb prod_rec
    [’α, ’β,
      la ’α (prod ’α ’β ⇨ 𝒰) 1,
      la ’a (a◆’α ⇨ (ap ’β (’α ⇨ 𝒰) [’a]) ⇨ ’α) 2, ’p])
  (α◆𝒰 ⇨ β◆(’α ⇨ 𝒰) ⇨ p◆(prod ’α ’β) ⇨ ’α)
  3

#guard ch fst

/-- ¬(A ∨ B) → ¬A -/
def not_ab_imp_not_a := la'
  (ap ’f (sum ’α ’β ⇨ ⊥)
    [apb inl [’α, ’β, ’a]])
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
  (ap ’f (((’α ⇨ ⊥) ⇨ ⊥) ⇨ ⊥)
    [la (ap ’f (’α ⇨ ⊥) [’a]) (f◆(’α ⇨ ⊥) ⇨ ⊥) 1])
  (α◆𝒰 ⇨ f◆(((’α ⇨ ⊥) ⇨ ⊥) ⇨ ⊥) ⇨ a◆’α ⇨ ⊥)
  3

#guard ch not_not_not_a_imp_not_a

/-- ∃ n : ℕ, n = 0 -/
def exists_n_eq_zero :=
  (apb pmk
    [ℕ, la (eq ’n zero ℕ) (n◆ℕ ⇨ 𝒰) 1, zero, apb refl [ℕ, zero]],
    prod ℕ (la (eq ’n zero ℕ) (n◆ℕ ⇨ 𝒰) 1))

#guard ch exists_n_eq_zero

/-- ∀ a : A, ∃ b : A, b = a -/
def forall_a_exists_b_eq_a := la'
  (apb pmk
    [’α, la (eq ’b ’a ’α) (b◆’α ⇨ 𝒰) 1, ’a, apb refl [’α, ’a]])
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
  (apb nat_rec
    [la ℕ (ℕ ⇨ 𝒰) 1, ’n, la (suc ’m) (ℕ ⇨ m◆ℕ ⇨ ℕ) 2])
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
  (apb sum_rec
    [unit, unit, la ’α (bool' ⇨ 𝒰) 1, la ’a (unit ⇨ ’α) 1, la ’a' (unit ⇨ ’α) 1, ’b])
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
  (apb eq_rec
    [’α, ’a,
      la (ap ’p (’α ⇨ 𝒰) [’x]) (x◆’α ⇨ (eq ’a ’x ’α) ⇨ 𝒰) 2,
      ’ha, ’b, ’h])
  (α◆𝒰 ⇨ a◆’α ⇨ b◆’α ⇨ p◆(’α ⇨ 𝒰) ⇨ h◆(eq ’a ’b ’α) ⇨ ha◆(ap ’p (’α ⇨ 𝒰) [’a]) ⇨ ap ’p (’α ⇨ 𝒰) [’b])
  6

#guard ch rw

/-- a = b → b = a -/
def eq_symm := la'
  (apb eq_rec
    [’α, ’a,
      la (eq ’x ’a ’α) (x◆’α ⇨ (eq ’a ’x ’α) ⇨ 𝒰) 2,
      apb refl [’α, ’a], ’b, ’h])
  (α◆𝒰 ⇨ a◆’α ⇨ b◆’α ⇨ h◆(eq ’a ’b ’α) ⇨ eq ’b ’a ’α)
  4

#guard ch eq_symm

/-- a = b → b = c → a = c -/
def eq_trans := la'
  (apb eq_rec
    [’α, ’b,
      la (eq ’a ’x ’α) (x◆’α ⇨ (eq ’b ’x ’α) ⇨ 𝒰) 2,
      ’hab, ’c, ’hbc])
  (α◆𝒰 ⇨ a◆’α ⇨ b◆’α ⇨ c◆’α ⇨ hab◆(eq ’a ’b ’α) ⇨ hbc◆(eq ’b ’c ’α) ⇨ eq ’a ’c ’α)
  6

#guard ch eq_trans

/-- Wrapper function for `eq_symm` -/
def sy α a b h :=
  ap eq_symm.1 eq_symm.2 [α, a, b, h]

/-- Wrapper function for `eq_trans` -/
def tr α a b c hab hbc :=
  ap eq_trans.1 eq_trans.2 [α, a, b, c, hab, hbc]

/-- n = m → suc n = suc m -/
def cong_suc := la'
  (ap rw.1 rw.2
    [ℕ, ’n, ’m,
      la (eq (suc ’n) (suc ’x) ℕ) (x◆ℕ ⇨ 𝒰) 1,
      ’h, apb refl [ℕ, suc ’n]])
  (n◆ℕ ⇨ m◆ℕ ⇨ h◆(eq ’n ’m ℕ) ⇨ eq (suc ’n) (suc ’m) ℕ)
  3

#guard ch cong_suc

/-- n = m → k + n = k + m -/
def cong_add_l := la'
  (ap rw.1 rw.2
    [ℕ, ’n, ’m,
      la (eq (add ’k ’n) (add ’k ’x) ℕ) (x◆ℕ ⇨ 𝒰) 1,
      ’h, apb refl [ℕ, add ’k ’n]])
  (n◆ℕ ⇨ m◆ℕ ⇨ k◆ℕ ⇨ h◆(eq ’n ’m ℕ) ⇨ eq (add ’k ’n) (add ’k ’m) ℕ)
  4

#guard ch cong_add_l

/-- n = m → n + k = m + k -/
def cong_add_r := la'
  (ap rw.1 rw.2
    [ℕ, ’n, ’m,
      la (eq (add ’n ’k) (add ’x ’k) ℕ) (x◆ℕ ⇨ 𝒰) 1,
      ’h, apb refl [ℕ, add ’n ’k]])
  (n◆ℕ ⇨ m◆ℕ ⇨ k◆ℕ ⇨ h◆(eq ’n ’m ℕ) ⇨ eq (add ’n ’k) (add ’m ’k) ℕ)
  4

#guard ch cong_add_r

/-- n = 0 + n -/
def zero_add := la'
  (apb nat_rec
    [la (eq ’n (add zero ’n) ℕ) (n◆ℕ ⇨ 𝒰) 1, apb refl [ℕ, zero],
      la
        (ap rw.1 rw.2
          [ℕ, ’n, add zero ’n,
            la (eq (add ’n one) (add ’m one) ℕ) (m◆ℕ ⇨ 𝒰) 1,
            ’h, apb refl [ℕ, add ’n one]])
        (n◆ℕ ⇨ h◆(eq ’n (add zero ’n) ℕ) ⇨ eq (add ’n one) (add zero (add ’n one)) ℕ)
        2,
      ’n])
  (n◆ℕ ⇨ eq ’n (add zero ’n) ℕ)
  1

#guard ch zero_add

/-- n + 0 = 0 + n -/
def add_zero_eq_zero_add := la'
  (ap zero_add.1 zero_add.2 [’n])
  (n◆ℕ ⇨ eq (add ’n zero) (add zero ’n) ℕ)
  1

#guard ch add_zero_eq_zero_add

/-- suc (m + n) = (suc m) + n -/
def succ_add := la'
  (apb nat_rec
    [la (eq (suc (add ’m ’n)) (add (suc ’m) ’n) ℕ) (n◆ℕ ⇨ 𝒰) 1,
      apb refl [ℕ, suc ’m],
      la
        (ap rw.1 rw.2
          [ℕ, suc (add ’m ’n), add (suc ’m) ’n,
            la (eq (suc (suc (add ’m ’n))) (suc ’x) ℕ) (x◆ℕ ⇨ 𝒰) 1,
            ’h, apb refl [ℕ, suc (suc (add ’m ’n))]])
        (n◆ℕ ⇨ h◆(eq (suc (add ’m ’n)) (add (suc ’m) ’n) ℕ) ⇨ eq (suc (add ’m (suc ’n))) (add (suc ’m) (suc ’n)) ℕ)
        2,
      ’n])
  (m◆ℕ ⇨ n◆ℕ ⇨ eq (suc (add ’m ’n)) (add (suc ’m) ’n) ℕ)
  2

#guard ch succ_add

/-- n + m = m + n -/
def add_comm := la'
  (apb nat_rec
    [la (eq (add ’n ’m) (add ’m ’n) ℕ) (m◆ℕ ⇨ 𝒰) 1,
      ap add_zero_eq_zero_add.1 add_zero_eq_zero_add.2 [’n],
      la
        (ap rw.1 rw.2
          [ℕ, suc (add ’m ’n), add (suc ’m) ’n,
            la (eq (suc (add ’n ’m)) ’x ℕ) (x◆ℕ ⇨ 𝒰) 1,
            ap succ_add.1 succ_add.2 [’m, ’n],
            ap rw.1 rw.2
              [ℕ, add ’n ’m, add ’m ’n,
                la (eq (suc (add ’n ’m)) (suc ’x) ℕ) (x◆ℕ ⇨ 𝒰) 1,
                ’h, apb refl [ℕ, suc (add ’n ’m)]]])
      (m◆ℕ ⇨ h◆(eq (add ’n ’m) (add ’m ’n) ℕ) ⇨ eq (add ’n (suc ’m)) (add (suc ’m) ’n) ℕ) 2, ’m])
  (n◆ℕ ⇨ m◆ℕ ⇨ eq (add ’n ’m) (add ’m ’n) ℕ)
  2

#guard ch add_comm

/-- n + (m + k) = (n + m) + k -/
def add_assoc := la'
  (apb nat_rec
    [la (eq (add ’n (add ’m ’k)) (add (add ’n ’m) ’k) ℕ) (k◆ℕ ⇨ 𝒰) 1,
      apb refl [ℕ, add ’n ’m],
      la
        (ap rw.1 rw.2
          [ℕ, add ’n (add ’m ’k), add (add ’n ’m) ’k,
            la (eq (suc (add ’n (add ’m ’k))) (suc ’x) ℕ) (x◆ℕ ⇨ 𝒰) 1,
            ’h, apb refl [ℕ, suc (add ’n (add ’m ’k))]])
        (k◆ℕ ⇨ h◆(eq (add ’n (add ’m ’k)) (add (add ’n ’m) ’k) ℕ) ⇨ eq (add ’n (add ’m (suc ’k))) (add (add ’n ’m) (suc ’k)) ℕ)
        2,
      ’k])
  (n◆ℕ ⇨ m◆ℕ ⇨ k◆ℕ ⇨ eq (add ’n (add ’m ’k)) (add (add ’n ’m) ’k) ℕ)
  3

#guard ch add_assoc

/-- Multiplication -/
def mul' := la'
  (apb nat_rec [la ℕ (ℕ ⇨ 𝒰) 1, zero, la (add ’n ’m) (ℕ ⇨ m◆ℕ ⇨ ℕ) 2])
  (n◆ℕ ⇨ ℕ ⇨ ℕ)
  1

#guard ch mul'

def mul n m := ap mul'.1 mul'.2 [n, m]

/-- 0 * n = 0 -/
def zero_mul := la'
  (apb nat_rec
    [la (eq (mul zero ’n) zero ℕ) (n◆ℕ ⇨ 𝒰) 1,
      apb refl [ℕ, zero],
      la
        (ap rw.1 rw.2
          [ℕ, zero, mul zero ’n,
            la (eq (add zero ’m) zero ℕ) (m◆ℕ ⇨ 𝒰) 1,
            sy ℕ (mul zero ’n) zero ’h, apb refl [ℕ, zero]])
        (n◆ℕ ⇨ h◆(eq (mul zero ’n) zero ℕ) ⇨ eq (mul zero (suc ’n)) zero ℕ)
        2,
    ’n])
  (n◆ℕ ⇨ eq (mul zero ’n) zero ℕ)
  1

#guard ch zero_mul

/-- (suc m) * n = n + m * n -/
def succ_mul := la'
  (apb nat_rec
    [la (eq (mul (suc ’m) ’n) (add ’n (mul ’m ’n)) ℕ) (n◆ℕ ⇨ 𝒰) 1,
      apb refl [ℕ, zero],
      la
        (tr ℕ (add (suc ’m) (mul (suc ’m) ’n))
          (add (suc ’m) (add ’n (mul ’m ’n)))
          (add (suc ’n) (add ’m (mul ’m ’n)))
          (ap cong_add_l.1 cong_add_l.2 [mul (suc ’m) ’n, add ’n (mul ’m ’n), suc ’m, ’ih])
          (tr ℕ (add (suc ’m) (add ’n (mul ’m ’n)))
            (add (add (suc ’m) ’n) (mul ’m ’n))
            (add (suc ’n) (add ’m (mul ’m ’n)))
            (ap add_assoc.1 add_assoc.2 [suc ’m, ’n, mul ’m ’n])
            (tr ℕ (add (add (suc ’m) ’n) (mul ’m ’n))
              (add (suc (add ’m ’n)) (mul ’m ’n))
              (add (suc ’n) (add ’m (mul ’m ’n)))
              (ap cong_add_r.1 cong_add_r.2
                [add (suc ’m) ’n, suc (add ’m ’n), mul ’m ’n,
                  sy ℕ (suc (add ’m ’n)) (add (suc ’m) ’n) (ap succ_add.1 succ_add.2 [’m, ’n])])
              (tr ℕ (add (suc (add ’m ’n)) (mul ’m ’n))
                (add (suc (add ’n ’m)) (mul ’m ’n))
                (add (suc ’n) (add ’m (mul ’m ’n)))
                (ap cong_add_r.1 cong_add_r.2
                  [suc (add ’m ’n), suc (add ’n ’m), mul ’m ’n,
                    (ap cong_suc.1 cong_suc.2 [add ’m ’n, add ’n ’m, ap add_comm.1 add_comm.2 [’m, ’n]])])
                (tr ℕ (add (suc (add ’n ’m)) (mul ’m ’n))
                  (add (add (suc ’n) ’m) (mul ’m ’n))
                  (add (suc ’n) (add ’m (mul ’m ’n)))
                  (ap cong_add_r.1 cong_add_r.2
                    [suc (add ’n ’m), add (suc ’n) ’m, mul ’m ’n, ap succ_add.1 succ_add.2 [’n, ’m]])
                  (sy ℕ (add (suc ’n) (add ’m (mul ’m ’n)))
                    (add (add (suc ’n) ’m) (mul ’m ’n))
                    (ap add_assoc.1 add_assoc.2 [suc ’n, ’m, mul ’m ’n])))))))
          (n◆ℕ ⇨ ih◆(eq (mul (suc ’m) ’n) (add ’n (mul ’m ’n)) ℕ) ⇨ eq (mul (suc ’m) (suc ’n)) (add (suc ’n) (mul ’m (suc ’n))) ℕ)
        2,
      ’n])
  (m◆ℕ ⇨ n◆ℕ ⇨ eq (mul (suc ’m) ’n) (add ’n (mul ’m ’n)) ℕ)
  2

-- This proof takes a long time to check
-- #guard ch succ_mul

def mul_comm := la'
  (apb nat_rec
    [la (eq (mul ’n ’m) (mul ’m ’n) ℕ) (m◆ℕ ⇨ 𝒰) 1,
      sy ℕ (mul zero ’n) zero (ap zero_mul.1 zero_mul.2 [’n]),
      la
        (tr ℕ
          (add ’n (mul ’n ’m))
          (add ’n (mul ’m ’n))
          (mul (suc ’m) ’n)
          (ap cong_add_r.1 cong_add_r.2 [mul ’n ’m, mul ’m ’n, ’n, ’ih])
          (sy ℕ (mul (suc ’m) ’n) (add ’n (mul ’m ’n)) (ap succ_mul.1 succ_mul.2 [’m, ’n])))
        (m◆ℕ ⇨ ih◆(eq (mul ’n ’m) (mul ’m ’n) ℕ) ⇨ eq (mul ’n (suc ’m)) (mul (suc ’m) ’n) ℕ)
        2,
      ’m])
  (n◆ℕ ⇨ m◆ℕ ⇨ eq (mul ’n ’m) (mul ’m ’n) ℕ)
  2

-- This proof takes a long time to check
-- #guard ch mul_comm

/-- 16 exists -/
def sixteen :=
  suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc four)))))))))))

#guard ch (sixteen, ℕ)

/-- 4 * 4 = 16 -/
def four_times_four_eq_sixteen :=
  (apb refl [ℕ, sixteen],
    eq (mul four four) sixteen ℕ)

#guard ch four_times_four_eq_sixteen

/-- Factorial function -/
def fac := la'
  (apb nat_rec [la ℕ (ℕ ⇨ 𝒰) 1, one, la (mul (add one ’n) ’nf)
  (n◆ℕ ⇨ nf◆ℕ ⇨ ℕ) 2, ’n])
  (n◆ℕ ⇨ ℕ)
  1

#guard ch fac

/-- 4 + 2 = 3! -/
def four_plus_two_eq_three_factorial :=
  (apb refl [ℕ, add four two],
    eq (ap fac.1 fac.2 [suc two]) (add four two) ℕ)

#guard ch four_plus_two_eq_three_factorial

/-- Exponentiation -/
def pow' := la'
  (apb nat_rec [la ℕ (ℕ ⇨ 𝒰) 1, one, la (mul ’n ’m)
  (ℕ ⇨ m◆ℕ ⇨ ℕ) 2])
  (n◆ℕ ⇨ ℕ ⇨ ℕ)
  1

#guard ch pow'

def pow n m := ap pow'.1 pow'.2 [n, m]

/-- 2 ^ 4 = 16 -/
def two_to_the_four_eq_sixteen :=
  (apb refl [ℕ, sixteen],
    eq (pow two four) sixteen ℕ)

#guard ch two_to_the_four_eq_sixteen

/-- Fermat's last theorem -/
def fermat := la'
  (name "sorry")
  (a◆ℕ ⇨ b◆ℕ ⇨ c◆ℕ ⇨ n◆ℕ ⇨ (eq ’a zero ℕ ⇨ ⊥) ⇨ (eq ’b zero ℕ ⇨ ⊥) ⇨ (eq ’c zero ℕ ⇨ ⊥) ⇨ (eq ’n zero ℕ ⇨ ⊥) ⇨ (eq ’n one ℕ ⇨ ⊥) ⇨ (eq ’n two ℕ ⇨ ⊥) ⇨ eq (add (pow ’a ’n) (pow ’b ’n)) (pow ’c ’n) ℕ ⇨ ⊥)
  10

-- #guard ch fermat

-- Takes 3.5 seconds to run when compiled
def main : IO Unit := do
  -- IO.FS.writeFile "mul_comm" <| serialize mul_comm
  let start ← IO.monoMsNow
  IO.println <| ch mul_comm
  -- Should take around 125ms, so most of the runtime is actually spent desugaring the vernacular
  IO.println s!"Took {(← IO.monoMsNow) - start}ms to check mul_comm"
