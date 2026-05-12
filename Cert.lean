import Std.Data.HashMap

/-! # Certificate-based μLean type checker

Self-contained.  Does *not* import `Dependent.lean`.  Builds proofs as indexed
DAGs from the start — no fat AST is ever materialized.  Outputs a Lurk dump
consisting of:

* a **term table** (balanced tree of node structures, indexed by 0..N-1),
* an **eval map** (balanced tree: index i → index of `eval(node i)`),
* a **rule table** (balanced tree: index i → reduction-rule entry justifying
  the eval map at i),
* per-test (term-idx, type-idx) pairs with `assert` calls.

Soundness: each rule entry is locally checkable from already-validated entries.
The Lurk verifier walks the rule table, validates each entry in order, then
runs `check` using the validated eval map.  No Lurk-side `evaluate` ever runs.
-/

namespace Cert

/-! ## Indexed AST -/

/-- Constructor tag.  `toNat` matches the wire encoding used by `Term.toString`
in the existing `Dependent.lean` (kept identical so we can reuse the dbtype
table later). -/
inductive Tag
  | var | lam | app | typ | fn | prod | pmk | prodRec | sum | inl | inr | sumRec
  | eq | refl | eqRec | nat | zero | succ | natRec | unit | intro | fls | flsRec
  | opq            -- black-box reference to a separately-verified theorem
deriving BEq, Hashable, Repr, Inhabited

def Tag.toNat : Tag → Nat
  | .var => 0  | .lam => 1  | .app => 2  | .typ => 3  | .fn => 4
  | .prod => 5 | .pmk => 6  | .prodRec => 7 | .sum => 8  | .inl => 9
  | .inr => 10 | .sumRec => 11 | .eq => 12 | .refl => 13 | .eqRec => 14
  | .nat => 15 | .zero => 16 | .succ => 17 | .natRec => 18 | .unit => 19
  | .intro => 20 | .fls => 21 | .flsRec => 22 | .opq => 23

/-- A node in the indexed AST.  `payload` carries the de Bruijn index for `var`
or the universe level for `typ`; `0` for everything else.  `children` lists
the child *indices* into the term table. -/
structure Node where
  tag      : Tag
  payload  : Nat       := 0
  children : List Nat  := []
deriving BEq, Hashable, Repr, Inhabited

/-! ## Builder monad — hash-cons nodes as we go -/

structure Builder where
  nodes   : Array Node            := #[]
  indexOf : Std.HashMap Node Nat  := ∅
  /-- Registry of opaque theorems, in declaration order:
  `(opaqueIdx, typeIdx, proofIdx, name)`.  The body has been (or will be)
  verified separately; downstream proofs reference it via the opaque leaf. -/
  theoremAlist : Array (Nat × Nat × Nat × String) := #[]

abbrev BuilderM := StateM Builder

def addNode (n : Node) : BuilderM Nat := do
  let st ← get
  if let some i := st.indexOf[n]? then
    return i
  let i := st.nodes.size
  modify fun s => { s with nodes := s.nodes.push n, indexOf := s.indexOf.insert n i }
  return i

-- Smart constructors.
def var (x : Nat) : BuilderM Nat := addNode { tag := .var, payload := x }
def typ (u : Nat) : BuilderM Nat := addNode { tag := .typ, payload := u }
def fls : BuilderM Nat            := addNode { tag := .fls }
def lam (b : Nat) : BuilderM Nat := addNode { tag := .lam, children := [b] }
def fn (α β : Nat) : BuilderM Nat := addNode { tag := .fn, children := [α, β] }
def app (f φ a : Nat) : BuilderM Nat := addNode { tag := .app, children := [f, φ, a] }
def prod (α β : Nat) : BuilderM Nat := addNode { tag := .prod, children := [α, β] }
def sum (α β : Nat) : BuilderM Nat := addNode { tag := .sum, children := [α, β] }
def eq (a a' α : Nat) : BuilderM Nat := addNode { tag := .eq, children := [a, a', α] }
def refl : BuilderM Nat := addNode { tag := .refl }
def eqRec : BuilderM Nat := addNode { tag := .eqRec }
def pmk : BuilderM Nat := addNode { tag := .pmk }
def prodRec : BuilderM Nat := addNode { tag := .prodRec }
def inl : BuilderM Nat := addNode { tag := .inl }
def inr : BuilderM Nat := addNode { tag := .inr }
def sumRec : BuilderM Nat := addNode { tag := .sumRec }
def nat : BuilderM Nat := addNode { tag := .nat }
def zero : BuilderM Nat := addNode { tag := .zero }
def succ : BuilderM Nat := addNode { tag := .succ }
def natRec : BuilderM Nat := addNode { tag := .natRec }
def unit : BuilderM Nat := addNode { tag := .unit }
def intro : BuilderM Nat := addNode { tag := .intro }
def flsRec : BuilderM Nat := addNode { tag := .flsRec }

/-- An opaque leaf referencing a theorem.  The payload distinguishes
references to different theorems (use the theorem's proofIdx). -/
def opq (id : Nat) : BuilderM Nat := addNode { tag := .opq, payload := id }

/-- Register a theorem.  `body` and `claimedType` are builders that produce
the proof's term-idx and type-idx respectively.  Returns the opaque-leaf
index that downstream proofs can use as a black-box reference. -/
def opaqueTheorem
    (name : String) (body : BuilderM Nat) (claimedType : BuilderM Nat) :
    BuilderM Nat := do
  let proofIdx ← body
  let typeIdx  ← claimedType
  let opaqueIdx ← opq proofIdx
  -- Avoid registering the same theorem twice (idempotent on repeated calls).
  let st ← get
  if st.theoremAlist.any (fun (o, _, _, _) => o == opaqueIdx) then
    return opaqueIdx
  modify fun s =>
    { s with theoremAlist := s.theoremAlist.push (opaqueIdx, typeIdx, proofIdx, name) }
  return opaqueIdx

/-! ## Indexed `incr` and `sub`

These mirror `Term.incr` and `Term.sub` from `Dependent.lean` but operate on
indexed nodes; results are interned via `addNode`, so the term-table grows to
include all substitution results we'll need at type-check time. -/

mutual
  partial def incrIdxAt (k : Nat) : Nat → Nat → BuilderM Nat := fun d i => do
    let st ← get
    match st.nodes[i]! with
    | { tag := .var, payload := x, .. } =>
      var (if d ≤ x then x + k else x)
    | { tag := .lam, children := [b], .. } => do
      let b' ← incrIdxAt k (d + 1) b
      lam b'
    | { tag := .fn, children := [α, β], .. } => do
      let α' ← incrIdxAt k d α
      let β' ← incrIdxAt k (d + 1) β
      fn α' β'
    | { tag := .app, children := [f, φ, a], .. } => do
      let f' ← incrIdxAt k d f
      let φ' ← incrIdxAt k d φ
      let a' ← incrIdxAt k d a
      app f' φ' a'
    | { tag := .prod, children := [α, β], .. } => do
      let α' ← incrIdxAt k d α
      let β' ← incrIdxAt k d β
      prod α' β'
    | { tag := .sum, children := [α, β], .. } => do
      let α' ← incrIdxAt k d α
      let β' ← incrIdxAt k d β
      sum α' β'
    | { tag := .eq, children := [a, a', α], .. } => do
      let a₁ ← incrIdxAt k d a
      let a'₁ ← incrIdxAt k d a'
      let α₁ ← incrIdxAt k d α
      eq a₁ a'₁ α₁
    | _ => return i  -- leaves: nothing to shift
end

def incrIdx (k : Nat) (i : Nat) : BuilderM Nat := incrIdxAt k 0 i

mutual
  partial def subIdxAt (a : Nat) : Nat → Nat → BuilderM Nat := fun d b => do
    let st ← get
    match st.nodes[b]! with
    | { tag := .var, payload := x, .. } =>
      if x = d then incrIdxAt d 0 a
      else var (if d < x then x - 1 else x)
    | { tag := .lam, children := [body], .. } => do
      let body' ← subIdxAt a (d + 1) body
      lam body'
    | { tag := .fn, children := [α, β], .. } => do
      let α' ← subIdxAt a d α
      let β' ← subIdxAt a (d + 1) β
      fn α' β'
    | { tag := .app, children := [f, φ, a'], .. } => do
      let f'' ← subIdxAt a d f
      let φ'' ← subIdxAt a d φ
      let a'' ← subIdxAt a d a'
      app f'' φ'' a''
    | { tag := .prod, children := [α, β], .. } => do
      let α' ← subIdxAt a d α
      let β' ← subIdxAt a d β
      prod α' β'
    | { tag := .sum, children := [α, β], .. } => do
      let α' ← subIdxAt a d α
      let β' ← subIdxAt a d β
      sum α' β'
    | { tag := .eq, children := [aa, aa', α], .. } => do
      let aa₁ ← subIdxAt a d aa
      let aa'₁ ← subIdxAt a d aa'
      let α₁ ← subIdxAt a d α
      eq aa₁ aa'₁ α₁
    | _ => return b
end

def subIdx (a b : Nat) : BuilderM Nat := subIdxAt a 0 b

/-- True iff the node at `i` is `app(app(...(op _ _)... _ _) _ _)` nested
exactly `k` times — i.e. walking the `arg1` chain `k` levels finds tag `op`. -/
partial def isAppKOf (k : Nat) (op : Tag) (i : Nat) : BuilderM Bool := do
  let st ← get
  if k = 0 then return st.nodes[i]!.tag == op
  match st.nodes[i]! with
  | { tag := .app, children := [f, _, _], .. } => isAppKOf (k - 1) op f
  | _ => return false

/-! ## Reduction rules

For the bare minimum (triple-neg), we only need `id`, `congLam`, `congFn`,
`congApp`.  More rules added as we scale up. -/

inductive Rule
  | id
  | congLam
  | congFn
  | congApp
  | congProd
  | congSum
  | congEq
  | beta
  | iotaEq
  | iotaNatZ
  | iotaNatS
  | iotaProd
  | iotaSumL
  | iotaSumR
deriving BEq, Repr, Inhabited

def Rule.toNat : Rule → Nat
  | .id => 0 | .congLam => 1 | .congFn => 2 | .congApp => 3
  | .congProd => 4 | .congSum => 5 | .congEq => 6
  | .beta => 7 | .iotaProd => 8 | .iotaSumL => 9 | .iotaSumR => 10
  | .iotaEq => 11 | .iotaNatZ => 12 | .iotaNatS => 13

structure TraceEntry where
  rule      : Rule
  output    : Nat
  witnesses : List Nat
deriving Repr, Inhabited

/-! ## Memoised eval -/

structure EvalState where
  /-- term-idx → eval-result-idx (memo) -/
  cache : Std.HashMap Nat Nat       := ∅
  /-- The trace, parallel to `Builder.nodes`: entry `trace[i]` justifies how
  `eval(node i) = entry.output` was derived. Order: as we discover them. -/
  entries : Array (Option TraceEntry) := #[]

abbrev EvalM := StateT EvalState BuilderM

/-- Look up a node by index. -/
def getNode (i : Nat) : EvalM Node := do
  let b ← liftM (m := BuilderM) get
  return b.nodes[i]!

/-- Pad the trace `entries` array up to `n` slots. -/
def padEntries (n : Nat) : EvalM Unit := do
  let st ← get
  if st.entries.size < n then
    let extra := List.replicate (n - st.entries.size) (none : Option TraceEntry)
    modify fun s => { s with entries := s.entries.append extra.toArray }

mutual
  partial def evalM (i : Nat) : EvalM Nat := do
    let st ← get
    if let some r := st.cache[i]? then return r
    let n := (← liftM (m := BuilderM) get).nodes.size
    padEntries n
    let nd ← getNode i
    let (output, rule, ws) ← compute nd
    -- We may have grown the table during `compute`, repad.
    let n' := (← liftM (m := BuilderM) get).nodes.size
    padEntries n'
    modify fun s =>
      { s with
        cache   := s.cache.insert i output,
        entries := s.entries.set! i (some { rule, output, witnesses := ws }) }
    return output

  partial def compute : Node → EvalM (Nat × Rule × List Nat)
    | { tag := .lam, children := [b], .. } => do
      let b' ← evalM b
      let r ← liftM (lam b')
      return (r, .congLam, [b'])
    | { tag := .fn, children := [α, β], .. } => do
      let α' ← evalM α
      let β' ← evalM β
      let r ← liftM (fn α' β')
      return (r, .congFn, [α', β'])
    | { tag := .prod, children := [α, β], .. } => do
      let α' ← evalM α
      let β' ← evalM β
      let r ← liftM (prod α' β')
      -- Aux for type-checker: (E[α] ⇨ 𝒰_0) so β can be checked against it.
      let u0Idx ← liftM (typ 0)
      let auxFn ← liftM (fn α' u0Idx)
      let _ ← evalM auxFn
      return (r, .congProd, [α', β', auxFn])
    | { tag := .sum, children := [α, β], .. } => do
      let α' ← evalM α
      let β' ← evalM β
      let r ← liftM (sum α' β')
      return (r, .congSum, [α', β'])
    | { tag := .eq, children := [a, a', α], .. } => do
      let ea ← evalM a
      let ea' ← evalM a'
      let eα ← evalM α
      let r ← liftM (eq ea ea' eα)
      return (r, .congEq, [ea, ea', eα])
    | { tag := .app, children := [f, φ, a], .. } => do
      let f' ← evalM f
      let φ' ← evalM φ
      let a' ← evalM a
      -- Pre-compute sub-and-eval of the type's β (codomain of φ).  This is
      -- needed by check-cert regardless of whether the eval rule is cong-app
      -- or beta or iota-*, so we always include it in the witness list.
      let φNode ← liftM (m := BuilderM) (do
        let st ← get; return st.nodes[φ]!)
      match φNode.children with
      | [_, β] => do
        -- Use eval'd `a'` here: the Lurk validator's `eq-sub-by` rule
        -- checks `subResPhi == sub(E[a], β)`, so the witness we record must
        -- be built from `a'` too.  For most leaf-a's this is identical, but
        -- in sqrt's helpers `a` is often a non-trivial expression and the
        -- two only agree after evaluation.
        let subResPhi   ← liftM (subIdx a' β)
        let subResEvPhi ← evalM subResPhi
        -- Check the eval'd head's shape — if it's a lam, beta-reduce.
        let f'Node ← liftM (m := BuilderM) (do
          let st ← get; return st.nodes[f']!)
        match f'Node with
        | { tag := .lam, children := [b], .. } => do
          let bodySubRes ← liftM (subIdx a' b)
          let result ← evalM bodySubRes
          return (result, .beta,
                  [f', φ', a', subResPhi, subResEvPhi, bodySubRes])
        | _ => do
          -- Iota patterns.
          let isER ← liftM (isAppKOf 5 .eqRec f')
          let isRf ← liftM (isAppKOf 2 .refl a')
          let isNR ← liftM (isAppKOf 3 .natRec f')
          let st1 ← liftM (m := BuilderM) get
          let aIsZero := st1.nodes[a']!.tag == .zero
          if isER ∧ isRf then
            -- iota-eq: extract ha = arg3 of (arg1 f')
            let l1 := st1.nodes[f']!.children[0]!
            let ha := st1.nodes[l1]!.children[2]!
            let result ← evalM ha
            return (result, .iotaEq,
                    [f', φ', a', subResPhi, subResEvPhi, ha])
          else if isNR ∧ aIsZero then
            -- iota-nat-z: f' is 3-deep app of nat_rec applied to (..., z, ...).
            -- z is arg3 of (arg1 f').  Result = eval(z).
            let l1 := st1.nodes[f']!.children[0]!
            let z := st1.nodes[l1]!.children[2]!
            let result ← evalM z
            return (result, .iotaNatZ,
                    [f', φ', a', subResPhi, subResEvPhi, z])
          else
            let isSR ← liftM (isAppKOf 5 .sumRec f')
            let isIL ← liftM (isAppKOf 3 .inl a')
            let isIR ← liftM (isAppKOf 3 .inr a')
            let isPR ← liftM (isAppKOf 4 .prodRec f')
            let isPK ← liftM (isAppKOf 4 .pmk a')
            let aIsSucc := match st1.nodes[a']! with
              | { tag := .app, children := [s, _, _], .. } =>
                st1.nodes[s]!.tag == .succ
              | _ => false
            if isSR && isIL then
              -- iota-sum-l: g = arg3 (arg1 f'); γ = arg1 (arg2 (arg1 f')); a = arg3 a'.
              let l1 := st1.nodes[f']!.children[0]!
              let g := st1.nodes[l1]!.children[2]!
              let phiL1 := st1.nodes[l1]!.children[1]!
              let γ := st1.nodes[phiL1]!.children[0]!
              let a := st1.nodes[a']!.children[2]!
              let outerApp ← liftM (app g γ a)
              let result ← evalM outerApp
              return (result, .iotaSumL,
                      [f', φ', a', subResPhi, subResEvPhi, outerApp])
            else if isSR && isIR then
              -- iota-sum-r: g = arg3 f'; γ = arg1 (arg2 f'); b = arg3 a'.
              let g := st1.nodes[f']!.children[2]!
              let phiF := st1.nodes[f']!.children[1]!
              let γ := st1.nodes[phiF]!.children[0]!
              let b := st1.nodes[a']!.children[2]!
              let outerApp ← liftM (app g γ b)
              let result ← evalM outerApp
              return (result, .iotaSumR,
                      [f', φ', a', subResPhi, subResEvPhi, outerApp])
            else if isPR && isPK then
              -- iota-prod: f' = `prod_rec α β m g` (4 apps), a' = `pmk α β a b` (4 apps).
              -- Result = eval(app (app g (α ⇨ γ) a) (sub a γ) b)
              -- where (α ⇨ γ) is arg1 of (arg2 f') = phi-of-f' is ((α ⇨ γ) ⇨ _).
              let phif := st1.nodes[f']!.children[1]!
              let alphaFnGamma := st1.nodes[phif]!.children[0]!
              let α := st1.nodes[alphaFnGamma]!.children[0]!
              let γ := st1.nodes[alphaFnGamma]!.children[1]!
              let g := st1.nodes[f']!.children[2]!
              -- a' = app(app(app(app(pmk, _, _), _, _), _, a), _, b)
              let aL1 := st1.nodes[a']!.children[0]!
              let aPK := st1.nodes[aL1]!.children[2]!   -- a (the value `a` from pmk)
              let bPK := st1.nodes[a']!.children[2]!     -- b
              let alphaFnGamma' ← liftM (fn α γ)
              let inner ← liftM (app g alphaFnGamma' aPK)
              let subResGamma ← liftM (subIdx aPK γ)
              let outer ← liftM (app inner subResGamma bPK)
              let result ← evalM outer
              return (result, .iotaProd,
                      [f', φ', a', subResPhi, subResEvPhi,
                       subResGamma, inner, outer])
            else if isNR && aIsSucc then
              -- iota-nat-s: f' = nat_rec ... g (3 apps), a' = succ ... n (1 app).
              -- Result = eval(app (app g (ℕ ⇨ γ) n) (sub n γ) (app f' phi n))
              -- where γ extracted from f' (phi-of-f' = ((ℕ ⇨ γ) ⇨ _)).
              let phif := st1.nodes[f']!.children[1]!  -- phi-of-f'
              let phifNd := st1.nodes[phif]!
              -- arg1 of phif = (ℕ ⇨ γ); arg2 of that = γ.
              let natFnGamma := phifNd.children[0]!
              let γ := st1.nodes[natFnGamma]!.children[1]!
              let g := st1.nodes[f']!.children[2]!
              let n := st1.nodes[a']!.children[2]!
              -- Construct intermediates.
              let natIdx ← liftM nat
              let natFnGamma' ← liftM (fn natIdx γ)   -- (ℕ ⇨ γ) — should equal natFnGamma
              let inner ← liftM (app g natFnGamma' n)
              let subResGamma ← liftM (subIdx n γ)
              let recApp ← liftM (app f' φ n)
              let outer ← liftM (app inner subResGamma recApp)
              let result ← evalM outer
              return (result, .iotaNatS,
                      [f', φ', a', subResPhi, subResEvPhi,
                       subResGamma, inner, recApp, outer])
            else do
              let r ← liftM (app f' φ' a')
              return (r, .congApp, [f', φ', a', subResPhi, subResEvPhi])
      | _ =>
        -- ill-typed; emit minimal witnesses, skip beta detection
        let r ← liftM (app f' φ' a')
        return (r, .congApp, [f', φ', a'])
    | nd => do
      -- var, typ, fls, ... — leaves; eval = self.
      let st ← liftM (m := BuilderM) get
      return (st.indexOf[nd]!, .id, [])
end

/-! ## Triple-negation proof

Term: `λα. λf. λa. f (λg. g a)`
Type: `α : 𝒰 → ((α → ⊥) → ⊥) → ⊥) → α → ⊥`

de Bruijn (after dbify with [α, f, a]):
- inside outer `α`-binder:               var 0 = α
- inside α + f binders:                  var 0 = f, var 1 = α
- inside α + f + a binders:              var 0 = a, var 1 = f, var 2 = α
- inside α + f + a + g binders (proof):  var 0 = g, var 1 = a, var 2 = f, var 3 = α
-/

/-! ## Dump rendering -/

/-- Render a single node as a Lurk cell.  The result is a *quoted* list so
Lurk treats it as data, not a function call. -/
def Node.render (nd : Node) : String :=
  let t := s!"{nd.tag.toNat}n"
  match nd.tag with
  | .var | .typ | .opq    => s!"'({t} {nd.payload})"
  | .fls | .nat | .zero | .succ | .pmk | .prodRec | .inl | .inr | .sumRec
  | .refl | .eqRec | .natRec | .unit | .intro | .flsRec => s!"'({t})"
  | .lam | .fn | .app | .prod | .sum | .eq =>
    let cs := String.intercalate " " (nd.children.map (s!"{·}"))
    s!"'({t} {cs})"

/-- Build a perfectly balanced binary tree of Lurk source from a list. -/
partial def buildBalanced : List String → String
  | []  => "nil"
  | [x] => x
  | xs  =>
    let n    := xs.length
    let half := n / 2
    let l    := buildBalanced (xs.take half)
    let r    := buildBalanced (xs.drop half)
    s!"(cons {l} {r})"

/-- Render a TraceEntry as a quoted Lurk list. -/
def TraceEntry.render (e : TraceEntry) : String :=
  let ws := String.intercalate " " (e.witnesses.map (s!"{·}"))
  if e.witnesses.isEmpty then s!"'({e.rule.toNat} {e.output})"
  else s!"'({e.rule.toNat} {e.output} {ws})"

/-- One test: name + (term-idx, type-idx). -/
structure TestCase where
  name     : String
  termIdx  : Nat
  typeIdx  : Nat

/-- Render the dbtype lookup table.  The verifier maps a built-in
constructor's tag-number to the index of its precomputed type.  We emit it as
a `(cons tag (cons dbtype-idx next))` list (terminated by nil); the verifier
walks it linearly. -/
def renderDbtypeAlist (entries : List (Nat × Nat)) : String :=
  let cells := entries.map fun (tag, idx) => s!"(cons {tag}n {idx})"
  let go : List String → String
    | [] => "nil"
    | [c] => s!"(cons {c} nil)"
    | xs => s!"(cons {xs.head!} {go xs.tail!})"
  go cells
where
  go : List String → String
  | [] => "nil"
  | x :: xs => s!"(cons {x} {go xs})"

/-- Render the theorem registry as an association list mapping
`opaqueIdx → typeIdx`.  The proofIdx is *not* in the alist (the verifier
only needs the type for lookup); per-theorem asserts use proofIdx separately. -/
partial def renderTheoremAlist (entries : List (Nat × Nat × Nat × String)) : String :=
  match entries with
  | [] => "nil"
  | (op, ty, _, _) :: rest => s!"(cons (cons {op} {ty}) {renderTheoremAlist rest})"

def renderDump (tests : List TestCase) (b : Builder) (es : EvalState)
    (dbtypeAlist : List (Nat × Nat) := []) : String := Id.run do
  let n := b.nodes.size
  let termCells : List String := (b.nodes.toList).map Node.render
  let entryList : List String := (es.entries.toList).map fun
    | some e => e.render
    | none   => "'(0 0)"  -- unreachable for cells we touched; placeholder
  let evalCells : List String := (es.entries.toList).map fun
    | some e => s!"{e.output}"
    | none   => "0"
  let theorems := b.theoremAlist.toList
  let mut out :=
    s!";; AUTOGENERATED — do not edit. {n} nodes, {tests.length} tests, {theorems.length} opaque theorems.\n\n"
  -- Define tables first so the verifier's `def`s close over them.
  out := out ++ s!"!(def N {n})\n\n"
  out := out ++ "!(def term-table\n  " ++ buildBalanced termCells ++ ")\n\n"
  out := out ++ "!(def eval-table\n  " ++ buildBalanced evalCells ++ ")\n\n"
  out := out ++ "!(def rule-table\n  " ++ buildBalanced entryList ++ ")\n\n"
  -- Dbtype lookup table for built-in constructors.
  out := out ++ "!(def dbtype-alist\n  " ++ renderDbtypeAlist dbtypeAlist ++ ")\n\n"
  -- Theorem registry (opaqueIdx → typeIdx).
  out := out ++ "!(def theorem-alist\n  " ++ renderTheoremAlist theorems ++ ")\n\n"
  -- Load the verifier (its `def`s close over the tables above).
  out := out ++ "!(load \"cert_verifier.lurk\")\n\n"
  out := out ++ ";; ---------- validate the eval map ----------\n"
  out := out ++ "!(assert (validate-trace 0))\n\n"
  -- Theorem bodies must be checked before the main tests so that downstream
  -- proofs that use them via opaque refs can rely on the registered type.
  -- NB: pass the EVAL'd type-idx (`(E ...)`) so check-cert's invariant
  -- "τ is in normal form at the top level" holds.  Recursive descent already
  -- maintains it via `(E alpha-idx)` / `(E beta-idx)`; the top-level was the
  -- only spot still feeding raw indices through eq-incr-by.
  if !theorems.isEmpty then
    out := out ++ ";; ---------- verify each opaque theorem's body ----------\n"
    for (_, ty, proof, name) in theorems do
      out := out ++ s!";; opaque theorem: {name}\n"
      out := out ++ s!"!(assert (check-cert nil {proof} (E {ty})))\n"
    out := out ++ "\n"
  out := out ++ ";; ---------- type-check each test ----------\n"
  for t in tests do
    out := out ++ s!";; {t.name}\n"
    out := out ++ s!"!(assert (check-cert nil {t.termIdx} (E {t.typeIdx})))\n"
  return out

end Cert

namespace Cert

/-- Drive a single proof-build through evalM, render the dump, write file.
We run `evalM` on the term, the type, AND every other node in the builder so
that unused-but-still-present nodes (e.g. `var 0` reserved by the proof
builder but never actually used by this particular proof) also get a valid
trace entry — otherwise the verifier would reject the dump. -/
def runOne (name fileBase : String) (build : BuilderM (Nat × Nat)) : IO Unit := do
  let ((termIdx, typeIdx), b1) := build.run {}
  let prog : EvalM Unit := do
    let _ ← evalM termIdx
    let _ ← evalM typeIdx
    -- Also evaluate every registered opaque theorem's body and type.
    let bld ← liftM (m := BuilderM) get
    for (_, ty, proof, _) in bld.theoremAlist do
      let _ ← evalM ty
      let _ ← evalM proof
    -- Force-evaluate any leftover nodes so every entry is populated.  Loop
    -- until the node table stops growing: each evalM pass can add new nodes
    -- (sub/incr witnesses) which themselves need entries.
    let mut prev := 0
    let mut cur := (← liftM (m := BuilderM) get).nodes.size
    while cur != prev do
      for i in List.range cur do
        let _ ← evalM i
      prev := cur
      cur := (← liftM (m := BuilderM) get).nodes.size
    return ()
  let (((), evalState), b2) := (prog.run {}).run b1
  let test : TestCase := { name, termIdx, typeIdx }
  let dump := renderDump [test] b2 evalState
  let path := s!"slop/cert_{fileBase}.lurk"
  IO.FS.writeFile path dump
  IO.println s!"{name}: {b2.nodes.size} nodes, {evalState.entries.size} trace entries -> {path} ({dump.length} bytes)"

/-- Variant of `runOne` that also accepts a precomputed dbtype-alist (from
the translator, so the Lurk verifier can look up types of built-in constants
like `pmk`, `prod_rec`, …). -/
def runOneWithDbtypes (name fileBase : String)
    (build : BuilderM (Nat × Nat × List (Nat × Nat))) : IO Unit := do
  let ((termIdx, typeIdx, dbtypeAlist), b1) := build.run {}
  IO.println s!"  [info] after translate (pre-eval): {b1.nodes.size} nodes"
  let prog : EvalM Unit := do
    let _ ← evalM termIdx
    let _ ← evalM typeIdx
    -- Make sure every dbtype entry has been eval'd too — those are needed by
    -- the verifier when it does `cumeq dbtype tau` for built-in constants.
    for (_, idx) in dbtypeAlist do
      let _ ← evalM idx
    -- Each opaque theorem's body and type must also be eval'd: the
    -- per-theorem `check-cert` assert reads their trace entries.
    let bld ← liftM (m := BuilderM) get
    for (_, ty, proof, _) in bld.theoremAlist do
      let _ ← evalM ty
      let _ ← evalM proof
    -- Force-evaluate leftover nodes.  Loop until the node table stabilises
    -- (evalM may add sub/incr witnesses that themselves need entries).
    let mut prev := 0
    let mut cur := (← liftM (m := BuilderM) get).nodes.size
    while cur != prev do
      for i in List.range cur do
        let _ ← evalM i
      prev := cur
      cur := (← liftM (m := BuilderM) get).nodes.size
    return ()
  let (((), evalState), b2) := (prog.run {}).run b1
  let test : TestCase := { name, termIdx, typeIdx }
  let dump := renderDump [test] b2 evalState dbtypeAlist
  let path := s!"slop/cert_{fileBase}.lurk"
  IO.FS.writeFile path dump
  IO.println s!"{name}: {b2.nodes.size} nodes, {evalState.entries.size} trace entries, {dbtypeAlist.length} dbtypes -> {path} ({dump.length} bytes)"

end Cert
