import Cert

/-! # Lean-side type checker

A reimplementation of `check` from `Dependent.lean` that works directly on
indexed `Cert.Node`s.  Shares the `EvalM` monad with `evalM`, so memoised
eval lookups carry over.

This is a *sanity oracle* — run it on a proof before dumping.  If `checkLean`
returns `true`, the dump will type-check in Lurk; if it returns `false`, the
proof is malformed and you'll get much better debugging info here than from
the Lurk verifier's eventual `assert failed`.

Mirrors the Lurk `check-cert` rule-by-rule so both must agree.
-/

namespace Cert

/-- Compare two **already-evaluated** type indices for equality, with universe
cumulativity.  Because the term table is hash-consed, normal-form equality
reduces to index equality. -/
partial def cumeqLean (a b : Nat) : EvalM Bool := do
  let ae ← evalM a
  let be ← evalM b
  let aNd ← getNode ae
  let bNd ← getNode be
  if aNd.tag == .typ && bNd.tag == .typ then
    return aNd.payload ≤ bNd.payload
  else
    return ae == be

/-- The type-checker.  `env` is a list of *already-evaluated* type indices.
`t` is the term to check, `τ` is its expected type (also expected to be in
normal form).  Returns `true` iff well-typed.  Uses `evalM` whenever a sub-
expression must be normalised. -/
partial def checkLean (env : List Nat) (t τ : Nat) : EvalM Bool := do
  let nd ← getNode t
  match nd.tag with
  | .var =>
    let x := nd.payload
    if h : x < env.length then
      let envType := env[x]
      let lifted ← liftM (incrIdx (x + 1) envType)
      let liftedEv ← evalM lifted
      cumeqLean liftedEv τ
    else return false
  | .lam =>
    let τNd ← getNode τ
    if τNd.tag == .fn then
      let α := τNd.children[0]!
      let β := τNd.children[1]!
      let b := nd.children[0]!
      let αEv ← evalM α
      let βEv ← evalM β
      checkLean (αEv :: env) b βEv
    else return false
  | .app =>
    let f := nd.children[0]!
    let φ := nd.children[1]!
    let a := nd.children[2]!
    let φNd ← getNode φ
    if φNd.tag == .fn then
      let α := φNd.children[0]!
      let β := φNd.children[1]!
      let αEv ← evalM α
      let cf ← checkLean env f φ
      let ca ← checkLean env a αEv
      if cf && ca then
        let subRes ← liftM (subIdx a β)
        let subEv ← evalM subRes
        cumeqLean subEv τ
      else return false
    else return false
  | .fn =>
    let τNd ← getNode τ
    if τNd.tag == .typ then
      let α := nd.children[0]!
      let β := nd.children[1]!
      let cα ← checkLean env α τ
      if cα then
        let αEv ← evalM α
        checkLean (αEv :: env) β τ
      else return false
    else return false
  | .prod =>
    let τNd ← getNode τ
    if τNd.tag == .typ then
      let α := nd.children[0]!
      let β := nd.children[1]!
      let cα ← checkLean env α τ
      if cα then
        -- β must check against (E[α] ⇨ 𝒰) (dependent product constraint).
        let αEv ← evalM α
        let u0Idx ← liftM (typ 0)
        let auxFn ← liftM (fn αEv u0Idx)
        let auxFnEv ← evalM auxFn
        checkLean env β auxFnEv
      else return false
    else return false
  | .sum =>
    let τNd ← getNode τ
    if τNd.tag == .typ then
      let α := nd.children[0]!
      let β := nd.children[1]!
      let cα ← checkLean env α τ
      if cα then checkLean env β τ else return false
    else return false
  | .eq =>
    let τNd ← getNode τ
    if τNd.tag == .typ then
      let a := nd.children[0]!
      let aPrime := nd.children[1]!
      let α := nd.children[2]!
      let αEv ← evalM α
      let ca ← checkLean env a αEv
      if ca then
        let cap ← checkLean env aPrime αEv
        if cap then checkLean env α τ else return false
      else return false
    else return false
  | .fls =>
    let τNd ← getNode τ
    return (τNd.tag == .typ)
  | .typ =>
    let τNd ← getNode τ
    if τNd.tag == .typ then
      return (nd.payload + 1) ≤ τNd.payload
    else return false
  | .opq =>
    -- An opaque leaf — black-box reference to a separately verified theorem.
    -- Look it up in the builder's theoremAlist; if found, compare its
    -- registered type to τ via cumeq.
    let b ← liftM (m := BuilderM) get
    match b.theoremAlist.find? (fun (op, _, _, _) => op == t) with
    | some (_, ty, _, _) =>
      let tyEv ← evalM ty
      cumeqLean tyEv τ
    | none => return false
  | _ =>
    -- Built-in constant.  Look up its tag in `dbtypeAlist` (threaded
    -- through via the EvalState pseudo-field — keep this simple by
    -- passing the list explicitly via the lifted reader below).
    return false  -- handled by the wrapper `checkLeanWithDbtypes` instead

/-- Convenience wrapper: build a proof, run `checkLean`, return `(ok?, builder, evalState)`.
The builder/state is returned so the caller can also dump if desired.

If any opaque theorems are registered in the builder, each one's body is
checked against its claimed type before the main proof is checked. -/
def runCheck (build : BuilderM (Nat × Nat)) : (Bool × Builder × EvalState) :=
  let ((termIdx, typeIdx), b1) := build.run {}
  let prog : EvalM Bool := do
    let bld ← liftM (m := BuilderM) get
    let mut allOk := true
    for (_, ty, proof, _) in bld.theoremAlist do
      if allOk then
        let τEv ← evalM ty
        let r ← checkLean [] proof τEv
        if !r then allOk := false
    if !allOk then return false
    let τEv ← evalM typeIdx
    checkLean [] termIdx τEv
  let ((ok, evalState), b2) := (prog.run {}).run b1
  (ok, b2, evalState)

/-- A more thorough checker that mirrors the Lurk verifier's `check-cert`,
including dbtype lookup for built-in constants.  Threads `dbtypes` through
every recursive call. -/
partial def checkLeanD (dbtypes : List (Nat × Nat))
    (env : List Nat) (t τ : Nat) : EvalM Bool := do
  let nd ← getNode t
  match nd.tag with
  | .var =>
    let x := nd.payload
    if h : x < env.length then
      let envType := env[x]
      let lifted ← liftM (incrIdx (x + 1) envType)
      let liftedEv ← evalM lifted
      cumeqLean liftedEv τ
    else return false
  | .lam =>
    let τNd ← getNode τ
    if τNd.tag == .fn then
      let α := τNd.children[0]!
      let β := τNd.children[1]!
      let b := nd.children[0]!
      let αEv ← evalM α
      let βEv ← evalM β
      checkLeanD dbtypes (αEv :: env) b βEv
    else return false
  | .app =>
    let f := nd.children[0]!
    let φ := nd.children[1]!
    let a := nd.children[2]!
    let φNd ← getNode φ
    if φNd.tag == .fn then
      let α := φNd.children[0]!
      let β := φNd.children[1]!
      let αEv ← evalM α
      let cf ← checkLeanD dbtypes env f φ
      let ca ← checkLeanD dbtypes env a αEv
      if cf && ca then
        let subRes ← liftM (subIdx a β)
        let subEv ← evalM subRes
        cumeqLean subEv τ
      else return false
    else return false
  | .fn =>
    let τNd ← getNode τ
    if τNd.tag == .typ then
      let α := nd.children[0]!
      let β := nd.children[1]!
      let cα ← checkLeanD dbtypes env α τ
      if cα then
        let αEv ← evalM α
        checkLeanD dbtypes (αEv :: env) β τ
      else return false
    else return false
  | .prod =>
    let τNd ← getNode τ
    if τNd.tag == .typ then
      let α := nd.children[0]!
      let β := nd.children[1]!
      let cα ← checkLeanD dbtypes env α τ
      if cα then
        let αEv ← evalM α
        let u0Idx ← liftM (typ 0)
        let auxFn ← liftM (fn αEv u0Idx)
        let auxFnEv ← evalM auxFn
        checkLeanD dbtypes env β auxFnEv
      else return false
    else return false
  | .sum =>
    let τNd ← getNode τ
    if τNd.tag == .typ then
      let α := nd.children[0]!
      let β := nd.children[1]!
      let cα ← checkLeanD dbtypes env α τ
      if cα then checkLeanD dbtypes env β τ else return false
    else return false
  | .eq =>
    let τNd ← getNode τ
    if τNd.tag == .typ then
      let a := nd.children[0]!
      let aPrime := nd.children[1]!
      let α := nd.children[2]!
      let αEv ← evalM α
      let ca ← checkLeanD dbtypes env a αEv
      if ca then
        let cap ← checkLeanD dbtypes env aPrime αEv
        if cap then checkLeanD dbtypes env α τ else return false
      else return false
    else return false
  | .fls =>
    let τNd ← getNode τ
    return (τNd.tag == .typ)
  | .typ =>
    let τNd ← getNode τ
    if τNd.tag == .typ then
      return (nd.payload + 1) ≤ τNd.payload
    else return false
  | .opq =>
    -- Opaque reference: look up registered type in builder's theoremAlist.
    let b ← liftM (m := BuilderM) get
    match b.theoremAlist.find? (fun (op, _, _, _) => op == t) with
    | some (_, ty, _, _) =>
      let tyEv ← evalM ty
      cumeqLean tyEv τ
    | none => return false
  | _ =>
    -- Built-in constant: dbtype lookup.
    let tag := nd.tag.toNat
    match dbtypes.find? (·.1 == tag) with
    | some (_, dbtIdx) =>
      let dbtEv ← evalM dbtIdx
      cumeqLean dbtEv τ
    | none => return false

/-- Run `checkLeanD` over a translator-produced build. -/
def runCheckWithDbtypes (build : BuilderM (Nat × Nat × List (Nat × Nat))) :
    (Bool × Builder × EvalState × List (Nat × Nat)) :=
  let ((termIdx, typeIdx, dbtypes), b1) := build.run {}
  let prog : EvalM Bool := do
    let τEv ← evalM typeIdx
    checkLeanD dbtypes [] termIdx τEv
  let ((ok, evalState), b2) := (prog.run {}).run b1
  (ok, b2, evalState, dbtypes)

/-- Debug variant of `checkLeanD` that prints the first failure encountered. -/
partial def checkLeanDebug (dbtypes : List (Nat × Nat))
    (env : List Nat) (t τ : Nat) : EvalM (Bool × String) := do
  let nd ← getNode t
  match nd.tag with
  | .var =>
    let x := nd.payload
    if h : x < env.length then
      let envType := env[x]
      let lifted ← liftM (incrIdx (x + 1) envType)
      let liftedEv ← evalM lifted
      let ok ← cumeqLean liftedEv τ
      if ok then return (true, "")
      else return (false, s!"var {x}: incr'd env entry #{liftedEv} ≠ τ #{τ}")
    else return (false, s!"var {x} out of bounds (env size {env.length})")
  | .lam =>
    let τNd ← getNode τ
    if τNd.tag == .fn then
      let α := τNd.children[0]!
      let β := τNd.children[1]!
      let b := nd.children[0]!
      let αEv ← evalM α
      let βEv ← evalM β
      checkLeanDebug dbtypes (αEv :: env) b βEv
    else return (false, s!"lam #{t} but τ #{τ} has tag {τNd.tag.toNat}, not fn")
  | .app =>
    let f := nd.children[0]!
    let φ := nd.children[1]!
    let a := nd.children[2]!
    let φNd ← getNode φ
    if φNd.tag == .fn then
      let α := φNd.children[0]!
      let β := φNd.children[1]!
      let αEv ← evalM α
      let (cf, why) ← checkLeanDebug dbtypes env f φ
      if !cf then return (false, s!"app #{t}: f #{f} doesn't match φ #{φ}: {why}")
      let (ca, why) ← checkLeanDebug dbtypes env a αEv
      if !ca then return (false, s!"app #{t}: a #{a} doesn't match α #{αEv}: {why}")
      let subRes ← liftM (subIdx a β)
      let subEv ← evalM subRes
      let ok ← cumeqLean subEv τ
      if ok then return (true, "")
      else return (false, s!"app #{t}: sub-eval #{subEv} ≠ τ #{τ}")
    else return (false, s!"app #{t}: φ #{φ} has tag {φNd.tag.toNat}, not fn")
  | .opq =>
    -- Opaque reference: look up registered type in builder's theoremAlist.
    let b ← liftM (m := BuilderM) get
    match b.theoremAlist.find? (fun (op, _, _, _) => op == t) with
    | some (_, ty, _, name) =>
      let tyEv ← evalM ty
      let ok ← cumeqLean tyEv τ
      if ok then return (true, "")
      else return (false, s!"opaque #{t} ({name}): registered type #{tyEv} ≠ τ #{τ}")
    | none => return (false, s!"opaque #{t}: not in theorem-alist")
  | _ =>
    -- Built-in constant: dbtype lookup.
    let tag := nd.tag.toNat
    match dbtypes.find? (·.1 == tag) with
    | some (_, dbtIdx) =>
      let dbtEv ← evalM dbtIdx
      let ok ← cumeqLean dbtEv τ
      if ok then return (true, "")
      else return (false, s!"built-in #{t} (tag {tag}): dbtype #{dbtEv} ≠ τ #{τ}")
    | none =>
      -- For non-built-in: fall back to type-position checker via checkLeanD
      let ok ← checkLeanD dbtypes env t τ
      if ok then return (true, "")
      else return (false, s!"non-app/var/lam #{t} (tag {tag}): rejected by checkLeanD vs τ #{τ}")

def runCheckDebug (build : BuilderM (Nat × Nat × List (Nat × Nat))) :
    (Bool × String × Builder) :=
  let ((termIdx, typeIdx, dbtypes), b1) := build.run {}
  let prog : EvalM (Bool × String) := do
    -- Verify each registered theorem's body before the main term.
    let bld ← liftM (m := BuilderM) get
    let mut firstFail : Option (Bool × String) := none
    for (_, ty, proof, name) in bld.theoremAlist do
      if firstFail.isNone then
        let τEv ← evalM ty
        let res ← checkLeanDebug dbtypes [] proof τEv
        if !res.1 then
          firstFail := some (false, s!"opaque theorem '{name}' body fails: {res.2}")
    match firstFail with
    | some r => return r
    | none =>
      let τEv ← evalM typeIdx
      checkLeanDebug dbtypes [] termIdx τEv
  let (((ok, why), _evalState), b2) := (prog.run {}).run b1
  (ok, why, b2)

end Cert
