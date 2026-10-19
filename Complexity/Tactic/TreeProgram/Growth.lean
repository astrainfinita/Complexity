/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Tactic.TreeProgram.Rules
public import Complexity.Encoding.TreeSize
public meta import Lean.Elab.Tactic.Omega.Frontend

/-! # Closing growth comparisons

`dominated` proves `Dominated f g` when both sides are given, as left by `source_fun_prop` and
`model_fun_prop`. It never changes either side. Sums and maxima on the left are split; each
summand is compared with the target pointwise after destructuring the input, splitting the
source cases, expanding encoded sizes and adding size facts for `omega`; powers and products are
compared through their bases. Maxima over lists and sums over tables are compared entry by entry.
The coefficient is a hidden witness. The list names definitions to unfold in the pointwise
goals, and statements `a ≤ b` or `a = b` to instantiate at matching terms there, as for those
registered with `@[dominated]`; facts that are genuine properties of the source function are
`Dominated` hypotheses, matched reducibly. Like `omega`, the pointwise step reads the other
hypotheses without changing them. Every comparison is settled once per call.
Summands that cannot be proved are left as goals.
-/

public meta section

open Lean Meta Elab Tactic

namespace Complexity.TreeProgram.Source.Growth

/-- The left side of a statement `l ≤ r` or `l = r`. -/
def lhs? (e : Lean.Expr) : Option Lean.Expr :=
  if e.isAppOfArity ``LE.le 4 || e.isAppOfArity ``Eq 3 then some e.appFn!.appArg! else none

/-- The instance of the statement `e : ∀ xs, l ≤ r` (or `l = r`) whose left side is `t`, stated
with `t` itself. -/
def instanceAt (e t : Lean.Expr) : MetaM (Option Lean.Expr) := withoutModifyingState do
  let (xs, bis, body) ← forallMetaTelescopeReducing (← inferType e)
  let some l := lhs? body | return none
  unless ← withReducible (isDefEq l t) do return none
  for x in xs, bi in bis do
    if bi.isInstImplicit && !(← x.mvarId!.isAssigned) then
      let some i ← synthInstance? (← inferType x) | return none
      x.mvarId!.assign i
  let h ← instantiateMVars (mkAppN e xs)
  if h.hasMVar then return none
  let body ← instantiateMVars body
  return some (← mkExpectedTypeHint h (mkApp2 body.appFn!.appFn! t body.appArg!))

/-- The hypotheses of `goal` introduced by the pointwise step, that is, not among `outer`. -/
def ownHyps (outer : FVarIdSet) (goal : MVarId) : MetaM (Array FVarId) :=
  return (← goal.getNondepPropHyps).filter (!outer.contains ·)

/-- Facts about every encoded size, list length and positive power occurring in the goal or in the
hypotheses introduced by the pointwise step, and the instances of the given statements and those
registered with `@[dominated]` at matching terms. -/
def addSizeFacts (outer : FVarIdSet) (lemmas : Array Lean.Expr) (goal : MVarId) : MetaM MVarId :=
  goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let mut exprs := #[target]
  for fvarId in ← ownHyps outer goal do exprs := exprs.push (← instantiateMVars (← fvarId.getType))
  let mut tree : DiscrTree Lean.Expr := {}
  for e in lemmas ++ (← (dominatedAttr.getState (← getEnv)).mapM (mkConstWithFreshMVarLevels ·)) do
    let (_, _, body) ← forallMetaTelescopeReducing (← inferType e)
    if let some l := lhs? body then tree ← tree.insert l e
  let visit (e : Lean.Expr) : StateT (Array Lean.Expr × Array Lean.Expr × Array (Lean.Expr × Nat) ×
      Array (Lean.Expr × Lean.Expr)) MetaM Unit := do
    if e.hasLooseBVars then return
    if e.isAppOfArity ``Tree.size 1 then
      modify fun (s, l, p, a) => (s.push e.appArg!, l, p, a)
      let t := e.appArg!
      if t.isAppOfArity ``UniqueEncoding.encode 4 then
        let v := t.appArg!
        if v.isAppOfArity ``HAppend.hAppend 6 then
          modify fun (s, l, p, a) => (s, l, p, a.push (v.getAppArgs[4]!, v.getAppArgs[5]!))
    else if e.isAppOfArity ``List.length 2 then
      modify fun (s, l, p, a) => (s, l.push e.appArg!, p, a)
    else if e.isAppOfArity ``HPow.hPow 6 then
      if let some k := e.appArg!.nat? then
        if k > 0 then modify fun (s, l, p, a) => (s, l, p.push (e.getAppArgs[4]!, k), a)
  let (_, (sizes, lengths, powers, appends)) ← (exprs.forM fun e => e.forEach' fun e => do
      visit e; return true : StateT _ MetaM Unit).run (#[], #[], #[], #[])
  let mut facts : Array Lean.Expr := #[]
  for t in sizes.toList.eraseDups do
    facts := facts.push (← mkAppM ``Tree.size_pos #[t])
    if t.isAppOfArity ``UniqueEncoding.encode 4 then
      if ← isDefEq (← inferType t.appArg!) (mkConst ``Bool) then
        facts := facts.push (← mkAppM ``size_encode_bool_le #[t.appArg!])
  for t in sizes.toList.eraseDups do
    if t.isAppOfArity ``UniqueEncoding.encode 4 then
      if let some h ← observing? (mkAppM ``card_le_size_encode_fin_function #[t.appArg!]) then
        facts := facts.push h
      let v := t.appArg!
      let type ← whnfR (← inferType v)
      if type.isConstOf ``Nat && v.nat?.isNone then
        facts := facts.push (← mkAppM ``size_encode_nat_le #[v])
        if v.isAppOfArity ``Fin.val 2 then facts := facts.push (← mkAppM ``Fin.isLt #[v.appArg!])
      if type.isForall && !type.bindingBody!.hasLooseBVars then
        if (← whnfR type.bindingDomain!).isAppOfArity ``Fin 1 &&
            (← whnfR type.bindingBody!).isAppOfArity ``Fin 1 then
          if let some h ← observing? (mkAppM ``size_encode_fin_table_le #[v]) then
            facts := facts.push h
  for l in lengths.toList.eraseDups do
    if let some h ← observing? (mkAppM ``length_le_codeSize #[l]) then facts := facts.push h
  for (b, k) in powers.toList.eraseDups do
    let hk ← mkDecideProof (← mkAppM ``Ne #[mkNatLit k, mkNatLit 0])
    if let some h ← observing? (mkAppOptM ``Nat.le_self_pow #[mkNatLit k, hk, b]) then
      facts := facts.push h
  for (xs, ys) in appends.toList.eraseDups do
    if let some h ← observing? (mkAppM ``size_encode_list_append #[xs, ys]) then
      facts := facts.push h
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let type ← instantiateMVars decl.type
    if type.isAppOfArity ``Membership.mem 5 then
      if let some h ← observing? (mkAppM ``size_encode_le_list_of_mem #[decl.toExpr]) then
        facts := facts.push h
  -- The terms of the goal, then for a few rounds those of the instances found.
  let subterms (e : Lean.Expr) : MetaM (Array Lean.Expr) := do
    let (_, ts) ← (e.forEach' fun e => do
        if e.isApp && !e.hasLooseBVars then modify (·.push e)
        return true : StateT (Array Lean.Expr) MetaM Unit).run #[]
    return ts
  let mut seen : Std.HashSet Lean.Expr := {}
  let mut pending := #[]
  for e in exprs do pending := pending ++ (← subterms e)
  for _ in [0:3] do
    let mut found := #[]
    for t in pending do
      if seen.contains t then continue
      seen := seen.insert t
      for e in ← tree.getMatch t do
        if let some h ← instanceAt e t then
          facts := facts.push h
          found := found ++ (← subterms (← inferType h))
    pending := found
  let mut goal := goal
  for h in facts do
    let (_, g) ← (← goal.assert `size_fact (← inferType h) h).intro1P
    goal := g
  return goal

/-- For powers `a ^ d` and `b ^ e` in the goal with `d ≤ e`, add `a ^ d ≤ k ^ d * b ^ e` whenever
`a` is `b` or `omega` proves `a ≤ k * b`, and `omega` proves `0 < b`; for a product `a * b` and a
power `c ^ e` with `2 ≤ e`, add `a * b ≤ k * l * c ^ e` whenever `omega` proves `a ≤ k * c`,
`0 < c`, and `b ≤ l * c` or `b ≤ l * c ^ d` for a power `c ^ d` of the goal with `d < e`. The
coefficients are 1, 2, 4 or 8. -/
def addPowerFacts (goal : MVarId) : TacticM MVarId := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let visit (e : Lean.Expr) : StateT (Array (Lean.Expr × Nat) × Array (Lean.Expr × Lean.Expr))
      MetaM Unit := do
    unless !e.hasLooseBVars && (e.isAppOfArity ``HPow.hPow 6 || e.isAppOfArity ``HMul.hMul 6) do
      return
    unless ← isDefEq (← inferType e) (mkConst ``Nat) do return
    if e.isAppOfArity ``HPow.hPow 6 then
      if let some k := e.appArg!.nat? then
        if k > 0 then modify fun (p, m) => (p.push (e.getAppArgs[4]!, k), m)
    else if e.isAppOfArity ``HMul.hMul 6 then
      let (a, b) := (e.getAppArgs[4]!, e.appArg!)
      if a.nat?.isNone && b.nat?.isNone then modify fun (p, m) => (p, m.push (a, b))
  let mut exprs := #[target]
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do exprs := exprs.push (← instantiateMVars decl.type)
  let mut found := #[]
  let mut products := #[]
  for e in exprs do
    let (_, (p, m)) ← (e.forEach' fun e => do
        visit e; return true : StateT _ MetaM Unit).run (#[], #[])
    found := found ++ p
    products := products ++ m
  let powers := found.toList.eraseDups
  let byOmega (p : Lean.Expr) : TacticM (Option Lean.Expr) := do
    let m ← mkFreshExprSyntheticOpaqueMVar p
    let saved ← saveState
    try
      setGoals [m.mvarId!]
      Omega.omegaDefault
      return some (← instantiateMVars m)
    catch _ =>
      saved.restore
      return none
  let le (a b : Lean.Expr) := do byOmega (← mkAppM ``LE.le #[a, b])
  let pos (a : Lean.Expr) := do byOmega (← mkAppM ``LT.lt #[mkNatLit 0, a])
  let powLe (hb : Lean.Expr) (d e : Nat) := do
    mkAppM ``Nat.pow_le_pow_right
      #[hb, ← mkDecideProof (← mkAppM ``LE.le #[mkNatLit d, mkNatLit e])]
  let mut facts := #[]
  for (a, d) in powers do
    for (b, e) in powers do
      if d > e || (a == b && d == e) then continue
      let some hb ← pos b | continue
      if a == b then
        facts := facts.push (← powLe hb d e)
        continue
      if let some hab ← le a b then
        facts := facts.push (← mkAppM ``le_trans
          #[← mkAppM ``Nat.pow_le_pow_left #[hab, mkNatLit d], ← powLe hb d e])
        continue
      -- A coefficient `k` on the base becomes the literal `k ^ d` on the power.
      for k in [2, 4, 8] do
        let some hab ← le a (← mkAppM ``HMul.hMul #[mkNatLit k, b]) | continue
        let scaled ← mkAppM ``le_trans #[← mkAppM ``Nat.pow_le_pow_left #[hab, mkNatLit d],
          ← mkAppM ``Eq.le #[← mkAppM ``Nat.mul_pow #[mkNatLit k, b, mkNatLit d]]]
        let h ← mkAppM ``le_trans #[scaled, ← mkAppM ``Nat.mul_le_mul_left
          #[← mkAppM ``HPow.hPow #[mkNatLit k, mkNatLit d], ← powLe hb d e]]
        let type ← mkAppM ``LE.le #[← mkAppM ``HPow.hPow #[a, mkNatLit d],
          ← mkAppM ``HMul.hMul #[mkNatLit (k ^ d), ← mkAppM ``HPow.hPow #[b, mkNatLit e]]]
        facts := facts.push (← mkExpectedTypeHint h type)
        break
  -- The least of the coefficients 1, 2, 4, 8 with `a ≤ k * c`, with its proof.
  let coefficient (a c : Lean.Expr) : TacticM (Option Lean.Expr) := do
    for k in [1, 2, 4, 8] do
      if let some h ← le a (← mkAppM ``HMul.hMul #[mkNatLit k, c]) then return some h
    return none
  for (a, b) in products.toList.eraseDups do
    for (c, e) in powers do
      if e < 2 then continue
      let some hc ← pos c | continue
      let some hac ← coefficient a c | continue
      if let some hbc ← coefficient b c then
        let he ← mkDecideProof (← mkAppM ``LE.le #[mkNatLit 2, mkNatLit e])
        facts := facts.push (← mkAppM ``mul_le_mul_pow_of_le_mul #[hac, hbc, he, hc])
        continue
      for (c', d) in powers do
        unless c' == c && 1 < d && d < e do continue
        let some hbc ← coefficient b (← mkAppM ``HPow.hPow #[c, mkNatLit d]) | continue
        let he ← mkDecideProof (← mkAppM ``LE.le #[mkNatLit (d + 1), mkNatLit e])
        facts := facts.push (← mkAppM ``mul_le_mul_pow_of_le_mul_pow #[hac, hbc, he, hc])
        break
  let mut goal := goal
  for h in facts do
    let (_, g) ← (← goal.assert `power_fact (← inferType h) h).intro1P
    goal := g
  return goal

/-! ### Rewriting in the pointwise step

The pointwise step introduces the input, destructures it and splits its cases. As with `omega` and
`linarith`, the hypotheses it finds are read but not changed: only the goal and the hypotheses it
introduces are rewritten. The input is new, so no other hypothesis can mention it. -/

/-- A simp context with the given lemmas and definitions to unfold only. -/
def simpContext (names : Array Name) (unfolds : Array Name := #[]) : MetaM Simp.Context := do
  let mut thms : SimpTheorems := {}
  for name in names do thms ← thms.addConst name
  for name in unfolds do thms ← thms.addDeclToUnfold name
  Simp.mkContext (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)

/-- Simplify the goal and the hypotheses introduced by the pointwise step; `none` if the goal is
closed. A simplification that fails or changes nothing keeps the goal. -/
def simpOwn (outer : FVarIdSet) (ctx : Simp.Context) (goal : MVarId)
    (simprocs : Simp.SimprocsArray := #[]) : MetaM (Option MVarId) := do
  try
    let (r, _) ← simpGoal goal ctx simprocs (fvarIdsToSimp := ← ownHyps outer goal)
    return r.map (·.2)
  catch _ => return some goal

/-- `dsimp` the goal, and the hypotheses introduced by the pointwise step when `outer` is given;
`none` if the goal is closed. -/
def dsimpOwn (ctx : Simp.Context) (goal : MVarId) (outer : Option FVarIdSet := none) :
    MetaM (Option MVarId) := do
  try
    let fvars ← match outer with | some outer => ownHyps outer goal | none => pure #[]
    return (← dsimpGoal goal ctx (fvarIdsToSimp := fvars)).1
  catch _ => return some goal

/-- Use the equations left by splitting a `match`: an equation between constructor applications
is substituted, and the goal is closed when `cases` on an equation leaves no cases, as for a
branch that contradicts the test selecting it. -/
partial def casesEquations (outer : FVarIdSet) (goal : MVarId) : MetaM (Array MVarId) :=
  goal.withContext do
  for decl in ← getLCtx do
    let type ← instantiateMVars decl.type
    if decl.isImplementationDetail || outer.contains decl.fvarId || !type.isAppOfArity ``Eq 3 then
      continue
    let constructor (e : Lean.Expr) : MetaM Bool := do
      let some name := (← whnfR e).getAppFn.constName? | return false
      return (← getEnv).find? name |>.any (·.isCtor)
    let injective := (← constructor type.appFn!.appArg!) && (← constructor type.appArg!)
    let saved ← saveState
    try
      let goals ← goal.cases decl.fvarId
      if goals.isEmpty then return #[]
      if let #[g] := goals then
        if injective then return ← casesEquations outer g.mvarId
    catch _ => pure ()
    saved.restore
  return #[goal]

/-- Split the first `casesOn` or `rec` application on a local variable in the goal. -/
def casesOnVariable (goal : MVarId) : MetaM (Option (Array MVarId)) := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let collect (e : Lean.Expr) : StateT (Array (Name × Lean.Expr)) MetaM Bool := do
    if let .const name _ := e.getAppFn then
      if name.isStr && (name.getString! == "casesOn" || name.getString! == "rec") then
        for a in e.getAppArgs do
          if a.isFVar then modify (·.push (name.getPrefix, a))
    return true
  let (_, candidates) ← (target.forEach' collect).run #[]
  for (family, major) in candidates do
    let type ← whnfR (← inferType major)
    unless type.getAppFn.isConstOf family do continue
    return some ((← goal.cases major.fvarId!).map (·.mvarId))
  return none

/-- Split the `match`, `if`, `casesOn` and `rec` applications of the goal, `dsimp`ing each case. -/
partial def splitAll (goal : MVarId) : MetaM (Array MVarId) := do
  let split? ← try splitTarget? goal catch _ => pure none
  let goals? ← match split? with
    | some goals => pure (some goals.toArray)
    | none => casesOnVariable goal
  let some goals := goals? | return #[goal]
  let plain ← simpContext #[]
  let mut out := #[]
  for g in goals do
    if let some g ← dsimpOwn plain g then out := out ++ (← splitAll g)
  return out

/-- Split the variables introduced by the pointwise step whose type is, up to reducible
unfolding, a product, dependent pair, subtype, unit, or a structure with a derived tree
encoding. -/
partial def destructure (outer : FVarIdSet) (goal : MVarId) : MetaM (Array MVarId) :=
  goal.withContext do
  for decl in ← getLCtx do
    if decl.isImplementationDetail || outer.contains decl.fvarId then continue
    let type ← whnfR decl.type
    let encodeMk := type.getAppFn.constName? |>.map (· ++ `encode_mk)
    let derived := encodeMk.any (← getEnv).contains
    if derived || [``Prod, ``Sigma, ``PSigma, ``Subtype, ``PProd, ``PUnit].any
        type.getAppFn.isConstOf then
      let mut out := #[]
      for g in ← goal.cases decl.fvarId do out := out ++ (← destructure outer g.mvarId)
      return out
  return #[goal]

/-- Rewrite the encoding of every constructor application of a type with a derived tree encoding
to the encoding of its fields. -/
def encodeFields (outer : FVarIdSet) (goal : MVarId) : MetaM (Option MVarId) := goal.withContext do
  let env ← getEnv
  let mut exprs := #[← instantiateMVars (← goal.getType)]
  for fvarId in ← ownHyps outer goal do exprs := exprs.push (← instantiateMVars (← fvarId.getType))
  let names := exprs.foldl (init := #[]) fun acc e => e.foldConsts acc fun c acc =>
    let encodeCtor := c.getPrefix ++ .mkSimple s!"encode_{c.getString!}"
    if c.isStr && (env.find? c).any (·.isCtor) && env.contains encodeCtor &&
        !acc.contains encodeCtor then
      acc.push encodeCtor else acc
  if names.isEmpty then return some goal
  simpOwn outer (← simpContext (#[``size_encode_prod] ++ names)) goal

/-- Reduce natural-number projections in the types of the variables introduced by the pointwise
step, as in the indices of a recursive result's type, and state each encoding at the inferred
type of the encoded value, so that the size of a dependent recursive result is one `omega` atom
and its pairs expand, however its type was reached. -/
def normalizeEncodings (outer : FVarIdSet) (goal : MVarId) : MetaM MVarId := goal.withContext do
  let isProjection (t : Lean.Expr) : MetaM Bool := do
    if t.isProj then return true
    let some name := t.getAppFn.constName? | return false
    let some info ← getProjectionFnInfo? name | return false
    return !info.fromClass && t.getAppNumArgs > info.numParams
  let reduce (e : Lean.Expr) : MetaM Lean.Expr := do
    Meta.transform (← instantiateMVars e) (post := fun t => do
      if !t.hasLooseBVars && (← isProjection t) &&
          (← whnfR (← inferType t)).isConstOf ``Nat then
        let r ← whnf t
        unless ← isProjection r do return .done r
      return .continue)
  let normalize (e : Lean.Expr) : MetaM Lean.Expr := do
    Meta.transform (← instantiateMVars e) (post := fun t => do
      if t.isAppOfArity ``UniqueEncoding.encode 4 && !t.hasLooseBVars then
        let args := t.getAppArgs
        let type ← instantiateMVars (← inferType t.appArg!)
        if type != args[1]! then
          if let some inst ← synthInstance? (← mkAppM ``UniqueEncoding #[args[0]!, type]) then
            return .done (mkAppN t.getAppFn #[args[0]!, type, inst, args[3]!])
      return .continue)
  let mut goal := goal
  for decl in ← getLCtx do
    if decl.isImplementationDetail || outer.contains decl.fvarId || (← isProp decl.type) then
      continue
    let type ← reduce decl.type
    if type != decl.type then goal ← goal.replaceLocalDeclDefEq decl.fvarId type
  for fvarId in ← goal.withContext (ownHyps outer goal) do
    let old ← goal.withContext do instantiateMVars (← fvarId.getType)
    let type ← goal.withContext do normalize old
    if type != old then goal ← goal.replaceLocalDeclDefEq fvarId type
  goal.replaceTargetDefEq (← goal.withContext do normalize (← goal.getType))

/-! ### The solver

`dominated` follows the structure of `positivity` and `fun_prop`: a recursive function builds
proof terms, with the facts of the call in a reader context and the settled comparisons in a
cache. The pointwise step `sizeOmega` plays the part of a discharger. -/

/-- The facts and the list of one `dominated` call. -/
structure Context where
  /-- Statements `a ≤ b` or `a = b` to instantiate at matching terms in the pointwise step. -/
  lemmas : Array Lean.Expr
  /-- `Dominated` facts with their types, compositions unfolded. -/
  facts : Array (Lean.Expr × Lean.Expr)
  /-- Expansion of encoded sizes on the left side. -/
  sizes : Simp.Context
  /-- The same, also distributing the table length over an entry. -/
  sizesMul : Simp.Context
  /-- Expansion of encoded sizes in the pointwise step, unfolding the definitions of the list. -/
  expand : Simp.Context
  /-- Numeral arithmetic used with `expand`, so that exponents such as `2 * 3` become literals. -/
  numerals : Simp.SimprocsArray
  /-- The default simp set with the same definitions, tried when `expand` is not enough. -/
  expandAll : Simp.Context

/-- Comparisons settled during one call, and the summands left to the user. -/
structure State where
  /-- Settled `Dominated` goals and positivity propositions: a proof, or `none` for a failure. -/
  cache : Std.HashMap Lean.Expr (Option Lean.Expr) := {}
  /-- Summands left as goals, by type. -/
  left : Array (Lean.Expr × MVarId) := #[]

/-- The solver monad: one context and one cache per `dominated` call. -/
abbrev DominatedM := ReaderT Context (StateRefT State TacticM)

/-- Settle `p` once per call. A proof that still has metavariables is not kept, since a later
backtracking step could unassign them. -/
def memo (p : Lean.Expr) (k : DominatedM (Option Lean.Expr)) : DominatedM (Option Lean.Expr) := do
  let p ← instantiateMVars p
  if let some r := (← get).cache[p]? then return r
  let r ← match ← k with
    | some proof => pure (some (← instantiateMVars proof))
    | none => pure none
  unless r.any (·.hasMVar) do modify fun s => { s with cache := s.cache.insert p r }
  return r

/-- Run a rule; an exception counts as a failure and leaves no trace. -/
def attempt (k : DominatedM (Option Lean.Expr)) : DominatedM (Option Lean.Expr) := do
  let saved ← show TacticM _ from saveState
  try k catch _ =>
    saved.restore
    return none

/-- Run `tac` on `goal`; keep its assignments only if it closes the goal. -/
def closes (goal : MVarId) (tac : TacticM Unit) : TacticM Bool := do
  let saved ← saveState
  let goals ← getGoals
  try
    setGoals [goal]
    tac
    if (← getGoals).isEmpty then
      setGoals goals
      return true
  catch _ => pure ()
  saved.restore
  return false

/-- Prove `type` by applying `rule` reducibly and settling each new goal with `prove`. -/
def viaRule (rule : Name) (type : Lean.Expr)
    (prove : Lean.Expr → DominatedM (Option Lean.Expr)) : DominatedM (Option Lean.Expr) :=
  attempt do
    let goal ← mkFreshExprSyntheticOpaqueMVar type
    for sub in ← withReducible (goal.mvarId!.apply (← mkConstWithFreshMVarLevels rule)) do
      let some proof ← prove (← instantiateMVars (← sub.getType)) | throwError "no proof"
      sub.assign proof
    return some (← instantiateMVars goal)

/-- The domain of a function. -/
def domainOf (f : Lean.Expr) : MetaM Lean.Expr := do
  return (← whnf (← inferType f)).bindingDomain!

/-- Close one case of the pointwise step by `omega` with the size and power facts, expanding the
encoded sizes that splitting has exposed, or else after simplifying with the default simp set. -/
def closeCase (outer : FVarIdSet) (goal : MVarId) : DominatedM Bool := do
  let ctx ← read
  let finish (goal : Option MVarId) : TacticM Unit := do
    setGoals goal.toList
    unless goal.isNone do Omega.omegaDefault
  if ← closes goal do
      let some g ← simpOwn outer ctx.expand (← addSizeFacts outer ctx.lemmas goal) ctx.numerals
        | setGoals []
      finish (some (← addPowerFacts g)) then
    return true
  closes goal do
    let some g ← simpOwn outer ctx.expandAll goal #[← Simp.getSimprocs] | setGoals []
    finish (← simpOwn outer ctx.sizes (← addSizeFacts outer ctx.lemmas g))

/-- The pointwise step: prove `goal : ∀ x, p x` by destructuring `x`, splitting its cases,
expanding encoded sizes and closing each case with `closeCase`. -/
def sizeOmega (goal : MVarId) : DominatedM Bool := do
  let ctx ← read
  let outer ← goal.withContext do return (← getLCtx).foldl (·.insert ·.fvarId) {}
  let plain ← simpContext #[]
  let ids ← simpContext #[] #[``id]
  let (_, goal) ← goal.intro1
  let mut goals := #[]
  for g in ← destructure outer goal do
    if let some g ← dsimpOwn plain g then goals := goals ++ (← splitAll g)
  for g in goals do
    let some g ← encodeFields outer g | continue
    for g in ← casesEquations outer g do
      let some g ← dsimpOwn ids g outer | continue
      let some g ← simpOwn outer ctx.expand (← normalizeEncodings outer g) ctx.numerals
        | continue
      let some g ← encodeFields outer g | continue
      for g in ← splitAll (← normalizeEncodings outer g) do
        unless ← closeCase outer g do return false
  return true

/-- Prove `∀ x, p x` with `sizeOmega`, where `p x` relates `f x` and `g x`. -/
def bySizeOmega (f : Lean.Expr) (p : Lean.Expr → MetaM Lean.Expr) :
    DominatedM (Option Lean.Expr) := do
  let type ← withLocalDeclD `x (← domainOf f) fun x => do mkForallFVars #[x] (← p x)
  let h ← mkFreshExprSyntheticOpaqueMVar type
  let saved ← show TacticM _ from saveState
  try
    if ← sizeOmega h.mvarId! then return some h
  catch _ => pure ()
  saved.restore
  return none

/-- `Dominated f g` pointwise, with the hidden coefficient `2 ^ 40`. -/
def pointwise (f g : Lean.Expr) : DominatedM (Option Lean.Expr) := do
  let C := mkNatLit 1099511627776
  let some h ← bySizeOmega f fun x => do
      mkAppM ``LE.le #[(mkApp f x).headBeta, ← mkAppM ``HMul.hMul #[C, (mkApp g x).headBeta]]
    | return none
  return some (← mkAppM ``Dominated.of_le_mul #[C, h])

/-- `∀ x, 0 < g x`, from a hypothesis or pointwise. -/
def positive (g : Lean.Expr) : DominatedM (Option Lean.Expr) := do
  let p ← withLocalDeclD `x (← domainOf g) fun x => do
    mkForallFVars #[x] (← mkAppM ``LT.lt #[mkNatLit 0, (mkApp g x).headBeta])
  memo p do
    for decl in ← getLCtx do
      if !decl.isImplementationDetail && (← withReducible (isDefEq decl.type p)) then
        return some decl.toExpr
    bySizeOmega g fun x => mkAppM ``LT.lt #[mkNatLit 0, (mkApp g x).headBeta]

/-- `Dominated f g` without facts: the target itself, a constant, or a pointwise bound. A
constant is recognized syntactically, after the left side is normalized: recognizing one by
unfolding definitions would leave a costly definitional equality in the proof. -/
def proveBase (f g : Lean.Expr) : DominatedM (Option Lean.Expr) := do
  if ← withReducible (isDefEq f g) then return some (← mkAppM ``Dominated.refl #[g])
  if let .lam _ _ body _ := f then
    if !body.hasLooseBVars then
      if let some h ← positive g then
        return some (← mkAppM ``Dominated.const_of_pos #[body, h])
  pointwise f g

/-- Unfold compositions, so that matching a fact is reducible and cheap to fail. -/
def unfoldComp (e : Lean.Expr) : MetaM Lean.Expr := Meta.transform e (post := fun t => do
  if t.isAppOfArity ``Function.comp 5 then
    let args := t.getAppArgs
    return .done (← withLocalDeclD `x args[0]! fun x => do
      mkLambdaFVars #[x] (mkApp args[3]! (mkApp args[4]! x).headBeta).headBeta)
  return .continue)

/-- `Dominated f g` through a fact `Dominated f g'`: directly when `g'` is `g`, otherwise with
`Dominated g' g` from `proveBase`, so facts are never chained. On the element domain of a
traversal, a fact about the outer input is used along the projection to that input. -/
def viaFacts (f g : Lean.Expr) : DominatedM (Option Lean.Expr) := do
  let domain ← whnfR (← domainOf f)
  let projection? : Option Lean.Expr ←
    if domain.isAppOf ``Sigma then
      some <$> withLocalDeclD `z domain fun z => do
        mkLambdaFVars #[z] (← mkAppM ``Sigma.fst #[z])
    else if domain.isAppOf ``Subtype then
      (observing? (withLocalDeclD `z domain fun z => do
        mkLambdaFVars #[z] (← mkAppM ``Prod.fst #[← mkAppM ``Subtype.val #[z]])) : MetaM _)
    else pure none
  for (h, type) in (← read).facts do
    let mut candidates := #[(h, type)]
    if let some projection := projection? then
      if let some h' ← (observing? (mkAppM ``Dominated.comp #[h, projection]) : MetaM _) then
        let lam (k : Lean.Expr) := withLocalDeclD `z domain fun z => do
          mkLambdaFVars #[z] (mkApp k (mkApp projection z)).headBeta
        let composed ← mkAppM ``Dominated #[← lam type.appFn!.appArg!, ← lam type.appArg!]
        candidates := candidates.push (← mkExpectedTypeHint h' composed, composed)
    for (h, type) in candidates do
      unless ← withReducible (isDefEq type.appFn!.appArg! f) do continue
      let g' := type.appArg!
      if ← withReducible (isDefEq g' g) then return some h
      if let some rest ← memo (← mkAppM ``Dominated #[g', g]) (attempt (proveBase g' g)) then
        return some (← mkAppM ``Dominated.trans #[h, rest])
  return none

/-- Expand encoded sizes in `f` with `ctx` and split its sums, maxima and zeros; `leaf` proves
`Dominated a g` for the remaining summands `a`. The right side `g` is not rewritten. -/
partial def split (f g : Lean.Expr) (ctx : Simp.Context)
    (leaf : Lean.Expr → Lean.Expr → DominatedM (Option Lean.Expr)) :
    DominatedM (Option Lean.Expr) := do
  let (r, _) ← simp f ctx
  let rec go (f : Lean.Expr) : DominatedM (Option Lean.Expr) := do
    let .lam n α body bi := f | leaf f g
    let part (e : Lean.Expr) := Lean.Expr.lam n α e bi
    if body.isAppOfArity ``HAdd.hAdd 6 || body.isAppOfArity ``Max.max 4 then
      let some pa ← go (part body.appFn!.appArg!) | return none
      let some pb ← go (part body.appArg!) | return none
      let combine := if body.isAppOfArity ``HAdd.hAdd 6 then ``Dominated.add_same
        else ``Dominated.max_same
      return some (← mkAppM combine #[pa, pb])
    if body.nat? == some 0 then
      let zero ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``Dominated #[f, g])
      let _ ← zero.mvarId!.apply (← mkConstWithFreshMVarLevels ``Dominated.zero)
      return some (← instantiateMVars zero)
    leaf f g
  let some proof ← go r.expr | return none
  let some eq := r.proof? | return some proof
  let motive ← withLocalDeclD `F (← inferType f) fun F => do
    mkLambdaFVars #[F] (← mkAppM ``Dominated #[F, g])
  return some (← mkEqMPR (← mkCongrArg motive eq) proof)

/-- One summand against the target: a fact, the base rules, or a traversal rule; a maximum over
a list, possibly of dependent elements, is compared element by element, and a table sum entry
by entry after multiplying each entry by the table length. Traversal rules read the target on
the element domain and split the element, which must be proved completely. -/
partial def prove (f g : Lean.Expr) : DominatedM (Option Lean.Expr) := do
  memo (← mkAppM ``Dominated #[f, g]) do
    if let some h ← attempt (viaFacts f g) then return some h
    let element (ctx : Simp.Context) (type : Lean.Expr) : DominatedM (Option Lean.Expr) := do
      let type := type.consumeMData
      unless type.isAppOf ``Dominated do return none
      split type.appFn!.appArg! type.appArg! ctx prove
    let type ← mkAppM ``Dominated #[f, g]
    let ctx ← read
    for rule in [``Dominated.list_foldr_max_le, ``Dominated.foldr_max_le] do
      if let some h ← viaRule rule type (element ctx.sizes) then return some h
    if let some h ← viaRule ``Dominated.sum_finRange_of_mul type (element ctx.sizesMul) then
      return some h
    attempt (proveBase f g)

/-- Prove a summand, or leave it as a goal; equal summands share one goal. -/
def proveOrLeave (f g : Lean.Expr) : DominatedM (Option Lean.Expr) := do
  if let some h ← prove f g then return some h
  let type ← instantiateMVars (← mkAppM ``Dominated #[f, g])
  if let some (_, goal) := (← get).left.find? (·.1 == type) then return some (mkMVar goal)
  let goal ← mkFreshExprSyntheticOpaqueMVar type
  modify fun s => { s with left := s.left.push (type, goal.mvarId!) }
  return some goal

/-- Close a growth comparison `Dominated f g` whose two sides are given, splitting sums and
maxima of the left side; equal summands are proved once. Local `Dominated` hypotheses are used
as facts. The list gives definitions to unfold when comparing pointwise, and statements `a ≤ b`
or `a = b` to instantiate at matching terms there, as for those registered with `@[dominated]`.
Summands that cannot be proved are left as goals. -/
syntax (name := dominated) "dominated" (" [" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| dominated $[[$args,*]]?) => withMainContext do
    let mut unfolds := #[]
    let mut lemmas := #[]
    for arg in args.map (·.getElems) |>.getD (#[] : Array Term) do
      let e ← Term.withoutErrToSorry <| elabTermForApply arg
      let type ← inferType e
      if let some name := e.constName? then
        unless ← isProp type do
          unfolds := unfolds.push name
          continue
      let (_, _, body) ← forallMetaTelescopeReducing type
      if (lhs? body).isNone then
        throwErrorAt arg "dominated: expected a definition or a statement `a ≤ b` or `a = b`"
      lemmas := lemmas.push e
    let goal ← getMainGoal
    let target := (← instantiateMVars (← goal.getType)).consumeMData
    unless target.isAppOf ``Dominated do throwError "dominated: expected a `Dominated` goal"
    let mut facts := #[]
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let type := (← instantiateMVars decl.type).consumeMData
      if type.isAppOf ``Dominated then facts := facts.push (decl.toExpr, ← unfoldComp type)
    let sizeLemmas := #[``size_encode_prod, ``Sigma.encode_mk, ``size_encode_unit,
      ``encode_list_cons, ``encode_list_nil, ``size_encode_reverse, ``List.length_reverse,
      ``Function.comp_apply]
    let sizes ← simpContext sizeLemmas
    let sizesMul ← simpContext (sizeLemmas ++ #[``Nat.mul_add, ``Nat.mul_one, ``Nat.mul_zero])
    let expand ← simpContext (simpOnlyBuiltins.toArray ++ #[``size_encode_prod, ``Sigma.encode_mk,
      ``UniqueEncoding.encode_subtype, ``encode_list_cons, ``encode_list_nil, ``size_encode_unit,
      ``encode_bool_true, ``encode_bool_false, ``size_encode_reverse, ``List.length_reverse,
      ``List.length_cons, ``List.length_nil, ``List.length_append, ``List.length_map,
      ``Tree.encode_self, ``encode_option_some, ``encode_option_none, ``encode_fin,
      ``encode_fin_castSucc, ``Fin.val_last, ``Function.comp_apply, ``max_le_iff,
      ``List.map_const', ``List.sum_replicate, ``smul_eq_mul, ``pow_zero]) unfolds
    let mut all ← (← getSimpTheorems).addConst ``size_encode_prod
    for name in unfolds do all ← all.addDeclToUnfold name
    let expandAll ←
      Simp.mkContext (simpTheorems := #[all]) (congrTheorems := ← getSimpCongrTheorems)
    let numerals := #[← (← ({} : Simp.Simprocs).add ``Nat.reduceMul true).add ``Nat.reduceAdd true]
    let ctx : Context := { lemmas, facts, sizes, sizesMul, expand, numerals, expandAll }
    let (proof, state) ← (split target.appFn!.appArg! target.appArg! ctx.sizes proveOrLeave
      |>.run ctx).run {}
    let some proof := proof | throwError "dominated: no proof"
    goal.assign (← mkExpectedTypeHint proof target)
    replaceMainGoal (state.left.map (·.2)).toList

end Complexity.TreeProgram.Source.Growth
