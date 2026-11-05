/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Asymptotics.Nat
public import Complexity.Tactic.Dominated.Facts
public meta import Lean.Elab.Tactic.Omega.Frontend

/-! # The pointwise step of `dominated`

The statements instantiated at matching terms, linear forms and `omega` on them, the facts about
products and powers, and the rewriting of the pointwise step: destructuring the input, splitting
its cases and expanding encoded sizes. See `Complexity.Tactic.Dominated.Basic`.
-/

@[expose] public section

namespace Complexity.Tactic.Dominated

/-- A product of two quantities, each within a multiple of `c`, is within a multiple of `c ^ e`. -/
theorem mul_le_mul_pow_of_le_mul {a b c ka kb e : ℕ} (ha : a ≤ ka * c) (hb : b ≤ kb * c)
    (he : 2 ≤ e) (hc : 0 < c) : a * b ≤ ka * kb * c ^ e :=
  (Nat.mul_le_mul ha hb).trans (by
    rw [Nat.mul_mul_mul_comm, ← pow_two]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hc he))

/-- A quantity within a multiple of `c`, times one within a multiple of `c ^ d`, is within a
multiple of `c ^ e` for `d < e`. -/
theorem mul_le_mul_pow_of_le_mul_pow {a b c ka kb d e : ℕ} (ha : a ≤ ka * c)
    (hb : b ≤ kb * c ^ d) (he : d + 1 ≤ e) (hc : 0 < c) : a * b ≤ ka * kb * c ^ e :=
  (Nat.mul_le_mul ha hb).trans (by
    rw [Nat.mul_mul_mul_comm, ← pow_succ']
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hc he))

end Complexity.Tactic.Dominated

end

public meta section

open Lean Meta Elab Tactic

namespace Complexity.Tactic.Dominated

/-- The code of a pair, of a constructor application with a derived encoding, or of a value
transported along an equation (`UniqueEncoding.encode_eqRec`), by its parts. The equations are
instantiated at default transparency: the type of a dependent field, or of a transported value, can
agree with the stated one only after unfolding, which `simp`'s matching does not do. -/
def expandParts (e : Lean.Expr) : SimpM Simp.Step := withTransparency .default do
  unless e.isAppOfArity ``UniqueEncoding.encode 4 do return .continue
  let value := e.appArg!
  let some name := value.getAppFn.constName? | return .continue
  let instantiate (equation : Name) : MetaM (Option Lean.Expr) := do
    let c ← mkConstWithFreshMVarLevels equation
    let (xs, _, type) ← forallMetaTelescopeReducing (← inferType c)
    let some (_, lhs, _) := type.eq? | return none
    unless ← isDefEq lhs e do return none
    return some (← instantiateMVars (mkAppN c xs))
  let some proof ← (if value.isAppOfArity ``Eq.rec 6 then do
      let args := value.getAppArgs
      some <$> mkAppOptM ``UniqueEncoding.encode_eqRec
        #[mkConst ``Tree, args[0]!, args[1]!, args[2]!, none, args[3]!, args[4]!, args[5]!]
    else do
      unless (← getEnv).isConstructor name do return none
      let equation := if name == ``Prod.mk then ``encode_prod
        else name.getPrefix ++ .mkSimple ("encode_" ++ name.getString!)
      unless (← getEnv).contains equation do return none
      instantiate equation) | return .continue
  let some (_, lhs, rhs) := (← inferType proof).eq? | return .continue
  unless ← isDefEq lhs e do return .continue
  let rhs ← Core.betaReduce (← instantiateMVars rhs)
  return .visit { expr := rhs, proof? := some (← mkExpectedTypeHint proof (← mkEq e rhs)) }

/-- Rewrite a code by its parts (`expandParts`). -/
simproc_decl encodeParts (encode Tree _) := expandParts

/-- The two sides of a statement `l ≤ r`, `l < r` or `l = r`. -/
def sides? (e : Lean.Expr) : Option (Lean.Expr × Lean.Expr) :=
  if e.isAppOfArity ``LE.le 4 || e.isAppOfArity ``LT.lt 4 || e.isAppOfArity ``Eq 3 then
    some (e.appFn!.appArg!, e.appArg!)
  else none

/-- Which side of a statement is the term it is about. -/
inductive Side where
  /-- The left side. -/
  | left
  /-- The left side without an added literal, as in `⌜f x⌝ₜ.size + 1 = …`. -/
  | leftOfAdd
  /-- The right side, when the left side is a variable or a literal, as in `n ≤ ⌜f⌝ₜ.size` or
  `0 < t.size`. -/
  | right

/-- The term a statement `l ≤ r`, `l < r` or `l = r` is about, and which side it is. -/
def key? (e : Lean.Expr) : Option (Lean.Expr × Side) := do
  let (l, r) ← sides? e
  let (l', side) := if l.isAppOfArity ``HAdd.hAdd 6 && l.appArg!.nat?.isSome then
      (l.appFn!.appArg!, Side.leftOfAdd) else (l, .left)
  if l'.isMVar || l'.nat?.isSome then some (r, .right) else some (l', side)

/-- The instance of the statement `e : ∀ xs, l ≤ r` (or `<`, `=`) about the term `t`, stated with
`t` itself, and the other side. -/
def instanceAt (e t : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) :=
    withoutModifyingState do
  let (xs, bis, body) ← forallMetaTelescopeReducing (← inferType e)
  -- The side is read from the statement itself, not from its instance.
  let some (k, side) := key? body | return none
  unless ← withReducible (isDefEq k t) do return none
  for x in xs, bi in bis do
    if bi.isInstImplicit && !(← x.mvarId!.isAssigned) then
      let some i ← synthInstance? (← inferType x) | return none
      x.mvarId!.assign i
  let h ← instantiateMVars (mkAppN e xs)
  if h.hasMVar then return none
  let body ← instantiateMVars body
  let some (l, r) := sides? body | return none
  let rel := body.appFn!.appFn!
  -- The key side is stated with `t` itself, so that `omega` sees one atom; the other side may
  -- mention new terms, which the next round looks at.
  let (stated, other) := match side with
    | .left => (mkApp2 rel t r, r)
    | .leftOfAdd => (mkApp2 rel (mkApp2 l.appFn!.appFn! t l.appArg!) r, r)
    | .right => (mkApp2 rel l t, l)
  return some (← mkExpectedTypeHint h stated, other)

/-- The instance of the statement `e : ∀ xs, p → l ≤ r` (or `<`, `=`) at the hypothesis `h : p`,
for the first explicit premise `p` of `e`. -/
def instanceOf (e h : Lean.Expr) : MetaM (Option Lean.Expr) := withoutModifyingState do
  let (xs, bis, body) ← forallMetaTelescopeReducing (← inferType e)
  if (sides? body).isNone then return none
  let some i ← (xs.zip bis).findIdxM? fun (x, bi) => do
      return bi.isExplicit && (← isProp (← inferType x)) | return none
  unless ← withReducible (isDefEq (← inferType xs[i]!) (← inferType h)) do return none
  xs[i]!.mvarId!.assign h
  for x in xs, bi in bis do
    if bi.isInstImplicit && !(← x.mvarId!.isAssigned) then
      let some inst ← synthInstance? (← inferType x) | return none
      x.mvarId!.assign inst
  let proof ← instantiateMVars (mkAppN e xs)
  if proof.hasMVar then return none
  return some proof

/-- The hypotheses of `goal` introduced by the pointwise step, that is, not among `outer`. -/
def ownHyps (outer : FVarIdSet) (goal : MVarId) : MetaM (Array FVarId) :=
  return (← goal.getNondepPropHyps).filter (!outer.contains ·)

/-- The statements registered with `@[dominated_forward]`, by their first explicit premise. -/
def premiseTree : MetaM (DiscrTree Lean.Expr) := do
  let mut tree : DiscrTree Lean.Expr := {}
  for name in dominatedForwardAttr.getState (← getEnv) do
    let e ← mkConstWithFreshMVarLevels name
    let (xs, bis, _) ← forallMetaTelescopeReducing (← inferType e)
    let some i ← (xs.zip bis).findIdxM? fun (x, bi) => do
        return bi.isExplicit && (← isProp (← inferType x)) | continue
    tree ← tree.insert (← inferType xs[i]!) e
  return tree

/-- The given statements and those registered with `@[dominated]`, by the term each is about. -/
def factTree (lemmas : Array Lean.Expr) : MetaM (DiscrTree Lean.Expr) := do
  let mut tree : DiscrTree Lean.Expr := {}
  for e in lemmas ++ (← (dominatedAttr.getState (← getEnv)).mapM (mkConstWithFreshMVarLevels ·)) do
    let (_, _, body) ← forallMetaTelescopeReducing (← inferType e)
    if let some (k, _) := key? body then tree ← tree.insert k e
  return tree

/-- Facts about the positive powers occurring in the goal or in the hypotheses introduced by the
pointwise step, and the instances of the statements of `tree` at matching terms there. The terms
of the instances take part in the next round, for a few rounds. -/
def addSizeFacts (outer : FVarIdSet) (tree premises : DiscrTree Lean.Expr) (goal : MVarId) :
    MetaM MVarId :=
  goal.withContext do
  -- The facts about one term by its shape, and the instances of the statements matching it.
  let about (e : Lean.Expr) : MetaM (Array Lean.Expr × Array (Lean.Expr × Lean.Expr)) := do
    let mut facts := #[]
    if e.isAppOfArity ``HPow.hPow 6 then
      if let some k := e.appArg!.nat? then
        if k > 0 then
          let hk ← mkDecideProof (← mkAppM ``Ne #[mkNatLit k, mkNatLit 0])
          let base := e.getAppArgs[4]!
          if let some h ← observing? (mkAppOptM ``Nat.le_self_pow #[mkNatLit k, hk, base]) then
            facts := facts.push h
    let mut instances := #[]
    for l in ← tree.getMatch e do
      if let some h ← instanceAt l e then instances := instances.push h
    return (facts, instances)
  let subterms (e : Lean.Expr) : MetaM (Array Lean.Expr) := do
    let (_, ts) ← (e.forEach' fun e => do
        if e.isApp && !e.hasLooseBVars then modify (·.push e)
        return true : StateT (Array Lean.Expr) MetaM Unit).run #[]
    return ts
  let mut pending ← subterms (← instantiateMVars (← goal.getType))
  for fvarId in ← ownHyps outer goal do
    pending := pending ++ (← subterms (← instantiateMVars (← fvarId.getType)))
  let mut facts : Array Lean.Expr := #[]
  let mut seen : Std.HashSet Lean.Expr := {}
  for _ in [0:3] do
    let mut next := #[]
    for e in pending do
      if seen.contains e then continue
      seen := seen.insert e
      let (shaped, instances) ← about e
      facts := facts ++ shaped ++ instances.map (·.1)
      for (_, other) in instances do next := next ++ (← subterms other)
    pending := next
  -- Statements registered with `@[dominated_forward]`, at each hypothesis matching their premise.
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    for e in ← premises.getMatch decl.type do
      if let some h ← instanceOf e decl.toExpr then facts := facts.push h
  let mut goal := goal
  for h in facts do
    let (_, g) ← (← goal.assert `size_fact (← inferType h) h).intro1P
    goal := g
  return goal

/-- A natural-number expression as a linear form: its constant and the coefficients of its atoms,
the maximal subterms other than sums, multiples by a literal and literals. -/
partial def linearForm (e : Lean.Expr) : Nat × Array (Lean.Expr × Nat) :=
  if let some n := e.nat? then (n, #[])
  else if e.isAppOfArity ``HAdd.hAdd 6 then
    let (c, xs) := linearForm e.getAppArgs[4]!
    let (d, ys) := linearForm e.appArg!
    (c + d, ys.foldl (init := xs) fun acc (t, n) =>
      match acc.findIdx? (·.1 == t) with
      | some i => acc.modify i fun (t, m) => (t, m + n)
      | none => acc.push (t, n))
  else if e.isAppOfArity ``HMul.hMul 6 then
    let scale (k : Nat) (x : Nat × Array (Lean.Expr × Nat)) :=
      if k == 0 then (0, #[]) else (k * x.1, x.2.map fun (t, n) => (t, k * n))
    match e.getAppArgs[4]!.nat?, e.appArg!.nat? with
    | some k, _ => scale k (linearForm e.appArg!)
    | _, some k => scale k (linearForm e.getAppArgs[4]!)
    | none, none => (0, #[(e, 1)])
  else (0, #[(e, 1)])

/-- The least `k ≥ 1` with `a ≤ k * c` term by term for a positive `c`: every atom of `a` is an
atom of `c`, and the constant of `a` is covered by that of `c`, or by `c` itself. -/
def termwiseCoefficient (a c : Lean.Expr) : Option Nat := Id.run do
  let (a₀, as) := linearForm a
  let (c₀, cs) := linearForm c
  let mut k := 1
  for (x, n) in as do
    let some (_, m) := cs.find? (·.1 == x) | return none
    k := max k ((n + m - 1) / m)
  if 0 < a₀ then
    k := if 0 < c₀ then max k ((a₀ + c₀ - 1) / c₀) else k + a₀
  return some k

/-- The atoms of the linear forms of the sides of a comparison `a ≤ b` or `a < b`. -/
def comparisonAtoms (e : Lean.Expr) : Array Lean.Expr :=
  ((linearForm e.appFn!.appArg!).2 ++ (linearForm e.appArg!).2).map (·.1)

/-- Prove the linear statement `p` from the linear `premises`, given with their proofs, by `omega`
with the atoms abstracted, so that no other hypothesis is read. -/
def omegaAbstracted (p : Lean.Expr) (premises : Array (Lean.Expr × Lean.Expr) := #[]) :
    TacticM (Option Lean.Expr) := do
  let atoms := (#[p] ++ premises.map (·.1)).foldl (init := #[]) fun acc e =>
    (comparisonAtoms e).foldl (init := acc) fun acc t => if acc.contains t then acc else acc.push t
  let stmt ← withLocalDeclsDND (atoms.map fun _ => (`x, mkConst ``Nat)) fun xs => do
    let abstract (e : Lean.Expr) := e.replace fun t => (atoms.idxOf? t).map (xs[·]!)
    mkForallFVars xs (← premises.foldrM (init := abstract p) fun (q, _) body =>
      mkArrow (abstract q) body)
  let saved ← saveState
  let goals ← getGoals
  try
    let proof ← withLCtx {} {} do
      let m ← mkFreshExprSyntheticOpaqueMVar stmt
      let (_, g) ← m.mvarId!.introN (atoms.size + premises.size)
      setGoals [g]
      Omega.omegaDefault
      instantiateMVars m
    setGoals goals
    return some (mkAppN (mkAppN proof atoms) (premises.map (·.2)))
  catch _ =>
    saved.restore
    return none

/-- The comparisons `a ≤ b`, `a < b` and `a = b` of a conjunction, by their sides, with whether
each is an equation. -/
partial def comparisonSides (e : Lean.Expr) : Array (Lean.Expr × Lean.Expr × Bool) :=
  if e.isAppOfArity ``And 2 then comparisonSides e.appFn!.appArg! ++ comparisonSides e.appArg!
  else if e.isAppOfArity ``LE.le 4 || e.isAppOfArity ``LT.lt 4 then
    #[(e.appFn!.appArg!, e.appArg!, false)]
  else if e.isAppOfArity ``Eq 3 then #[(e.appFn!.appArg!, e.appArg!, true)]
  else #[]

/-- Bounds for the powers and products that the left side of the goal depends on, against the
powers of its right side: for a power `a ^ d` and a power `b ^ e` with `d ≤ e`, add
`a ^ d ≤ k ^ d * b ^ e` whenever `a` is `b` or `a ≤ k * b`, and `0 < b`; for a product `a * b` and a
power `c ^ e` with `2 ≤ e`, add `a * b ≤ k * l * c ^ e` whenever `a ≤ k * c`, `0 < c`, and
`b ≤ l * c` or `b ≤ l * c ^ d` for a power `c ^ d` of either side with `d < e`. The left side
depends on its variables and terms and, transitively, on the bounds of hypotheses `t ≤ u`, `t < u`
or `t = u` about them, also within conjunctions. A comparison of linear forms whose coefficients
show it is proved by `omega` without the other hypotheses, with the least such coefficient;
otherwise `omega` with the hypotheses tries the coefficients 1, 2, 4 and 8. A goal that is not a
conjunction of comparisons compares all its powers and products. Since degree synthesis, these facts
serve only the summands with a `match` on a pattern (`viaPowerFacts`), provisionally (plan W2). -/
def addPowerFacts (goal : MVarId) : TacticM MVarId := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let isNat (e : Lean.Expr) : TacticM Bool := do isDefEq (← inferType e) (mkConst ``Nat)
  -- The variables and applications in `e`.
  let terms (e : Lean.Expr) : TacticM (Array Lean.Expr) := do
    let (_, ts) ← (e.forEach' fun e => do
        if e.isFVar || e.isApp && !e.hasLooseBVars then modify (·.push e)
        return true : StateT (Array Lean.Expr) MetaM Unit).run #[]
    return ts
  let power? (e : Lean.Expr) : TacticM (Option (Lean.Expr × Nat)) := do
    unless e.isAppOfArity ``HPow.hPow 6 do return none
    let some k := e.appArg!.nat? | return none
    unless k > 0 && (← isNat e) do return none
    return some (e.getAppArgs[4]!, k)
  let product? (e : Lean.Expr) : TacticM (Option (Lean.Expr × Lean.Expr)) := do
    unless e.isAppOfArity ``HMul.hMul 6 do return none
    let (a, b) := (e.getAppArgs[4]!, e.appArg!)
    unless a.nat?.isNone && b.nat?.isNone && (← isNat e) do return none
    return some (a, b)
  let sides := (comparisonSides target).filterMap fun (a, b, eq) => if eq then none else some (a, b)
  let rightSideTerms ← sides.flatMapM fun (_, b) => terms b
  -- Every fact bounds a term by a power of the right side.
  if !sides.isEmpty && (← rightSideTerms.filterMapM power?).isEmpty then return goal
  let mut hyps := #[]
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do hyps := hyps.push (← instantiateMVars decl.type)
  -- The terms the left side depends on, and those of the right side.
  let (leftTerms, rightTerms) ← if sides.isEmpty then
      let all ← (#[target] ++ hyps).flatMapM terms
      pure (all, all)
    else do
      let mut left : Std.HashSet Lean.Expr := {}
      for (a, _) in sides do
        for t in ← terms a do left := left.insert t
      let mut bounds := #[]
      for h in hyps do
        for (t, u, eq) in comparisonSides h do bounds := bounds.push (← terms t, ← terms u, eq)
      for _ in [0:3] do
        for (t, u, eq) in bounds do
          if t.any left.contains then
            for v in u do left := left.insert v
          if eq && u.any left.contains then
            for v in t do left := left.insert v
      pure (left.toArray, rightSideTerms)
  let rightPowers := (← rightTerms.filterMapM power?).toList.eraseDups
  let leftPowers := (← leftTerms.filterMapM power?).toList.eraseDups
  let products := (← leftTerms.filterMapM product?).toList.eraseDups
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
  -- `a ≤ k * c` given `hc : 0 < c`, written `a ≤ c` for `k = 1` when `plain`: with `k` read off
  -- the linear forms, or the least of 1, 2, 4, 8 for which `omega` proves it from the hypotheses.
  let bound (a c hc : Lean.Expr) (plain : Bool) : TacticM (Option (Nat × Lean.Expr)) := do
    let times (k : Nat) := if plain && k == 1 then pure c else mkAppM ``HMul.hMul #[mkNatLit k, c]
    if let some k := termwiseCoefficient a c then
      if let some h ← omegaAbstracted (← mkAppM ``LE.le #[a, ← times k])
          #[(← mkAppM ``LT.lt #[mkNatLit 0, c], hc)] then
        return some (k, h)
    for k in [1, 2, 4, 8] do
      if let some h ← byOmega (← mkAppM ``LE.le #[a, ← times k]) then return some (k, h)
    return none
  -- `0 < a` when the constant of `a`, or of the base of the power `a`, is positive; otherwise by
  -- `omega` with the hypotheses.
  let positiveConstant (a : Lean.Expr) : TacticM (Option Lean.Expr) := do
    unless 0 < (linearForm a).1 do return none
    omegaAbstracted (← mkAppM ``LT.lt #[mkNatLit 0, a])
  let pos (a : Lean.Expr) : TacticM (Option Lean.Expr) := do
    if let some h ← positiveConstant a then return some h
    if let some (b, d) ← power? a then
      if let some h ← positiveConstant b then
        return some (← mkAppOptM ``Nat.pow_pos #[none, mkNatLit d, h])
    byOmega (← mkAppM ``LT.lt #[mkNatLit 0, a])
  let powLe (hb : Lean.Expr) (d e : Nat) : TacticM Lean.Expr := do
    mkAppM ``Nat.pow_le_pow_right
      #[hb, ← mkDecideProof (← mkAppM ``LE.le #[mkNatLit d, mkNatLit e])]
  let mut facts := #[]
  for (a, d) in leftPowers do
    for (b, e) in rightPowers do
      if d > e || (a == b && d == e) then continue
      let some hb ← pos b | continue
      if a == b then
        facts := facts.push (← powLe hb d e)
        continue
      let some (k, hab) ← bound a b hb true | continue
      if k == 1 then
        facts := facts.push (← mkAppM ``le_trans
          #[← mkAppM ``Nat.pow_le_pow_left #[hab, mkNatLit d], ← powLe hb d e])
        continue
      -- A coefficient `k` on the base becomes the literal `k ^ d` on the power.
      let scaled ← mkAppM ``le_trans #[← mkAppM ``Nat.pow_le_pow_left #[hab, mkNatLit d],
        ← mkAppM ``Eq.le #[← mkAppM ``Nat.mul_pow #[mkNatLit k, b, mkNatLit d]]]
      let h ← mkAppM ``le_trans #[scaled, ← mkAppM ``Nat.mul_le_mul_left
        #[← mkAppM ``HPow.hPow #[mkNatLit k, mkNatLit d], ← powLe hb d e]]
      let type ← mkAppM ``LE.le #[← mkAppM ``HPow.hPow #[a, mkNatLit d],
        ← mkAppM ``HMul.hMul #[mkNatLit (k ^ d), ← mkAppM ``HPow.hPow #[b, mkNatLit e]]]
      facts := facts.push (← mkExpectedTypeHint h type)
  for (a, b) in products do
    for (c, e) in rightPowers do
      if e < 2 then continue
      let some hc ← pos c | continue
      let some (_, hac) ← bound a c hc false | continue
      if let some (_, hbc) ← bound b c hc false then
        let he ← mkDecideProof (← mkAppM ``LE.le #[mkNatLit 2, mkNatLit e])
        facts := facts.push (← mkAppM ``mul_le_mul_pow_of_le_mul #[hac, hbc, he, hc])
        continue
      -- A factor `x ^ d` with `x ≤ k * c` is within `k ^ d * c ^ d`.
      if b.isAppOfArity ``HPow.hPow 6 then
        if let some d := b.appArg!.nat? then
          if 1 < d && d < e then
            if let some (_, hx) ← bound b.getAppArgs[4]! c hc false then
              let hp ← mkAppM ``Nat.pow_le_pow_left #[hx, mkNatLit d]
              let hbc ← mkAppM ``le_of_le_of_eq #[hp, ← mkAppM ``Nat.mul_pow
                #[(← inferType hx).appArg!.appFn!.appArg!, c, mkNatLit d]]
              let he ← mkDecideProof (← mkAppM ``LE.le #[mkNatLit (d + 1), mkNatLit e])
              facts := facts.push (← mkAppM ``mul_le_mul_pow_of_le_mul_pow #[hac, hbc, he, hc])
              continue
      -- `b` depends on its bounds `c ^ d`, which are among the powers of the left side.
      for (c', d) in (leftPowers ++ rightPowers).eraseDups do
        unless c' == c && 1 < d && d < e do continue
        let cd ← mkAppM ``HPow.hPow #[c, mkNatLit d]
        let some (_, hbc) ← bound b cd (← mkAppOptM ``Nat.pow_pos #[none, mkNatLit d, hc]) false
          | continue
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

/-- The declarations registered with a simp attribute, with their direction. -/
def attrDecls (attr : Name) : MetaM (Array (Name × Bool)) := do
  let some ext ← getSimpExtension? attr | throwError "unknown simp attribute `{attr}`"
  return (← ext.getTheorems).lemmaNames.fold (init := #[]) fun acc o => match o with
    | .decl n _ inv => acc.push (n, inv)
    | _ => acc

/-- A simp context with the given lemmas, those of the given simp attributes, and definitions to
unfold only. -/
def simpContext (names : Array Name) (unfolds : Array Name := #[]) (attrs : Array Name := #[]) :
    MetaM Simp.Context := do
  let mut thms : SimpTheorems := {}
  for name in names do thms ← thms.addConst name
  for name in unfolds do thms ← thms.addDeclToUnfold name
  -- Registered statements about encodings, such as `@[dominated_simp]`, in the same index.
  for attr in attrs do
    for (name, inv) in ← attrDecls attr do thms ← thms.addConst name (inv := inv)
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

/-- Use the equations left by splitting a `match`: an equation between constructor applications,
or of a variable to one, is substituted, and the goal is closed when `cases` on an equation
leaves no cases, as for a branch that contradicts the test selecting it. A heterogeneous equation
between variables, left by generalizing a dependent discriminant, is substituted. -/
partial def casesEquations (outer : FVarIdSet) (goal : MVarId) : MetaM (Array MVarId) :=
  goal.withContext do
  for decl in ← getLCtx do
    let type ← instantiateMVars decl.type
    if decl.isImplementationDetail || outer.contains decl.fvarId then continue
    if type.isAppOfArity ``HEq 4 && type.appFn!.appFn!.appArg!.isFVar && type.appArg!.isFVar then
      let saved ← saveState
      try
        if let #[g] ← goal.cases decl.fvarId then return ← casesEquations outer g.mvarId
      catch _ => pure ()
      saved.restore
    unless type.isAppOfArity ``Eq 3 do continue
    let constructor (e : Lean.Expr) : MetaM Bool := do
      let some name := (← whnfR e).getAppFn.constName? | return false
      return (← getEnv).find? name |>.any (·.isCtor)
    -- A variable equal to a constructor, as a `match h : x with` leaves, is substituted too.
    let injective := (← constructor type.appArg!) &&
      (type.appFn!.appArg!.isFVar || (← constructor type.appFn!.appArg!))
    let saved ← saveState
    try
      let goals ← goal.cases decl.fvarId
      if goals.isEmpty then return #[]
      if let #[g] := goals then
        if injective then return ← casesEquations outer g.mvarId
    catch _ => pure ()
    saved.restore
  return #[goal]

/-- The patterns of each alternative of a matcher, as functions of the alternative's parameters,
read from the matcher's type with an opaque motive. -/
def alternativePatterns (app : MatcherApp) : MetaM (Array (Array Lean.Expr)) := do
  let matcher := mkAppN (mkConst app.matcherName app.matcherLevels.toList) app.params
  withLocalDeclD `motive (← inferType app.motive) fun motive => do
    let types ← inferArgumentTypesN app.alts.size (mkAppN (mkApp matcher motive) app.discrs)
    (types.zip app.altNumParams).mapM fun (type, n) =>
      forallBoundedTelescope type n fun xs body =>
        body.consumeMData.getAppArgs.mapM (mkLambdaFVars xs ·)

/-- The variables of a discriminant at which a pattern has a constructor. -/
partial def inspectedVariables (discr pattern : Lean.Expr) : MetaM (Array Lean.Expr) := do
  let pattern ← whnfR pattern
  let .const ctor _ := pattern.getAppFn | return #[]
  unless (← getEnv).find? ctor |>.any (·.isCtor) do return #[]
  let discr ← whnfR discr
  if discr.isFVar then return #[discr]
  unless discr.getAppFn.isConstOf ctor do return #[]
  (discr.getAppArgs.zip pattern.getAppArgs).foldlM (init := #[]) fun vars (d, p) => do
    return vars ++ (← inspectedVariables d p)

/-- Split the first `casesOn` or `rec` application on a local variable in the goal, or a variable
that a `match` inspects. -/
def casesOnVariable (goal : MVarId) : MetaM (Option (Array MVarId)) := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let collect (e : Lean.Expr) : StateT (Array (Name × Lean.Expr)) MetaM Bool := do
    if let .const name _ := e.getAppFn then
      if name.isStr && (name.getString! == "casesOn" || name.getString! == "rec") then
        for a in e.getAppArgs do
          if a.isFVar then modify (·.push (name.getPrefix, a))
      -- A `match` that `split` cannot eliminate, as on an indexed family: split the variables
      -- its patterns inspect.
      -- (Not under a binder, as `split` does, since the discriminants are inspected.)
      else if !e.hasLooseBVars then
        if let some app ← matchMatcherApp? e then
          for patterns in ← alternativePatterns app do
            let some first := patterns[0]? | continue
            let (params, _, _) ← lambdaMetaTelescope first
            for discr in app.discrs, pattern in patterns do
              for a in ← inspectedVariables discr (pattern.beta params) do
                if let .const family _ := (← whnfR (← inferType a)).getAppFn then
                  modify (·.push (family, a))
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

end Complexity.Tactic.Dominated
