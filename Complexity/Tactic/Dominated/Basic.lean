/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Asymptotics.Nat
public import Complexity.Tactic.Dominated.Facts
public meta import Lean.Elab.Tactic.Omega.Frontend

/-! # Closing growth comparisons

`dominated` proves `Dominated f g` when both sides are given, as left by `source_fun_prop` and
`model_fun_prop`, whose default discharger it is. It never changes either side, and leaves the
summands it cannot prove as goals. Every comparison is settled once per call.

## Splitting

The left side is normalized with `@[dominated_simp]`, and its sums and maxima are split. A
difference is compared as stated when it is the target or a fact, and through its minuend
otherwise. Each summand is tried in turn through a `Dominated` hypothesis, a genuine property of
the source function matched reducibly; entry by entry for maxima over lists and sums over tables;
by the pointwise step; and, against a power of degree at least 2 on the right, for its products and
powers.

## The pointwise step

The pointwise step destructures the input, splits the source cases, expands encoded sizes with
`@[dominated_expand]` and the definitions of the list, adds size facts and closes each case with
`omega`; the coefficient is the hidden witness `2 ^ 40`. The size facts are the statements
`a ≤ b`, `a < b` or `a = b` of the list and those registered with `@[dominated]`, instantiated at
the terms they are about (their left side, or their right side when the left side is a variable or
a literal), the terms of their other side being looked at in the next round, and the statements
registered with `@[dominated_forward]`, instantiated at matching hypotheses. Like `omega`, it reads
the other hypotheses without changing them. Products and powers are atoms there.

## Products and powers

A summand that the pointwise step cannot prove is proved by degree synthesis against a base `S`
taken from the powers of the right side: every subterm `t` of the left side gets a degree `d` with
`Dominated (fun x => t) (fun x => S x ^ d)`, sums and maxima taking the larger degree, products
adding and powers multiplying the degrees, and `Dominated (fun x => S x ^ e) g` closes it when
`d ≤ e`. The constants stay hidden in `Dominated`, so nested products and powers need no
coefficient, and `Dominated` hypotheses give degrees of any size. An atom has degree 1 when it is
linearly within a multiple of `S`, and otherwise the degree of an upper bound of it.

Splitting sums and maxima loses nothing, but splitting a product, a power or a difference loses what
is known about it as a whole, such as `x * y ≤ z` or `x ^ 2 ≤ y`. So when the rules alone fail, a
second pass also bounds products, powers and differences as atoms are, and keeps the lower degree.
An `if` whose condition depends only on the input is split losslessly by cases on the condition,
which each part has as the property of its subtype input. A `match` on a pattern binds variables
that degree synthesis cannot see: such a summand is still compared pointwise, with facts about the
products and powers it depends on (`addPowerFacts`), a provisional treatment (plan W2). See
`degree`, `viaDegree` and `viaCases`.
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

/-! ### The solver

`dominated` follows the structure of `positivity` and `fun_prop`: a recursive function builds
proof terms, with the facts of the call in a reader context and the settled comparisons in a
cache. The pointwise step `sizeOmega` plays the part of a discharger. -/

/-- The facts and the list of one `dominated` call. -/
structure Context where
  /-- Statements `a ≤ b`, `a < b` or `a = b` to instantiate at matching terms in the pointwise
  step, by the term each is about: those given and those registered with `@[dominated]`. -/
  statements : DiscrTree Lean.Expr
  /-- Statements registered with `@[dominated_forward]`, by their premise. -/
  premises : DiscrTree Lean.Expr
  /-- `Dominated` facts with their types, compositions unfolded. -/
  facts : Array (Lean.Expr × Lean.Expr)
  /-- Expansion of encoded sizes on the left side. -/
  sizes : Simp.Context
  /-- The same, also distributing the table length over an entry. -/
  sizesMul : Simp.Context
  /-- Expansion of encoded sizes in the pointwise step, unfolding the definitions of the list. -/
  expand : Simp.Context
  /-- The normalization of `sizes`, also unfolding the definitions of the list: degree synthesis
  reads atoms and the right side with it, without rewriting the goals left to the user. -/
  sizesUnfold : Simp.Context
  /-- Numeral arithmetic used with `expand`, so that exponents such as `2 * 3` become literals. -/
  numerals : Simp.SimprocsArray

/-- Comparisons settled during one call, and the summands left to the user. -/
structure State where
  /-- Settled `Dominated` goals and positivity propositions: a proof, or `none` for a failure. -/
  cache : Std.HashMap Lean.Expr (Option Lean.Expr) := {}
  /-- Summands left as goals, by type. -/
  left : Array (Lean.Expr × MVarId) := #[]
  /-- Whether the pointwise step adds the facts about products and powers, as for a `match` on a
  pattern (`viaPowerFacts`). -/
  nonlinear : Bool := false

/-- The solver monad: one context and one cache per `dominated` call. -/
abbrev DominatedM := ReaderT Context (StateRefT State TacticM)

/-- Unfold the type abbreviations in `e`, such as `CNF ℕ` to `List (CNF.Clause ℕ)`. -/
partial def unfoldTypeAbbrevs (env : Environment) (e : Lean.Expr) : Lean.Expr :=
  e.replace fun t => do
    let .const c us := t.getAppFn | none
    let some (.defnInfo info) := env.find? c | none
    unless getReducibilityStatusCore env c matches .reducible do none
    unless info.type.getForallBody.isSort do none
    some (unfoldTypeAbbrevs env ((info.value.instantiateLevelParams info.levelParams us).beta
      t.getAppArgs))

/-- Settle `p` once per call, up to type abbreviations: a lemma about an underlying type, such as
one about `List α` used at `CNF ℕ`, reaches the same comparisons. A proof that still has
metavariables is not kept, since a later backtracking step could unassign them. -/
def memo (p : Lean.Expr) (k : DominatedM (Option Lean.Expr)) : DominatedM (Option Lean.Expr) := do
  let p ← instantiateMVars p
  let key := unfoldTypeAbbrevs (← getEnv) p
  -- The proof is stated at `p`, so assembling proofs never rechecks definitional equality.
  if let some r := (← get).cache[key]? then
    -- A failure settled without the facts about products and powers is tried again with them.
    if r.isSome || !(← get).nonlinear then return ← r.mapM (mkExpectedTypeHint · p)
  let r ← match ← k with
    | some proof => pure (some (← mkExpectedTypeHint (← instantiateMVars proof) p))
    | none => pure none
  unless r.any (·.hasMVar) do modify fun s => { s with cache := s.cache.insert key r }
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

/-- `e` without metadata. -/
partial def eraseMData (e : Lean.Expr) : Lean.Expr :=
  e.replace fun | .mdata _ b => some (eraseMData b) | _ => none

/-- Close one case of the pointwise step by `omega` with the size facts, and the facts about
products and powers when `nonlinear`, expanding the encoded sizes that splitting has exposed. -/
def closeCase (outer : FVarIdSet) (goal : MVarId) : DominatedM Bool := do
  let nonlinear := (← get).nonlinear
  let ctx ← read
  -- `omega` takes a term under metadata, as the alternatives of a `match` carry, for an atom.
  let goal ← goal.replaceTargetDefEq (eraseMData (← instantiateMVars (← goal.getType)))
  closes goal do
    let some g ← simpOwn outer ctx.expand
        (← addSizeFacts outer ctx.statements ctx.premises goal) ctx.numerals
      | setGoals []
    setGoals [← if nonlinear then addPowerFacts g else pure g]
    Omega.omegaDefault

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

/-- The structures whose projections occur in `es`. Degree synthesis reads the size of such a
structure as the size of its fields, and of no other structure. -/
def projectedIn (es : Array Lean.Expr) : MetaM (Std.HashSet Lean.Expr) := do
  let env ← getEnv
  let (_, s) ← (es.forM fun e => e.forEach' fun t => do
      if let .proj _ _ b := t then modify (·.insert b)
      if let some n := t.getAppFn.constName? then
        if let some info := env.getProjectionFnInfo? n then
          if t.getAppNumArgs == info.numParams + 1 then modify (·.insert t.appArg!)
      return true : StateT (Std.HashSet Lean.Expr) MetaM Unit).run {}
  return s

/-- `⌜y⌝ₜ.size` with `y` replaced by its constructor applied to its projections, when `y`
has a structure type and is not a constructor application. Equal by structure eta. -/
def etaSize? (t : Lean.Expr) : MetaM (Option Lean.Expr) := do
  unless t.isAppOfArity ``Tree.size 1 do return none
  let e := t.appArg!
  unless e.isAppOfArity ``UniqueEncoding.encode 4 do return none
  let y := e.appArg!
  let ty ← whnfR (← inferType y)
  let .const name us := ty.getAppFn | return none
  let env ← getEnv
  let some info := getStructureInfo? env name | return none
  let ctor := getStructureCtor env name
  if (← whnfR y).getAppFn.isConstOf ctor.name then return none
  let projs ← info.fieldNames.mapM fun f => mkProjection y f
  let y' := mkAppN (mkConst ctor.name us) (ty.getAppArgs ++ projs)
  return some (mkApp t.appFn! (mkApp e.appFn! y'))

/-- `Dominated (fun x => t) (fun x => S x ^ d)` for a degree `d` read off the structure of `t`, with
`x` standing for the input and `hS` the positivity of `S`. Literals have degree 0; sums and maxima
take the larger degree of their parts, products add and powers multiply them (the exponent is
evaluated), and a difference takes the degree of its minuend. Any other term is an atom, bounded as
a whole by `bound`:
* with degree 1 when it is within a multiple of `S`: read off when it is an atom of the linear form
  of `S`, and otherwise by the pointwise step, run in `outer`, the context without `x`, so that its
  auxiliary proofs do not capture `x`;
* otherwise with the degree of an upper bound: a `Dominated` hypothesis about it, or `t ≤ u` from
  a comparison whose left side has `t` in its linear form, `u` not containing `t`, among the
  conjuncts of the property of a subtype input and the statements instantiated at `t`;
* an atom also through the definitions of the list, and the size of a structure in `projected`
  through the sizes of its fields.

Splitting a product, a power or a difference loses what is known about it as a whole, such as
`x * y ≤ z` or `x ^ 2 ≤ y`. In the `thorough` pass these are also bounded as atoms are, first, and
the lower degree is kept; degree 1 is the least for a term with an atom, so the parts are then not
read. That pass also tries every upper bound instead of the first one. The degree found is not
always the least: degrees are integers, and one base is used throughout. -/
partial def degree (outer : LocalContext × LocalInstances) (projected : Std.HashSet Lean.Expr)
    (thorough : Bool) (x S hS t : Lean.Expr) :
    DominatedM (Option (Nat × Lean.Expr)) := do
  -- Pointwise comparisons run without `x` in scope, so their auxiliary proofs do not capture it.
  let outside {β : Type} (k : DominatedM β) : DominatedM β := withLCtx outer.1 outer.2 k
  let Sx := (mkApp S x).headBeta
  let fn (e : Lean.Expr) : MetaM Lean.Expr := mkLambdaFVars #[x] e
  let powFn (d : Nat) : MetaM Lean.Expr := do fn (← mkAppM ``HPow.hPow #[Sx, mkNatLit d])
  let lift (p : Lean.Expr) (d e : Nat) : MetaM Lean.Expr := do
    if d == e then return p
    mkAppM ``Dominated.mono_pow
      #[p, ← mkDecideProof (← mkAppM ``LE.le #[mkNatLit d, mkNatLit e]), hS]
  let hinted (p : Lean.Expr) (t : Lean.Expr) (d : Nat) : MetaM Lean.Expr := do
    mkExpectedTypeHint p (← mkAppM ``Dominated #[← fn t, ← powFn d])
  let lower (a b : Option (Nat × Lean.Expr)) : Option (Nat × Lean.Expr) :=
    match a, b with
    | some (d, p), some (e, q) => if e < d then some (e, q) else some (d, p)
    | some r, none => some r
    | none, r => r
  let sub := degree outer projected thorough x S hS
  if t.nat?.isSome then
    let hpos ← fn (← mkAppOptM ``Nat.pow_pos #[none, mkNatLit 0, mkApp hS x])
    return some (0, ← mkAppM ``Dominated.const_of_pos #[t, hpos])
  let two (a b : Lean.Expr) := do
    let some (da, pa) ← sub a | return none
    let some (db, pb) ← sub b | return none
    return some (da, pa, db, pb)
  if t.isAppOfArity ``HAdd.hAdd 6 || t.isAppOfArity ``Max.max 4 then
    let (a, b) := if t.isAppOfArity ``HAdd.hAdd 6 then (t.getAppArgs[4]!, t.appArg!)
      else (t.appFn!.appArg!, t.appArg!)
    let some (da, pa, db, pb) ← two a b | return none
    let d := max da db
    let rule := if t.isAppOfArity ``HAdd.hAdd 6 then ``Dominated.add_same else ``Dominated.max_same
    return some (d, ← hinted (← mkAppM rule #[← lift pa da d, ← lift pb db d]) t d)
  -- `t ≤ u` from a comparison whose left side has `t` in its linear form.
  let upper (h : Lean.Expr) : DominatedM (Option (Lean.Expr × Lean.Expr)) := do
    let ty ← whnfR (← instantiateMVars (← inferType h))
    unless ty.getAppNumArgs > 0 && ty.getAppArgs[0]!.isConstOf ``Nat do return none
    let le ← if ty.isAppOfArity ``LE.le 4 then pure h
      else if ty.isAppOfArity ``LT.lt 4 then mkAppM ``Nat.le_of_lt #[h]
      else if ty.isAppOfArity ``Eq 3 then mkAppM ``Nat.le_of_eq #[h]
      else return none
    let leTy ← whnfR (← inferType le)
    let (l, u) := (leTy.appFn!.appArg!, leTy.appArg!)
    if (u.find? (· == t)).isSome then return none
    if ← withReducible (isDefEq l t) then return some (u, le)
    unless (linearForm l).2.any (·.1 == t) do return none
    let some h' ← omegaAbstracted (← mkAppM ``LE.le #[t, u]) #[(leTy, le)] | return none
    return some (u, h')
  -- The comparisons about `t`: the conjuncts of the property of a subtype input, and the given
  -- and registered statements instantiated at `t`.
  let comparisons : DominatedM (Array Lean.Expr) := do
    let mut out := #[]
    let ty ← whnfR (← inferType x)
    if ty.isAppOfArity ``Subtype 2 then
      let rec conjuncts (h : Lean.Expr) (p : Lean.Expr) (fuel : Nat) : MetaM (Array Lean.Expr) := do
        if fuel == 0 then return #[]
        let p ← whnfR p
        if p.isAppOfArity ``And 2 then
          return (← conjuncts (← mkAppM ``And.left #[h]) p.appFn!.appArg! (fuel - 1)) ++
            (← conjuncts (← mkAppM ``And.right #[h]) p.appArg! (fuel - 1))
        return #[h]
      let hx ← mkAppM ``Subtype.property #[x]
      out := out ++ (← conjuncts hx (← inferType hx) 4)
    for l in ← (← read).statements.getMatch t do
      let some (h, _) ← instanceAt l t | continue
      out := out.push h
    return out
  -- `t` bounded as a whole: degree 1 by a linear comparison, or the degree of an upper bound.
  let bound (atomic : Bool) : DominatedM (Option (Nat × Lean.Expr)) := do
    let atom ← fn t
    -- An atom of the base's linear form has degree 1, read off without the pointwise step.
    if let some k := termwiseCoefficient t Sx then
      if let some h ← omegaAbstracted
          (← mkAppM ``LE.le #[t, ← mkAppM ``HMul.hMul #[mkNatLit k, Sx]])
          #[(← mkAppM ``LT.lt #[mkNatLit 0, Sx], mkApp hS x)] then
        let p ← mkAppM ``Dominated.of_le_mul #[mkNatLit k, ← fn h]
        return some (1, ← hinted (← mkAppM ``Dominated.le_pow #[p, ← mkDecideProof
          (← mkAppM ``LT.lt #[mkNatLit 0, mkNatLit 1])]) t 1)
    -- Otherwise degree 1 by a pointwise linear comparison.
    if let some p ← outside (memo (← mkAppM ``Dominated #[atom, S]) (attempt (proveBase atom S)))
    then
      return some (1, ← hinted (← mkAppM ``Dominated.le_pow #[p, ← mkDecideProof
        (← mkAppM ``LT.lt #[mkNatLit 0, mkNatLit 1])]) t 1)
    let mut best : Option (Nat × Lean.Expr) := none
    -- A `Dominated` hypothesis about the term, of some degree.
    for (h, type) in (← read).facts do
      unless ← withReducible (isDefEq type.appFn!.appArg! atom) do continue
      let some (d, po) ← sub (mkApp type.appArg! x).headBeta | continue
      best := lower best (some (d, ← hinted (← mkAppM ``Dominated.trans #[h, po]) t d))
      unless thorough do return best
    -- An upper bound from a comparison, of some degree.
    for h in ← comparisons do
      let some (u, le) ← upper h | continue
      let some (d, po) ← sub u | continue
      let p ← mkAppM ``Dominated.trans #[← mkAppM ``Dominated.of_le #[← fn le], po]
      best := lower best (some (d, ← hinted p t d))
      unless thorough do return best
    -- An atom read through the definitions of the list.
    if atomic then
      let (r, _) ← simp t (← read).sizesUnfold
      if r.expr != t then
        let eq ← r.getProof
        if let some (d, po) ← sub r.expr then
          let p ← mkAppM ``Dominated.trans
            #[← mkAppM ``Dominated.of_le #[← fn (← mkAppM ``Nat.le_of_eq #[eq])], po]
          best := lower best (some (d, ← hinted p t d))
    return best
  -- Products, powers and differences: by their rule, and in the thorough pass also as a whole.
  let composed? : Option (DominatedM (Option (Nat × Lean.Expr))) ←
    if t.isAppOfArity ``HMul.hMul 6 then
      pure (some do
        let some (da, pa, db, pb) ← two t.getAppArgs[4]! t.appArg! | pure none
        let p ← mkAppM ``Dominated.mul #[pa, pb]
        let h ← fn (← mkAppM ``Eq.ge #[← mkAppM ``Nat.pow_add #[Sx, mkNatLit da, mkNatLit db]])
        pure (some (da + db, ← hinted (← mkAppM ``Dominated.mono #[p, h]) t (da + db))))
    else if t.isAppOfArity ``HPow.hPow 6 then do
      match ← (evalNat t.appArg!).run with
      | some n => pure (some do
          let some (da, pa) ← sub t.getAppArgs[4]! | pure none
          let p ← mkAppM ``Dominated.pow #[pa, mkNatLit n]
          let h ← fn (← mkAppM ``Eq.ge #[← mkAppM ``Nat.pow_mul #[Sx, mkNatLit da, mkNatLit n]])
          pure (some (da * n, ← hinted (← mkAppM ``Dominated.mono #[p, h]) t (da * n))))
      | none => pure none
    else if t.isAppOfArity ``HSub.hSub 6 then
      pure (some do
        let some (da, pa) ← sub t.getAppArgs[4]! | pure none
        pure (some (da, ← hinted (← mkAppM ``Dominated.sub_left #[pa, ← fn t.appArg!]) t da)))
    else pure none
  if let some composed := composed? then
    unless thorough do return ← composed
    -- A whole bound of degree 1 is the least possible, so the parts need not be read.
    let whole ← bound false
    if whole.any (·.1 ≤ 1) then return whole
    return lower (← composed) whole
  -- The size of a structure whose projections occur: read through its projections.
  if let some t' ← etaSize? t then
    if projected.contains t.appArg!.appArg! then
      let (r, _) ← simp t' (← read).expand
      if r.expr != t' then
        let eq ← mkEqTrans (← mkExpectedTypeHint (← mkEqRefl t) (← mkEq t t')) (← r.getProof)
        if let some (d, po) ← sub r.expr then
          let p ← mkAppM ``Dominated.trans
            #[← mkAppM ``Dominated.of_le #[← fn (← mkAppM ``Nat.le_of_eq #[eq])], po]
          return some (d, ← hinted p t d)
  bound true

/-- Whether the body of `f` matches on a pattern (a `match`, `casesOn` or recursor), whose variables
degree synthesis cannot see. -/
def matchesPattern (f : Lean.Expr) : MetaM Bool := do
  withLocalDeclD `x (← domainOf f) fun x => do
    let body := (mkApp f x).headBeta
    let env ← getEnv
    return (body.find? fun e =>
      (e.getAppFn.constName?.any fun n => n.isStr && (n.getString! == "casesOn" ||
        n.getString! == "rec" || (Lean.Meta.Match.Extension.getMatcherInfo? env n).isSome))).isSome

/-- The condition of an `if` in the body of `f` that depends only on the input, not on variables
bound in the body, as a predicate on the input. -/
def conditionOf? (f : Lean.Expr) : MetaM (Option Lean.Expr) := do
  withLocalDeclD `x (← domainOf f) fun x => do
    let some t := (mkApp f x).headBeta.find? fun t =>
        (t.isAppOfArity ``ite 5 || t.isAppOfArity ``dite 5) && !t.getAppArgs[1]!.hasLooseBVars
      | return none
    return some (← mkLambdaFVars #[x] t.getAppArgs[1]!)

/-- Whether the right side has a power of degree at least 2, also once the definitions of the list
are unfolded. Products and powers are compared only then: a product or power of non-constant terms
has degree at least 2. -/
def hasHighPower (g : Lean.Expr) : DominatedM Bool := do
  withLocalDeclD `x (← domainOf g) fun x => do
    let r := (mkApp g x).headBeta
    let high (r : Lean.Expr) := (r.find? fun t => t.isAppOfArity ``HPow.hPow 6 &&
      (t.appArg!.nat?.any (2 ≤ ·) || !t.appArg!.isLit && t.appArg!.nat?.isNone)).isSome
    if high r then return true
    -- The right side read through the definitions of the list.
    let (r', _) ← simp r (← read).sizesUnfold
    return high r'.expr

/-- `Dominated f g` by degree synthesis. The candidate bases `S`, with exponents `e`, are the powers
of `g`, first those of its linear form and then those within its terms, also once the definitions
of the list are unfolded (read only here: the goals left to the user keep `g`), and lastly `g`
itself with exponent 1. For a positive `S`, the degree `d` of the left side comes from `degree`,
and when `d ≤ e`, `Dominated (fun x => S x ^ e) g` from the pointwise step. All candidates are
tried by the rules alone before any is tried thoroughly. On the element domain of a traversal, the
`Dominated` hypotheses about the outer input are composed with the projection to it. -/
def viaDegree (f g : Lean.Expr) : DominatedM (Option Lean.Expr) := do
  let outer := (← getLCtx, ← getLocalInstances)
  withLocalDeclD `x (← domainOf f) fun x => do
    let body := (mkApp f x).headBeta
    let r := (mkApp g x).headBeta
    -- The powers of the right side: those of its linear form first, then those within its terms.
    let powers (e : Lean.Expr) : MetaM (Array (Lean.Expr × Nat)) := do
      let (_, nested) ← (e.forEach' fun t => do
          if t.isAppOfArity ``HPow.hPow 6 && !t.hasLooseBVars then modify (·.push t)
          return true : StateT (Array Lean.Expr) MetaM Unit).run #[]
      let mut out := #[]
      for t in (linearForm e).2.map (·.1) ++ nested do
        unless t.isAppOfArity ``HPow.hPow 6 do continue
        let some n ← (evalNat t.appArg!).run | continue
        let b := t.getAppArgs[4]!
        unless 0 < n && (← isDefEq (← inferType b) (mkConst ``Nat)) do continue
        unless out.contains (b, n) do out := out.push (b, n)
      return out
    let mut candidates : Array (Lean.Expr × Nat) := ← powers r
    -- Facts about the outer input, along the projection to it on an element domain.
    let domain ← whnfR (← domainOf f)
    let mut composedFacts : Array (Lean.Expr × Lean.Expr) := #[]
    if domain.isAppOf ``Sigma then
      let projection ← withLocalDeclD `z domain fun z => do
        mkLambdaFVars #[z] (← mkAppM ``Sigma.fst #[z])
      for (h, type) in (← read).facts do
        if let some h' ← (observing? (mkAppM ``Dominated.comp #[h, projection]) : MetaM _) then
          let lam (k : Lean.Expr) := withLocalDeclD `z domain fun z => do
            mkLambdaFVars #[z] (mkApp k (mkApp projection z)).headBeta
          let composed ← mkAppM ``Dominated #[← lam type.appFn!.appArg!, ← lam type.appArg!]
          composedFacts := composedFacts.push (← mkExpectedTypeHint h' composed, composed)
    let (r', _) ← simp r (← read).sizesUnfold
    let projected ← projectedIn #[body, r, r'.expr]
    if r'.expr != r then
      for c in ← powers r'.expr do
        unless candidates.contains c do candidates := candidates.push c
    -- The right side itself, unless it is already a power among the candidates.
    unless r.isAppOfArity ``HPow.hPow 6 && candidates.any (·.1 == r.getAppArgs[4]!) do
      candidates := candidates.push (r, 1)
    -- First by the rules alone, then also bounding products, powers and differences as wholes.
    for thorough in [false, true] do
      for (base, e) in candidates do
        let S ← mkLambdaFVars #[x] base
        let some hS ← withLCtx outer.1 outer.2 (positive S) | continue
        let saved ← show TacticM _ from saveState
        let run : DominatedM (Option (Nat × Lean.Expr)) :=
          withReader (fun c => { c with facts := c.facts ++ composedFacts })
            (degree outer projected thorough x S hS body)
        let res ← try run catch _ => do
          saved.restore
          pure none
        let some (d, p) := res | continue
        if d > e then continue
        let p ← (do
          if d == e then return p
          mkAppM ``Dominated.mono_pow
            #[p, ← mkDecideProof (← mkAppM ``LE.le #[mkNatLit d, mkNatLit e]), hS] :
            MetaM Lean.Expr)
        let Se ← mkLambdaFVars #[x] (← mkAppM ``HPow.hPow #[base, mkNatLit e])
        let mut q? : Option Lean.Expr := none
        if base == r && e == 1 then
          q? := some (← mkAppM ``Dominated.of_le #[← mkLambdaFVars #[x] (← mkAppM ``Nat.le_of_eq
            #[← mkAppM ``Nat.pow_one #[base]])])
        else
          q? ← withLCtx outer.1 outer.2 (attempt (proveBase Se g))
        let some q := q? | continue
        let h ← instantiateMVars (← mkAppM ``Dominated.trans #[p, q])
        if h.containsFVar x.fvarId! || h.hasMVar then continue
        return some h
    return none

/-- Unfold compositions, so that matching a fact is reducible and cheap to fail. -/
def unfoldComp (e : Lean.Expr) : MetaM Lean.Expr := Meta.transform e (post := fun t => do
  if t.isAppOfArity ``Function.comp 5 then
    let args := t.getAppArgs
    return .done (← withLocalDeclD `x args[0]! fun x => do
      mkLambdaFVars #[x] (mkApp args[3]! (mkApp args[4]! x).headBeta).headBeta)
  return .continue)

/-- Whether `f` is the encoded size of a projection, possibly nested, of the value whose encoded
size is `f'`: a fact about `f'` then bounds `f` through the pointwise step. -/
def sizeOfProjection (f f' : Lean.Expr) : MetaM Bool := do
  withLocalDeclD `z (← domainOf f) fun z => do
    let a := (mkApp f z).headBeta
    let b := (mkApp f' z).headBeta
    let value? (e : Lean.Expr) : Option Lean.Expr :=
      if e.isAppOfArity ``Tree.size 1 && e.appArg!.isAppOfArity ``UniqueEncoding.encode 4 then
        some e.appArg!.appArg! else none
    let some va := value? a | return false
    let some vb := value? b | return false
    return va != vb && (va.find? (· == vb)).isSome

/-- `Dominated f g` through a fact `Dominated f' g'`: directly when `g'` is `g`, otherwise with
`Dominated g' g` from `proveBase`, or by degree synthesis when `g` has a power of degree at least 2,
so facts are never chained. `f'` is `f`, or a value of which `f` is the size of a projection, with
`Dominated f f'` from `proveBase`. On the element domain of a traversal, a fact about the outer
input is used along the projection to that input. -/
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
      let f' := type.appFn!.appArg!
      let mut h := h
      unless ← withReducible (isDefEq f' f) do
        -- A fact about a value also bounds the size of its projections.
        unless ← sizeOfProjection f f' do continue
        let some hf ← memo (← mkAppM ``Dominated #[f, f']) (attempt (proveBase f f')) | continue
        h ← mkAppM ``Dominated.trans #[hf, h]
      let g' := type.appArg!
      if ← withReducible (isDefEq g' g) then return some h
      if let some rest ← memo (← mkAppM ``Dominated #[g', g]) (do
          if let some h ← attempt (proveBase g' g) then return some h
          unless ← hasHighPower g do return none
          attempt (viaDegree g' g)) then
        return some (← mkAppM ``Dominated.trans #[h, rest])
  return none

/-- Expand encoded sizes in `f` with `ctx` and split its sums, maxima and zeros, and the minuends
of its differences; `leaf` proves `Dominated a g` for the remaining summands `a`. The right side
`g` is not rewritten. -/
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
    if body.isAppOfArity ``HSub.hSub 6 then
      -- The difference itself when it is the target or a fact; its minuend otherwise.
      if ← withReducible (isDefEq f g) then return some (← mkAppM ``Dominated.refl #[g])
      if let some h ← attempt (viaFacts f g) then return some h
      let some h ← go (part body.appFn!.appArg!) | return none
      return some (← mkAppM ``Dominated.sub_left #[h, part body.appArg!])
    if body.nat? == some 0 then
      let zero ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``Dominated #[f, g])
      let _ ← zero.mvarId!.apply (← mkConstWithFreshMVarLevels ``Dominated.zero)
      return some (← instantiateMVars zero)
    leaf f g
  let some proof ← go r.expr | return none
  let some eq := r.proof? | return some proof
  let motive ← withLocalDeclD `F (← inferType f) fun F => do
    mkLambdaFVars #[F] (← mkAppM ``Dominated #[F, g])
  let proof ← mkExpectedTypeHint proof (← mkAppM ``Dominated #[r.expr, g])
  return some (← mkEqMPR (← mkCongrArg motive eq) proof)

/-- `Dominated f g` pointwise with the facts about the products and powers that `f` depends on
(`addPowerFacts`), for a `match` on a pattern, whose variables degree synthesis cannot see. This
keeps the earlier treatment of products and powers for these summands, provisionally (plan W2). -/
def viaPowerFacts (f g : Lean.Expr) : DominatedM (Option Lean.Expr) := do
  modify fun s => { s with nonlinear := true }
  let r ← attempt (do
    if let some h ← viaFacts f g then return some h
    proveBase f g)
  modify fun s => { s with nonlinear := false }
  return r

/-- `Dominated f g` for a left side with an `if` whose condition depends only on the
input, by `Dominated.of_cases` on the condition. On each part the condition is the property of the
subtype, which settles the `if`s on it, and the part is split and proved again. -/
def viaCases (prove : Lean.Expr → Lean.Expr → DominatedM (Option Lean.Expr)) (f g : Lean.Expr) :
    DominatedM (Option Lean.Expr) := do
  let α ← domainOf f
  let some p ← conditionOf? f | return none
  let part (holds : Bool) : DominatedM (Option Lean.Expr) := do
    let pred ← if holds then pure p else withLocalDeclD `x α fun x => do
      mkLambdaFVars #[x] (mkNot (mkApp p x).headBeta)
    -- The part is proved outside the scope of `y`, so that no auxiliary proof captures it.
    let (f', g', funEq) ← withLocalDeclD `y (← mkAppM ``Subtype #[pred]) fun y => do
      let val ← mkAppM ``Subtype.val #[y]
      let hy ← mkAppM ``Subtype.property #[y]
      let c := (mkApp p val).headBeta
      let body := (mkApp f val).headBeta
      let mut cur := body
      let mut eq ← mkEqRefl body
      -- Settle the `if`s on the condition, one at a time.
      repeat
        let some t := cur.find? fun t => (t.isAppOfArity ``ite 5 || t.isAppOfArity ``dite 5) &&
            t.getAppArgs[1]! == c | break
        let args := t.getAppArgs
        let rule := if t.isAppOfArity ``ite 5 then
            (if holds then ``ite_eq_left else ``ite_eq_right)
          else (if holds then ``dite_eq_left else ``dite_eq_right)
        let h ← mkAppOptM rule #[c, args[2]!, hy, args[0]!, args[3]!, args[4]!]
        let abst ← kabstract cur t
        let motive := Lean.mkLambda `z .default args[0]! abst
        eq ← mkEqTrans eq (← mkCongrArg motive h)
        cur := abst.instantiate1 (← inferType h).appArg!
      return (← mkLambdaFVars #[y] cur, ← mkLambdaFVars #[y] (mkApp g val).headBeta,
        ← mkFunExt (← mkLambdaFVars #[y] eq))
    let some proof ← split f' g' (← read).sizes prove | return none
    let motive ← withLocalDeclD `F (← inferType f') fun F => do
      mkLambdaFVars #[F] (← mkAppM ``Dominated #[F, g'])
    return some (← mkEqMPR (← mkCongrArg motive funEq) proof)
  let some yes ← part true | return none
  let some no ← part false | return none
  return some (← mkAppOptM ``Dominated.of_cases #[α, f, g, p, yes, no])

/-- One summand against the target: a fact; a traversal rule, comparing a maximum over a list,
possibly of dependent elements, element by element and a table sum entry by entry after multiplying
each entry by the table length; the linear pointwise step; and, against a power of degree at least
2 on the right, the facts about products and powers for a `match` on a pattern, cases on the
condition of an `if`, or degree synthesis. Traversal rules read the target on the element domain
and split the element, which must be proved completely. -/
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
    if let some h ← attempt (proveBase f g) then return some h
    unless ← hasHighPower g do return none
    if ← matchesPattern f then return ← viaPowerFacts f g
    if (← conditionOf? f).isSome then return ← attempt (viaCases prove f g)
    attempt (viaDegree f g)

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
as facts. The list gives definitions to unfold when comparing pointwise, and statements `a ≤ b`,
`a < b` or `a = b` to instantiate at matching terms there, as for those registered with
`@[dominated]`. Products and powers are compared by their degrees against the powers of the
right side, read through the definitions of the list: an equation about the right side given in the
list is not used for this. Summands that cannot be proved are left as goals. -/
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
      if (key? body).isNone then
        throwErrorAt arg
          "dominated: expected a definition or a statement `a ≤ b`, `a < b` or `a = b`"
      lemmas := lemmas.push e
    let goal ← getMainGoal
    let target := (← instantiateMVars (← goal.getType)).consumeMData
    unless target.isAppOf ``Dominated do throwError "dominated: expected a `Dominated` goal"
    let mut facts := #[]
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let type := (← instantiateMVars decl.type).consumeMData
      if type.isAppOf ``Dominated then facts := facts.push (decl.toExpr, ← unfoldComp type)
    let sizes ← simpContext #[``Function.comp_apply, ``Nat.mul_one, ``Tree.size_pair]
      (attrs := #[`dominated_simp])
    let sizesUnfold ← simpContext #[``Function.comp_apply, ``Nat.mul_one, ``Tree.size_pair] unfolds
      (attrs := #[`dominated_simp])
    let sizesMul ← simpContext
      #[``Function.comp_apply, ``Nat.mul_add, ``Nat.mul_one, ``Nat.mul_zero]
      (attrs := #[`dominated_simp])
    let expand ← simpContext (simpOnlyBuiltins.toArray ++ #[``Function.comp_apply, ``max_le_iff,
      ``Tree.size_pair, ``not_true_eq_false,
      ``List.map_const', ``List.sum_replicate, ``smul_eq_mul, ``pow_zero]) unfolds
      (attrs := #[`dominated_simp, `dominated_expand])
    let numerals := #[← (← (← ({} : Simp.Simprocs).add ``Nat.reduceMul true).add ``Nat.reduceAdd
      true).add ``encodeParts true]
    let ctx : Context :=
      { statements := ← factTree lemmas, premises := ← premiseTree, facts, sizes, sizesMul,
        expand, numerals, sizesUnfold }
    let (proof, state) ← (split target.appFn!.appArg! target.appArg! ctx.sizes proveOrLeave
      |>.run ctx).run {}
    let some proof := proof | throwError "dominated: no proof"
    goal.assign (← mkExpectedTypeHint proof target)
    replaceMainGoal (state.left.map (·.2)).toList

end Complexity.Tactic.Dominated
