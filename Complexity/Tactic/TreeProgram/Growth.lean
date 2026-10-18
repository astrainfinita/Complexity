/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Tactic.TreeProgram.Rules
public import Complexity.Encoding.TreeSize

/-! # Closing growth comparisons

`dominated` proves `Dominated f g` when both sides are given, as left by `source_fun_prop` and
`model_fun_prop`. It never changes either side. Sums and maxima on the left are split; each
summand is compared with the target pointwise after destructuring the input, splitting the
source cases, expanding encoded sizes and adding size facts for `omega`; powers and products are
compared through their bases. Maxima over lists and sums over tables are compared entry by entry.
The coefficient is a hidden witness. Hints name definitions to unfold or equations to use; facts
that are genuine properties of the source function are given as `Dominated` hypotheses. Summands
that cannot be proved are left as goals.
-/

public meta section

open Lean Meta Elab Tactic

namespace Complexity.TreeProgram.Source.Growth

/-- Facts about every encoded size, list length and positive power occurring in the goal. -/
def addSizeFacts : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
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
  let (_, (sizes, lengths, powers, appends)) ← (target.forEach' fun e => do
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
      if v.isAppOfArity ``List.range 1 then
        facts := facts.push (← mkAppM ``size_encode_range_le #[v.appArg!])
      if v.isAppOfArity ``Function.comp 5 then
        if let some h ← observing? (mkAppM ``size_encode_fin_comp_le #[v.appArg!, v.appFn!.appArg!])
        then facts := facts.push h
      if v.isAppOfArity ``HAdd.hAdd 6 && v.appArg!.nat? == some 1 then
        if let some h ← observing? (mkAppM ``size_encode_nat_succ_le #[v.appFn!.appArg!]) then
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
  let mut goal := goal
  for h in facts do
    let (_, g) ← (← goal.assert `size_fact (← inferType h) h).intro1P
    goal := g
  replaceMainGoal [goal]

/-- Add size facts for the encoded sizes, list lengths and positive powers in the goal. -/
elab (name := sizeFacts) "size_facts" : tactic => addSizeFacts

/-- For powers `a ^ d` and `b ^ e` in the goal with `d ≤ e`, add `a ^ d ≤ b ^ e` whenever `omega`
proves `a ≤ b` and `0 < b`; for a product `a * b` in a hypothesis and a power `c ^ e` with
`2 ≤ e`, add `a * b ≤ c ^ e` whenever `omega` proves `a ≤ c`, `b ≤ c` and `0 < c`. -/
def addPowerFacts : TacticM Unit := withMainContext do
  let goal ← getMainGoal
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
      evalTactic (← `(tactic| omega))
      setGoals [goal]
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
      if d > e || a == b then continue
      let some hb ← pos b | continue
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
  for (a, b) in products.toList.eraseDups do
    for (c, e) in powers do
      if e < 2 then continue
      let some hac ← le a c | continue
      let some hbc ← le b c | continue
      let some hc ← pos c | continue
      let square ← mkAppM ``Eq.le #[← mkAppM ``Eq.symm #[← mkAppM ``pow_two #[c]]]
      facts := facts.push (← mkAppM ``le_trans #[← mkAppM ``Nat.mul_le_mul #[hac, hbc],
        ← mkAppM ``le_trans #[square, ← powLe hc 2 e]])
  let mut goal := goal
  for h in facts do
    let (_, g) ← (← goal.assert `power_fact (← inferType h) h).intro1P
    goal := g
  replaceMainGoal [goal]

/-- Add comparisons between the powers in the goal that follow from comparisons of their bases. -/
elab (name := powerFacts) "power_facts" : tactic => addPowerFacts

/-- Use the equations left by splitting a `match`: an equation between constructor applications
is substituted, and the goal is closed when `cases` on an equation leaves no cases, as for a
branch that contradicts the test selecting it. -/
partial def casesEquations : TacticM Unit := withMainContext do
  for decl in ← getLCtx do
    let type ← instantiateMVars decl.type
    if decl.isImplementationDetail || !type.isAppOfArity ``Eq 3 then continue
    let constructor (e : Lean.Expr) : MetaM Bool := do
      let some name := (← whnfR e).getAppFn.constName? | return false
      return (← getEnv).find? name |>.any (·.isCtor)
    let injective := (← constructor type.appFn!.appArg!) && (← constructor type.appArg!)
    let saved ← saveState
    try
      let goals ← (← getMainGoal).cases decl.fvarId
      if goals.isEmpty then
        replaceMainGoal []
        return
      if let #[goal] := goals then
        if injective then
          replaceMainGoal [goal.mvarId]
          casesEquations
          return
    catch _ => pure ()
    saved.restore

/-- Substitute equations between constructor applications and close goals whose equations have no
cases. -/
elab (name := casesEquationsTac) "cases_equations" : tactic => casesEquations

/-- Split a `casesOn` or `rec` application whose major premise is a local variable. -/
def splitCasesOnVariable : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
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
    let goals ← (← getMainGoal).cases major.fvarId!
    replaceMainGoal (goals.map fun g => g.mvarId).toList
    return
  throwError "no casesOn on a variable"

/-- Split the first `casesOn` or `rec` application on a local variable in the goal. -/
elab (name := casesOnVariable) "cases_on_variable" : tactic => splitCasesOnVariable

/-- Split every local variable whose type is, up to reducible unfolding, a product, dependent
pair, subtype, unit, or a structure with a derived tree encoding; the latter's encoding is
rewritten to the encoding of its fields. -/
partial def splitStructures : TacticM Unit := withMainContext do
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let type ← whnfR decl.type
    let encodeMk := type.getAppFn.constName? |>.map (· ++ `encode_mk)
    let derived := encodeMk.any (← getEnv).contains
    let structural := derived || [``Prod, ``Sigma, ``PSigma, ``Subtype, ``PProd, ``PUnit].any
      type.getAppFn.isConstOf
    if structural then
      let goals ← (← getMainGoal).cases decl.fvarId
      let goals := (goals.map fun g => g.mvarId).toList
      let mut remaining := []
      for g in goals do
        setGoals [g]
        splitStructures
        remaining := remaining ++ (← getGoals)
      setGoals remaining
      return

/-- Split local variables of product, dependent pair, subtype, unit and derived structure
types. -/
elab (name := destructInputs) "destruct_inputs" : tactic => splitStructures

/-- Rewrite the encoding of every constructor application of a type with a derived tree encoding
to the encoding of its fields. -/
def expandDerivedEncodings : TacticM Unit := withMainContext do
  let env ← getEnv
  let mut exprs := #[← instantiateMVars (← getMainTarget)]
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do exprs := exprs.push (← instantiateMVars decl.type)
  let names := exprs.foldl (init := #[]) fun acc e => e.foldConsts acc fun c acc =>
    let encodeCtor := c.getPrefix ++ .mkSimple s!"encode_{c.getString!}"
    if c.isStr && (env.find? c).any (·.isCtor) && env.contains encodeCtor &&
        !acc.contains encodeCtor then
      acc.push encodeCtor else acc
  unless names.isEmpty do
    let lemmas ← names.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
    evalTactic (← `(tactic| try simp only [size_encode_prod, $lemmas,*] at *))

/-- Rewrite encodings of constructor applications of derived types to the encodings of their
fields. -/
elab (name := encodeFields) "encode_fields" : tactic => expandDerivedEncodings

/-- Reduce natural-number projections in the types of local variables, as in the indices of a
recursive result's type. -/
def reduceVariableTypes : TacticM Unit := withMainContext do
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
  let mut goal ← getMainGoal
  for decl in ← getLCtx do
    if decl.isImplementationDetail || (← isProp decl.type) then continue
    let type ← reduce decl.type
    if type != decl.type then goal ← goal.replaceLocalDeclDefEq decl.fvarId type
  replaceMainGoal [goal]

/-- State each encoding at the inferred type of the encoded value, so that the size of a
dependent recursive result is one `omega` atom and its pairs expand, however its type was
reached. -/
def normalizeVariableEncodings : TacticM Unit := do
  reduceVariableTypes
  withMainContext do
  let normalize (e : Lean.Expr) : MetaM Lean.Expr := do
    Meta.transform (← instantiateMVars e) (post := fun t => do
      if t.isAppOfArity ``UniqueEncoding.encode 4 && !t.hasLooseBVars then
        let args := t.getAppArgs
        let type ← instantiateMVars (← inferType t.appArg!)
        if type != args[1]! then
          if let some inst ← synthInstance? (← mkAppM ``UniqueEncoding #[args[0]!, type]) then
            return .done (mkAppN t.getAppFn #[args[0]!, type, inst, args[3]!])
      return .continue)
  let mut goal ← getMainGoal
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let type ← normalize decl.type
    if type != decl.type then goal ← goal.replaceLocalDeclDefEq decl.fvarId type
  goal ← goal.replaceTargetDefEq (← normalize (← goal.getType))
  replaceMainGoal [goal]

/-- State encodings at the inferred types of the encoded values. -/
elab (name := normalizeEncodings) "normalize_encodings" : tactic => normalizeVariableEncodings

/-- Pointwise size arithmetic: destructure the input, split its cases, expand encoded sizes and
use the size facts with `omega`. -/
syntax (name := sizeOmega) "size_omega" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| size_omega $[[$hints,*]]?) => do
    let hints := hints.map (·.getElems) |>.getD #[]
    `(tactic| (
      try destruct_inputs
      try dsimp only
      repeat' (first | (split <;> try dsimp only) | (cases_on_variable <;> try dsimp only))
      all_goals
        try encode_fields
        try cases_equations
        try dsimp only [id] at *
        try normalize_encodings
      all_goals
        try simp only [size_encode_prod, Sigma.encode_mk, UniqueEncoding.encode_subtype,
          encode_list_cons, encode_list_nil, size_encode_unit, encode_bool_true,
          encode_bool_false, size_encode_reverse, List.length_reverse, List.length_cons,
          List.length_nil, List.length_append, List.length_map, Tree.encode_self,
          encode_option_some, encode_option_none, encode_fin, encode_fin_castSucc, Fin.val_last,
          Function.comp_apply, max_le_iff, List.map_const', List.sum_replicate, smul_eq_mul,
          pow_zero, $hints,*] at *
        try encode_fields
        try normalize_encodings
        repeat' (first | (split <;> try dsimp only) | (cases_on_variable <;> try dsimp only))
        all_goals
          first
          | (size_facts
             try simp only [size_encode_prod, size_encode_reverse, List.length_reverse] at *
             power_facts
             omega)
          | (try simp [size_encode_prod, $hints,*] at *
             size_facts
             try simp only [size_encode_prod, size_encode_reverse, List.length_reverse] at *
             omega)))

/-- A summand bounded by the target without using hypotheses: the target itself, a constant,
or a pointwise bound. The coefficient is a hidden witness; any large enough one serves, so a
single one, `2 ^ 40`, is tried. -/
syntax (name := dominatedBase) "dominated_base" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| dominated_base $[[$hints,*]]?) => do
    let hints := hints.map (·.getElems) |>.getD #[]
    `(tactic| first
      | with_reducible exact Dominated.refl _
      | with_reducible exact Dominated.zero
      | (with_reducible apply Dominated.const_of_pos; assumption)
      | (apply Dominated.const_of_pos; intro x; size_omega [$hints,*])
      | (apply Dominated.of_le_mul 1099511627776; intro x; size_omega [$hints,*]))

/-- One summand against the target: `dominated_base`, a hypothesis, or a hypothesis followed by
`dominated_base`; a maximum over a list, possibly of dependent elements, is compared element by
element, and a table sum against a power of a scale bounds its length and entries by the scale. -/
syntax (name := dominatedLeaf) "dominated_leaf" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| dominated_leaf $[[$hints,*]]?) => do
    let hints := hints.map (·.getElems) |>.getD #[]
    `(tactic| first
      | assumption
      | dominated_base [$hints,*]
      | exact Dominated.trans (by assumption) (by dominated_base [$hints,*])
      | (with_reducible (apply Dominated.list_foldr_max_le); dominated_leaf [$hints,*])
      | (with_reducible (apply Dominated.foldr_max_le); dominated_leaf [$hints,*])
      | (with_reducible (apply Dominated.sum_finRange_pow (by decide))) <;>
          first | dominated_leaf [$hints,*] | (intro x; size_omega [$hints,*]))

/-- Close a growth comparison `Dominated f g` whose two sides are given, splitting sums and
maxima of the left side. Hints are definitions to unfold or equations to use pointwise.
Leaves that cannot be proved are left as goals. -/
syntax (name := dominated) "dominated" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| dominated $[[$hints,*]]?) => do
    let hints := hints.map (·.getElems) |>.getD #[]
    `(tactic| (
      try simp only [Dominated.add_iff, Dominated.max_iff, Dominated.zero, true_and, and_true,
        size_encode_prod, Sigma.encode_mk, size_encode_unit, size_encode_reverse,
        List.length_reverse]
      repeat' apply And.intro
      all_goals try dominated_leaf [$hints,*]))

end Complexity.TreeProgram.Source.Growth
