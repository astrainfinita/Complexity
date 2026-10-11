/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Tactic.TreeProgram.Rules
public meta import Complexity.Tactic.TreeProgram.Search
public meta import Complexity.Tactic.TreeProgram.Environment
public import Complexity.Models.TreeMachine.Language.Derive
public meta import Complexity.Models.TreeMachine.Language.Semantics
public import Complexity.Resources.TreeMachine.Program
public import Complexity.Classes.Functions.Basic
public meta import Lean.Meta.Match.MatcherApp.Basic
public meta import Lean.Meta.RecExt

/-! # Certified translation of Lean source functions -/

@[expose] public section

open Complexity TreeProgram

namespace Complexity.TreeProgram.Source

theorem Implements.computableInTimeAndSpace {α β : Type*}
    [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {p : Value → Code Value} {f : α → β} {b : Bounds α} {time space : ℕ → ℕ}
    (hp : Implements p f b)
    (hb : ∀ x, b.time x + 4 ≤ time ⌜x⌝ₜ.size ∧
      max ⌜x⌝ₜ.size (b.peak x) + 2 ≤ space ⌜x⌝ₜ.size) :
    TimeSpaceModel.tree.ComputableInTimeAndSpace f time
      (fun n => (p .input).registers * space n) := by
  refine ⟨_, ⟨(p .input).registers, inferInstance, _, inferInstance,
    (p .input).compile, rfl⟩, ?_⟩
  apply Encoding.Computes.iff_of_uniqueEncoding.mpr
  intro x
  have hr := (hp.2 .input 1 (Function.update (fun _ => Tree.nil) 0 ⌜x⌝ₜ) x
    le_rfl (by simp)).mono le_rfl (Nat.le_max_right ⌜x⌝ₜ.size _) (fun _ _ h => h.1)
  exact (hr.compile (Nat.le_max_left _ _)).mono (hb x).1
    (Nat.mul_le_mul_left _ (hb x).2)

theorem Implementation.computableInTimeAndSpace {α β : Type*}
    [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {f : α → β} {time space : ℕ → ℕ} (hf : Implementation f)
    (hb : ∀ x, hf.bounds.time x + 4 ≤ time ⌜x⌝ₜ.size ∧
      max ⌜x⌝ₜ.size (hf.bounds.peak x) + 2 ≤ space ⌜x⌝ₜ.size) :
    TimeSpaceModel.tree.ComputableInTimeAndSpace f time
      (fun n => (hf.program .input).registers * space n) :=
  hf.implements.computableInTimeAndSpace hb

theorem Realizes.computableInTimeAndSpace {α β : Type*}
    [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {f : α → β} {b : Bounds α} {time space : ℕ → ℕ} (hf : Realizes f b)
    (hb : ∀ x, b.time x + 4 ≤ time ⌜x⌝ₜ.size ∧
      max ⌜x⌝ₜ.size (b.peak x) + 2 ≤ space ⌜x⌝ₜ.size) :
    ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace f time (fun n => k * space n) :=
  hf.elim fun _ hp => ⟨_, hp.computableInTimeAndSpace hb⟩

end Complexity.TreeProgram.Source

end

public meta section


namespace Complexity.TreeProgram.Source

namespace FiniteCases
open Lean Meta

-- Instantiate structural pair equations explicitly, including opaque Sigma inputs.
-- Dependent field types can need more transparency than simp's matching allows.
private def expandPair (e : Lean.Expr) : SimpM Simp.Step := withTransparency .default do
  unless e.isAppOfArity ``UniqueEncoding.encode 4 do return .continue
  let args := e.getAppArgs
  let ty ← whnf args[1]!
  let (name, equation) ← if ty.isAppOfArity ``Prod 2 then pure (``Prod, ``encode_prod)
    else if ty.isAppOfArity ``Sigma 2 then pure (``Sigma, ``Sigma.encode_mk)
    else return .continue
  let value := args[3]!
  let proof ← mkAppOptM equation #[some ty.getAppArgs[0]!, some ty.getAppArgs[1]!,
    none, none, some (← mkAppM (name ++ `fst) #[value]), some (← mkAppM (name ++ `snd) #[value])]
  let some (_, lhs, rhs) := (← inferType proof).eq? | return .continue
  unless ← withTransparency .default (isDefEq lhs e) do return .continue
  return .visit { expr := rhs, proof? := some proof }

/-- Expose only product and dependent-pair structure when analyzing an encoded result. -/
simproc_decl sourcePair (encode Tree _) := expandPair

end FiniteCases

open Lean Meta Elab Tactic in
private partial def independentValue (x : FVarId) (value : Lean.Expr) : MetaM Lean.Expr := do
  let type ← inferType value
  unless type.containsFVar x do return value
  if (← whnf type).isAppOfArity ``Prod 2 then
    let left ← if value.isAppOfArity ``Prod.mk 4 then pure value.getAppArgs[2]!
      else mkAppM ``Prod.fst #[value]
    let right ← if value.isAppOfArity ``Prod.mk 4 then pure value.getAppArgs[3]!
      else mkAppM ``Prod.snd #[value]
    let left ← independentValue x left
    let right ← independentValue x right
    mkAppM ``Prod.mk #[left, right]
  else
    mkAppM ``encode #[mkConst ``Tree, value]

open Lean Meta Elab Tactic in
private partial def structuralResult (x : FVarId) (lhs : Lean.Expr) (dependentOnly : Bool) :
    TacticM (Lean.Expr × Lean.Expr) := do
  let source := lhs.appArg!.headBeta
  if source.isAppOfArity ``UniqueEncoding.encode 4 then
    if ← isDefEq source.getAppArgs[0]! (mkConst ``Tree) then
      let self ← mkAppM ``Tree.encode_self #[source]
      let some (_, start, _) := (← inferType self).eq? |
        throwError "source translation: expected the tree encoding identity"
      if ← isDefEq start lhs then
        let (code, proof) ← structuralResult x source false
        return (code, ← mkEqTrans self proof)
  -- Expose the source constructor before matching its structural encoding equation.
  let value ← whnf lhs.appArg!
  if dependentOnly && !(← isConstructorApp value) then
    Search.unsupported "dependent result construction requires a known constructor"
  let ctx ← mkSimpContext (← `(tactic| simp)) false
  let (r, _) ← simp (mkAppN lhs.getAppFn (lhs.getAppArgs.set! 3 value)) ctx.ctx ctx.simprocs
  if lhs == r.expr then Search.unsupported "no structural encoding equation applies"
  unless r.expr.isAppOfArity ``UniqueEncoding.encode 4 do
    Search.unsupported "expected a structural encoding"
  unless r.expr.getAppArgs[1]!.containsFVar x do
    if dependentOnly then
      Search.unsupported "the structural result type is independent of the input"
    return (r.expr, ← r.getProof)
  unless ← isConstructorApp value do
    Search.unsupported "dependent result construction requires a known constructor"
  let value ← independentValue x r.expr.appArg!
  let code ← mkAppM ``encode #[mkConst ``Tree, value]
  let some proof ← Mathlib.Meta.FunProp.tacticToDischarge
    (← `(tactic| simp only [encode_prod, Tree.encode_self, FiniteCases.sourcePair]))
      (← mkEq r.expr code) |
    throwError "the structural result changed its encoding"
  return (code, ← mkEqTrans (← r.getProof) proof)

open Lean Meta in
private def typedSourceProof (type proof : Lean.Expr) : MetaM Lean.Expr := do
  if ← withReducible (isDefEq type (← inferType proof)) then return proof
  mkAuxTheorem type proof

open Lean Meta Elab Tactic in
/-- Prove a structural encoding equation for a source function's result. -/
elab (name := sourceEncoding) "source_encoding" : tactic => do
  let (x, goal) ← (← getMainGoal).intro1
  replaceMainGoal [goal]
  withMainContext do
    let some (_, lhs, rhs) := (← goal.getType).eq? |
      throwError "expected an encoding equation"
    let (code, proof) ← structuralResult x lhs false
    unless rhs.isAppOfArity ``UniqueEncoding.encode 4 do throwError "expected an encoding"
    for (a, b) in code.getAppArgs.zip rhs.getAppArgs do
      unless ← isDefEq a b do throwError "incompatible structural encoding"
    let proof ← typedSourceProof (← instantiateMVars (← goal.getType)) proof
    closeMainGoal `source_encoding proof

open Lean Meta Elab Tactic in
private def sourceGoalArgs (goal : MVarId) : MetaM (Array Lean.Expr × Lean.Expr) := do
  let target ← instantiateMVars (← goal.getType)
  if target.isAppOfArity ``Realizes 6 then
    return (target.getAppArgs.extract 0 5, target.getAppArgs[5]!)
  unless target.isAppOfArity ``Implementation 5 do
    throwError "source translation: expected Realizes or Implementation"
  let args := target.getAppArgs
  return (args, ← mkFreshExprMVar (← mkAppM ``Bounds #[args[0]!]))

open Lean Meta Elab Tactic in
private def certifySourceGoal (goal : MVarId) (args : Array Lean.Expr)
    (program bounds : Lean.Expr) : MetaM (MVarId × MetaM Unit) := do
  let type ← mkAppOptM ``Implements
    (args.extract 0 4 |>.map some |>.append #[some program, some args[4]!, some bounds])
  let certificate ← mkFreshExprSyntheticOpaqueMVar type
  return (certificate.mvarId!, goal.withContext do
    let type ← instantiateMVars type
    let proof ← typedSourceProof type (← instantiateMVars certificate)
    let implementation ← mkAppOptM ``Implementation.ofImplements
      (args.map some |>.append #[some program, some bounds, some proof])
    let target ← instantiateMVars (← goal.getType)
    let result ← if target.isAppOf ``Realizes then
      mkAppM ``Implementation.realizes #[implementation] else pure implementation
    goal.assign result)

open Lean Meta Elab Tactic in
private def sourceDependent : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let (args, bounds) ← sourceGoalArgs goal
  let #[input, output, inputInst, outputInst, f] := args |
    throwError "source dependent: invalid source arguments"
  let (g, proof) ← withLocalDeclD `x input fun x => do
    let lhs ← mkAppM ``encode #[mkConst ``Tree, mkApp f x]
    let (code, proof) ← structuralResult x.fvarId! lhs true
    let proof ← typedSourceProof (← mkEq lhs code) proof
    return (← mkLambdaFVars #[x] code.appArg!, ← mkLambdaFVars #[x] proof)
  if (← goal.getType).isAppOf ``Implementation then
    let next ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``Implementation #[g])
    goal.assign (← mkAppOptM ``Implementation.ofEncode #[some input, some output, none,
      some inputInst, some outputInst, none, some f, some g, some proof, some next])
    replaceMainGoal [next.mvarId!]
    return
  let next ← mkFreshExprMVar (← mkAppM ``Realizes #[g, bounds])
  goal.assign (← mkAppOptM ``Realizes.of_encode #[some input, some output, none,
    some inputInst, some outputInst, none, some f, some g, some bounds, some proof, some next])
  replaceMainGoal [next.mvarId!]

/-- Reinterpret a dependent source result through its structural encoding. -/
elab (name := sourceDependentTactic) "source_dependent" : tactic => sourceDependent

/-- Certify source branches with previously registered function implementations. -/
syntax (name := sourceCalls) "source_calls" : tactic
/-- Compose source-function specifications and synthesize their resource budget. -/
syntax (name := sourceFunProp) "source_fun_prop" : tactic

namespace FiniteCases
open Lean Meta Elab Tactic

private partial def projectionBase (e : Lean.Expr) : MetaM (Option FVarId) := do
  match ← whnf e with
  | .fvar id => return some id
  | .proj _ _ e => projectionBase e
  | .app f _ => projectionBase f
  | _ => return none

private def projectInput (path : List Bool) : TreeProgram.Expr Unit :=
  path.foldl (fun e right => if right then .right e else .left e) (.var ())

private def branchFunction (outer : LocalContext) (body : Lean.Expr) :
    MetaM (Lean.Expr × Lean.Expr) := do
  let body ← Environment.normalizeProjections body
  let mut used := collectFVars {} body
  for decl in (← getLCtx).foldl (fun ds d => d :: ds) [] do
    if used.fvarSet.contains decl.fvarId then
      used := collectFVars used (← Environment.normalizeProjections decl.type)
  let xs := (← getLCtx).foldl (init := #[]) fun xs decl =>
    if used.fvarSet.contains decl.fvarId && !outer.contains decl.fvarId then
      xs.push decl.toExpr else xs
  let packed ← Environment.packValues xs.toList
  let value := packed.value
  let type ← inferType value
  withLocalDeclD `env type fun env => do
    let function ← Environment.normalizeProjections (← mkLambdaFVars xs body)
    let function ← mkLambdaFVars #[env] (function.beta (← packed.unpack env))
    if (collectFVars {} function).fvarIds.any (!outer.contains ·) then
      Search.unsupported "source calls: branch environment is not closed"
    return (function, value)

-- Known roots select branches; all remaining subtrees are arbitrary encoded data.
private partial def inputLayout (e : Lean.Expr) (path : List Bool := []) :
    List (List Bool × Bool) × List (Lean.Expr × List Bool) :=
  if e.isConstOf ``Tree.nil then ([(path, false)], [])
  else if e.isAppOfArity ``Tree.pair 2 then
    let (ls, lf) := inputLayout e.getAppArgs[0]! (path ++ [false])
    let (rs, rf) := inputLayout e.getAppArgs[1]! (path ++ [true])
    ((path, true) :: ls ++ rs, lf ++ rf)
  else ([], [(e, path)])

private partial def outputExpr (e : Lean.Expr) (fields : List (Lean.Expr × List Bool)) :
    MetaM (TreeProgram.Expr Unit) := do
  if e.isConstOf ``Tree.nil then return .nil
  if e.isAppOfArity ``Tree.pair 2 then
    return .pair (← outputExpr e.getAppArgs[0]! fields) (← outputExpr e.getAppArgs[1]! fields)
  for (field, path) in fields do
    if ← isDefEq field e then return projectInput path
  Search.unsupported m!"source cases: output contains an operation needing its own certificate: {e}"

private structure CompiledCase where
  tests : List (List Bool × Bool)
  result : TreeProgram.Expr Unit
  goal : MVarId
  sourceGoal : MVarId
  inputCode : Lean.Expr
  output : Lean.Expr

private partial def caseDiscriminators (e : Lean.Expr) (fromMatcher := false) :
    MetaM (Array Lean.Expr) := do
  if let .proj _ _ base := e then return #[base]
  if let some matcher ← matchMatcherApp? e (alsoCasesOn := true) then
    -- The eliminator identifies the scrutinized input; other arguments may only be carried along.
    let info ← getConstInfo matcher.matcherName
    if info.value?.isSome then
      let value ← instantiateValueLevelParams info matcher.matcherLevels.toList
      let next ← whnf (value.beta e.getAppArgs)
      if next != e then return ← caseDiscriminators next true
    return matcher.discrs
  let .const name _ := e.getAppFn | return #[]
  let .recInfo info ← getConstInfo name | return #[]
  let some major := e.getAppArgs[info.getMajorIdx]? | return #[]
  if !fromMatcher && (← getConstInfoInduct info.getMajorInduct).isRec then return #[]
  return #[major]

-- Prune immediate contradictions, without recursively searching stored data for emptiness.
private def closeImpossibleCase (g : MVarId) : MetaM Bool :=
  g.contradictionCore { searchFuel := 1, useDecide := false }

private partial def visitCases {α : Type} (g : MVarId) (f : Lean.Expr) (inputName : Name)
    (ctx : Simp.Context) (procs : Simp.SimprocsArray)
    (leaf : MVarId → LocalDecl → Lean.Expr → Lean.Expr → MetaM α)
    (requireBranch := false) (branched := false)
    (record : MVarId → Option FVarId → Array CasesSubgoal → MetaM Unit := fun _ _ _ => pure ()) :
    MetaM (Array α) :=
    withIncRecDepth <| g.withContext do
  if ← closeImpossibleCase g then
    record g none #[]
    return #[]
  let some decl := (← getLCtx).findFromUserName? inputName | throwError "missing source input"
  let some (_, _, inputCode) := decl.type.eq? | throwError "expected source input equation"
  let input := inputCode.appArg!
  -- A coded field is already present in the input; do not classify inside its encoder.
  let out := f.beta #[input]
  let out ← if out.isAppOfArity ``UniqueEncoding.encode 4 then pure out else
    withCanUnfoldPred (fun cfg info => do
      if info.name == ``UniqueEncoding.encode then return false
      canUnfoldDefault cfg info) (whnf out)
  let inspected ← if out.isAppOfArity ``UniqueEncoding.encode 4 then whnf out.appArg!
    else pure out
  let discrs ← caseDiscriminators inspected
  unless discrs.isEmpty do
    for discr in discrs.reverse do
      let discr := (← simp discr ctx procs).1.expr
      let ty ← whnf (← inferType discr)
      let .const name _ := ty.getAppFn | continue
      let .inductInfo _ ← getConstInfo name | continue
      if let some major ← projectionBase discr then
        let majorType ← whnf (← inferType (mkFVar major))
        let .const majorName _ := majorType.getAppFn | continue
        let .inductInfo _ ← getConstInfo majorName | continue
        let mut result := #[]
        let cases ← g.cases major
        record g (some major) cases
        for c in cases do
          result := result ++ (← visitCases c.mvarId f inputName ctx procs leaf requireBranch
            (branched || cases.size > 1) record)
        return result
    -- Computed tests stay in the branch callback, where ordinary source rules apply.
  if requireBranch && !branched then
    Search.unsupported "source calls: no runtime branch; repacking a structure cannot supply its \
      implementation"
  let out ← if out.isAppOfArity ``UniqueEncoding.encode 4 && (← isConstructorApp inspected) then
    pure (mkAppN out.getAppFn (out.getAppArgs.set! 3 inspected)) else pure out
  return #[← leaf g decl inputCode out]

private def caseEquations (g : MVarId) (f outputType outputInst : Lean.Expr)
    (decl : LocalDecl) (inputCode out : Lean.Expr)
    (ctx : Simp.Context) (procs : Simp.SimprocsArray) :
    MetaM (Lean.Expr × Lean.Expr × MVarId × Array Lean.Expr) := do
  let input := inputCode.appArg!
  let ri := (← simp inputCode ctx procs).1
  let output ← mkAppOptM ``encode
    #[some (mkConst ``Tree), some outputType, some outputInst, some out]
  let ro := (← simp output ctx procs).1
  let (hi, g) ← g.note `source_input_tree (← mkEqTrans (mkFVar decl.fvarId) (← ri.getProof))
  let (hc, g) ← (← g.assert `source_input_code (← mkEq inputCode ri.expr) (← ri.getProof)).intro1
  let sourceOutput ← mkAppOptM ``encode
    #[some (mkConst ``Tree), some outputType, some outputInst, some (mkApp f input)]
  let (ho, g) ← (← g.assert `source_output_tree
    (← mkEq sourceOutput ro.expr) (← ro.getProof)).intro1
  let g ← g.clear decl.fvarId
  return (ri.expr, ro.expr, g, #[mkFVar hi, mkFVar hc, mkFVar ho])

private def collectCases (g : MVarId) (f : Lean.Expr)
    (outputType outputInst : Lean.Expr) (inputName : Name)
    (ctx : Simp.Context) (procs : Simp.SimprocsArray)
    (record : MVarId → Option FVarId → Array CasesSubgoal → MetaM Unit) :
    MetaM (Array CompiledCase) :=
    visitCases g f inputName ctx procs (record := record) fun g decl inputCode out => do
  let sourceGoal := g
  let (input, output, g, _) ← caseEquations g f outputType outputInst decl inputCode out ctx procs
  let (tests, fields) := inputLayout input
  return ⟨tests, ← outputExpr output fields, g, sourceGoal, inputCode, out⟩

private inductive Dispatch (α : Type) where
  | leaf (a : α)
  | branch (test : TreeProgram.Expr Unit) (yes no : Dispatch α)

private partial def dispatchCases {α : Type}
    (choices : Array (List (List Bool × Bool) × α)) : MetaM (Dispatch α) := do
  let some first := choices[0]? | Search.unsupported "source cases: no inhabited input cases"
  if choices.size = 1 then return .leaf first.2
  for (path, _) in first.1 do
    let roots := choices.map fun c => c.1.lookup path
    if roots.all (·.isSome) && roots.contains (some true) && roots.contains (some false) then
      return .branch (projectInput path)
        (← dispatchCases (choices.filter fun c => c.1.lookup path == some true))
        (← dispatchCases (choices.filter fun c => c.1.lookup path == some false))
  Search.unsupported "source cases: branch layouts cannot be distinguished by their known roots"

private partial def exprSyntax (e : TreeProgram.Expr Unit) (v : Term) : TermElabM Term := do
  match e with
  | .nil => ``(TreeProgram.Expr.nil)
  | .var _ => ``(Value.expression $v)
  | .left e => ``(TreeProgram.Expr.left $(← exprSyntax e v))
  | .right e => ``(TreeProgram.Expr.right $(← exprSyntax e v))
  | .pair a b => ``(TreeProgram.Expr.pair $(← exprSyntax a v) $(← exprSyntax b v))

private partial def compileCommand (p : Dispatch (TreeProgram.Expr Unit)) (v n : Term) :
    TermElabM (Term × Nat) := do
  match p with
  | .leaf e => return (← ``(Cmd.assign $n $(← exprSyntax e v)), e.assignSteps)
  | .branch e yes no =>
    let (yes, a) ← compileCommand yes v n
    let (no, b) ← compileCommand no v n
    return (← ``(Cmd.branch $(← exprSyntax e v) $yes $no), e.steps + 1 + max a b)

private partial def evalExprSyntax (e : TreeProgram.Expr Unit) (input : Term) : TermElabM Term := do
  match e with
  | .nil => ``(Tree.nil)
  | .var _ => pure input
  | .left e => ``(Tree.left $(← evalExprSyntax e input))
  | .right e => ``(Tree.right $(← evalExprSyntax e input))
  | .pair a b => ``(Tree.pair $(← evalExprSyntax a input) $(← evalExprSyntax b input))

-- A fixed user budget may distinguish inputs taking different branches.
private partial def dispatchTime (p : Dispatch (TreeProgram.Expr Unit)) (input : Term) :
    TermElabM Term := do
  match p with
  | .leaf e => pure (quote e.assignSteps)
  | .branch e yes no =>
    let test ← evalExprSyntax e input
    let yes ← dispatchTime yes input
    let no ← dispatchTime no input
    ``($(quote (e.steps + 1)) + ite (Tree.root $test = true) $yes $no)

private structure CaseSplit where
  goal : MVarId
  major : Option FVarId
  branches : Array CasesSubgoal

-- Replay the recorded case eliminations without analyzing source functions or layouts again.
private def replayCases (splits : Array CaseSplit) (oldGoal newGoal : MVarId)
    (initial : FVarSubst) : MetaM (Std.HashMap MVarId (MVarId × FVarSubst)) := do
  let mut goals := ({} : Std.HashMap MVarId (MVarId × FVarSubst)).insert oldGoal (newGoal, initial)
  for split in splits do
    let some (goal, subst) := goals[split.goal]? | throwError "source calls: missing case goal"
    let some major := split.major | do
      unless ← closeImpossibleCase goal do
        throwError "source calls: an impossible branch became inhabited"
      continue
    let major := subst.get major
    unless major.isFVar do throwError "source calls: case variable became a computed value"
    let branches ← goal.cases major.fvarId!
    unless branches.size = split.branches.size do
      throwError "source calls: incompatible case elimination"
    for old in split.branches, next in branches do
      unless old.ctorName == next.ctorName && old.fields.size == next.fields.size do
        throwError "source calls: incompatible case constructor"
      let mut translated := subst.append next.subst
      for field in old.fields, value in next.fields do
        if field.isFVar then translated := translated.insert field.fvarId! value
      let context := (← next.mvarId.getDecl).lctx
      translated := old.subst.map.foldl (init := translated) fun translated id value =>
        let mapped := next.subst.apply (subst.get id)
        -- Intermediate case variables and budget-only proofs have no replayed counterpart.
        if value.isFVar && (collectFVars {} mapped).fvarIds.all context.contains then
          translated.insert value.fvarId! mapped
        else translated
      goals := goals.insert old.mvarId (next.mvarId, translated)
  return goals

private def sourceCases : TacticM Unit := withMainContext do
  let userGoal ← getMainGoal
  let rest := (← getGoals).tail
  let (args, requested) ← sourceGoalArgs userGoal
  let fixedBudget := !requested.isMVar
  let #[inputType, outputType, inputInst, outputInst, f] := args |
    throwError "source cases: invalid source arguments"
  if let .const name _ := f.eta.getAppFn then
    if ← isRecursiveDefinition name then
      Search.unsupported (Search.recursionMessage name)
  let bounds ← if fixedBudget then mkFreshExprMVar (← inferType requested) else pure requested
  let goal ← if fixedBudget then
    pure (← mkFreshExprSyntheticOpaqueMVar
      (← mkAppOptM ``Realizes ((args.map some).push (some bounds)))).mvarId!
    else pure userGoal
  setGoals [goal]
  let program ← mkFreshExprMVar (← mkArrow (mkConst ``Value)
    (← mkAppM ``Code #[mkConst ``Value]))
  let (certificate, finish) ← certifySourceGoal goal args program bounds
  setGoals [certificate]
  evalTactic (← `(tactic| constructor))
  let [freshGoal, correctGoal] ← getGoals | throwError "unexpected source goals"
  let inputName ← mkFreshUserName `source_input
  let (locals, correctGoal) ← correctGoal.introN 6 [`v, `n, `s, `x, `hv, inputName]
  let ctx ← mkSimpContext
    (← `(tactic| simp [encode_unit, encode_prod, List.ofFn_succ, sourcePair])) false
  let splits ← IO.mkRef (#[] : Array CaseSplit)
  let cases ← collectCases correctGoal f outputType outputInst inputName ctx.ctx ctx.simprocs
    (fun goal major branches => splits.modify (·.push ⟨goal, major, branches⟩))
  let command ← dispatchCases (cases.map fun c => (c.tests, c.result))
  let v := mkIdent (← mkFreshUserName `input)
  let n := mkIdent (← mkFreshUserName `next)
  let (body, time) ← compileCommand command v n
  program.mvarId!.assign (← Term.elabTerm
    (← `(fun $v => (⟨fun $n => (.var $n, $n + 1, [$body])⟩ : Code Value)))
    (some (← inferType program)))
  if bounds.isMVar then
    withLocalDeclD `x inputType fun x => do
      let input ← mkAppOptM ``encode
        #[some (mkConst ``Tree), some inputType, some inputInst, some x]
      let output ← mkAppOptM ``encode
        #[some (mkConst ``Tree), some outputType, some outputInst, some (mkApp f x)]
      let peak ← mkAppM ``max #[← mkAppM ``Tree.size #[input], ← mkAppM ``Tree.size #[output]]
      let time ← if fixedBudget then
        Term.elabTerm (← dispatchTime command (← Term.exprToSyntax input)) (some (mkConst ``Nat))
        else pure (mkNatLit time)
      let b ← mkAppM ``Bounds.mk #[← mkLambdaFVars #[x] time, ← mkLambdaFVars #[x] peak]
      unless ← isDefEq bounds b do throwError "source cases: cannot infer budgets"
  setGoals [freshGoal]
  evalTactic (← `(tactic| intro v n hv; exact ⟨Nat.le_succ _, le_rfl⟩))
  setGoals (cases.toList.map (·.goal))
  evalTactic (← `(tactic| all_goals
    (simp +contextual (disch := omega) [Code.Bounded, Code.block, *] <;> omega)))
  finish
  if fixedBudget then
    let proof ← instantiateMVars (mkMVar goal)
    let comparison ← withLocalDeclD `x inputType fun x => do
      let time ← mkAppM ``LE.le #[← mkAppM ``Bounds.time #[bounds, x],
        ← mkAppM ``Bounds.time #[requested, x]]
      let peak ← mkAppM ``LE.le #[← mkAppM ``Bounds.peak #[bounds, x],
        ← mkAppM ``Bounds.peak #[requested, x]]
      mkFreshExprSyntheticOpaqueMVar (← mkForallFVars #[x] (← mkAppM ``And #[time, peak]))
    userGoal.assign (← mkAppM ``Realizes.mono #[proof, comparison])
    let (x, root) ← comparison.mvarId!.intro1
    let (inputEq, root) ← root.withContext do
      let input ← mkAppOptM ``encode
        #[some (mkConst ``Tree), some inputType, some inputInst, some (mkFVar x)]
      root.note inputName (← mkEqRefl input)
    let replayed ← replayCases (← splits.get) correctGoal root
      (({} : FVarSubst).insert locals[3]! (mkFVar x) |>.insert locals[5]! (mkFVar inputEq))
    let obligations ← cases.mapM fun c => do
      let some (g, subst) := replayed[c.sourceGoal]? |
        throwError "source cases: missing budget branch"
      g.withContext do
        let some decl := (← getLCtx).findFromUserName? inputName |
          throwError "source cases: missing budget input"
        return (← caseEquations g f outputType outputInst decl (subst.apply c.inputCode)
          (subst.apply c.output) ctx.ctx ctx.simprocs).2.2.1
    setGoals obligations.toList
    let verification ← saveState
    try
      evalTactic (← `(tactic| all_goals
        (simp_all [sourcePair] <;> (repeat' apply And.intro) <;> omega)))
    catch ex =>
      let message ← match ex with
        | .error _ message => pure message
        | _ =>
          if isAbortTacticException ex then
            pure (MessageData.joinSep ((← Core.getMessageLog).toList.map (·.data)) "\n")
          else throw ex
      verification.restore
      throwError (.tagged `sourceBudgetFailure
        m!"source cases: could not verify the supplied budget\n{message}")
  setGoals ((← getGoals) ++ rest)

/-- Certify a finite source case split with structural branch results. -/
elab (name := sourceCasesTactic) "source_cases" : tactic => sourceCases

private def simplifyBudget (inputType outputType inputInst outputInst f : Lean.Expr) :
    TacticM Unit := do
  let (x, g) ← (← getMainGoal).intro1
  setGoals [g]
  let g ← g.withContext do
    let ctx ← mkSimpContext
      (← `(tactic| simp [encode_unit, encode_prod, List.ofFn_succ, sourcePair])) false
    let input ← mkAppOptM ``encode
      #[some (mkConst ``Tree), some inputType, some inputInst, some (mkFVar x)]
    let name ← mkFreshUserName `source_input
    let (_, g) ← g.note name (← mkEqRefl input)
    let cases ← visitCases g f name ctx.ctx ctx.simprocs fun g decl inputCode out => do
      return (← caseEquations g f outputType outputInst
        decl inputCode out ctx.ctx ctx.simprocs).2.2.1
    return cases.toList
  setGoals g
  evalTactic (← `(tactic| all_goals (simp_all [sourcePair] <;> (repeat' apply And.intro) <;>
    try omega)))

private structure Call where
  argument : TreeProgram.Expr Unit
  implementation : Lean.Expr
  bounds_eq : Lean.Expr

private structure CallCase where
  tests : List (List Bool × Bool)
  call : Call
  goal : MVarId
  value : Lean.Expr
  inputCode : Lean.Expr
  output : Lean.Expr
  cost : Lean.Expr

private partial def compileCalls (p : Dispatch Call) (v : Term) :
    TermElabM (Term × Term) := do
  match p with
  | .leaf c =>
    let h ← Term.exprToSyntax c.implementation
    let e ← exprSyntax c.argument v
    return (← `(($h).call $e), ← `(fun n => ($h).call_fresh $e n))
  | .branch e yes no =>
    let (yes, fresh) ← compileCalls yes v
    let (no, _) ← compileCalls no v
    let e ← exprSyntax e v
    return (← `((⟨fun n => (.var n,
      max (($yes).build n).2.1 (($no).build n).2.1,
      [Cmd.branch $e (Code.block (($yes).build n).2.2)
        (Code.block (($no).build n).2.2)])⟩ : Code Value)),
      ← ``(fun n => Nat.le_trans (($fresh) n) (Nat.le_max_left _ _)))

private def sourceCalls (certify : Lean.Expr → MetaM (Lean.Expr × Lean.Expr)) :
    TacticM Unit := withMainContext do
  trace[source.translation] "analyze call branches"
  let goal ← getMainGoal
  let rest := (← getGoals).tail
  let (args, bounds) ← sourceGoalArgs goal
  let #[inputType, outputType, inputInst, outputInst, f] := args |
    throwError "source calls: invalid source arguments"
  if let .const name _ := f.eta.getAppFn then
    if ← isRecursiveDefinition name then
      Search.unsupported (Search.recursionMessage name)
  unless bounds.isMVar do Search.unsupported "source calls: infer the branch budgets first"
  let outer ← getLCtx
  let outerInstances ← getLocalInstances
  let costs ← mkFreshExprMVar
    (← mkArrow inputType (← mkAppM ``Prod #[mkConst ``Nat, mkConst ``Nat]))
  let overhead ← mkFreshExprMVar (mkConst ``Nat)
  let (x, budgetGoal) ← costs.mvarId!.intro1
  let inputName ← mkFreshUserName `source_input
  let ctx ← mkSimpContext
    (← `(tactic| simp [encode_unit, encode_prod, List.ofFn_succ, sourcePair])) false
  let splits ← IO.mkRef (#[] : Array CaseSplit)
  let (budgetRoot, choices) ← budgetGoal.withContext do
    let input ← mkAppOptM ``encode
      #[some (mkConst ``Tree), some inputType, some inputInst, some (mkFVar x)]
    let (_, budgetGoal) ← budgetGoal.note inputName (← mkEqRefl input)
    let choices ← visitCases budgetGoal f inputName ctx.ctx ctx.simprocs (requireBranch := true)
      (record := fun goal major branches => splits.modify (·.push ⟨goal, major, branches⟩))
      fun g _ inputCode out => do
      let input := inputCode.appArg!
      let mut body := mkApp f input
      if out.isAppOfArity ``UniqueEncoding.encode 4 then
        let source ← whnf out.appArg!
        if ← isConstructorApp source then
          body := mkAppN out.getAppFn (out.getAppArgs.set! 3 source)
      let (branch, value) ← branchFunction outer body
      trace[source.translation] "certify branch callback"
      let (implementation, bounds_eq) ← withLCtx outer outerInstances (certify branch)
      let specification ← inferType implementation
      unless specification.isAppOfArity ``Implementation 5 do
        throwError "source calls: expected a certified implementation"
      let escapes := fun e : Lean.Expr =>
        (collectFVars {} e).fvarIds.any (!outer.contains ·)
      if escapes specification || escapes implementation then
        for e in #[specification, implementation] do
          for id in (collectFVars {} e).fvarSet do
            unless outer.contains id do
              trace[source.translation] "escaping variable: {mkFVar id} : {← inferType (mkFVar id)}"
        Search.unsupported "source calls: branch certificate depends on runtime data"
      let some (_, lhs, b) := (← inferType bounds_eq).eq? |
        throwError "source calls: expected a certified budget equation"
      unless ← isDefEq lhs (← mkAppM ``Implementation.bounds #[implementation]) do
        throwError "source calls: budget belongs to a different implementation"
      let ri := (← simp inputCode ctx.ctx ctx.simprocs).1
      trace[source.translation] "extract branch argument"
      let code ← mkAppM ``encode #[mkConst ``Tree, value]
      let rv := (← simp code ctx.ctx ctx.simprocs).1
      let (tests, fields) := inputLayout ri.expr
      let argument ← outputExpr rv.expr fields
      let time ← mkAppM ``Bounds.time #[b, value]
      let time ← mkAppM ``HAdd.hAdd #[time, ← mkAppM ``HAdd.hAdd #[overhead,
        mkNatLit (argument.assignSteps + 2)]]
      let peak ← mkAppM ``max #[← mkAppM ``Tree.size #[inputCode],
        ← mkAppM ``max #[← mkAppM ``Tree.size #[code], ← mkAppM ``Bounds.peak #[b, value]]]
      let cost ← mkAppM ``Prod.mk #[time, peak]
      g.assign cost
      return (⟨tests, ⟨argument, implementation, bounds_eq⟩, g, value,
        inputCode, out, cost⟩ : CallCase)
    return (budgetGoal, choices)
  -- Keep each closed implementation shared with the budgets that refer to it.
  let mut goal := goal
  let mut shared := #[]
  for branch in choices do
    let c := branch.call
    let some (_, _, budget) := (← inferType c.bounds_eq).eq? |
      throwError "source calls: expected a certified budget equation"
    let predicate ← withLocalDeclD `implementation (← inferType c.implementation) fun p => do
      mkLambdaFVars #[p] (← mkEq (← mkAppM ``Implementation.bounds #[p]) budget)
    let package ← mkAppOptM ``Subtype.mk
      #[none, some predicate, some c.implementation, some c.bounds_eq]
    let (h, next) ← goal.note (← mkFreshUserName `source_branch) package
    let (implementation, bounds_eq) ← next.withContext do
      return (← mkAppM ``Subtype.val #[mkFVar h], ← mkAppM ``Subtype.property #[mkFVar h])
    goal := next
    shared := shared.push { branch with
      call := { c with implementation, bounds_eq } }
  let choices := shared
  setGoals [goal]
  withMainContext do
    let tree ← dispatchCases (choices.map fun c => (c.tests, c.call))
    let v := mkIdent (← mkFreshUserName `input)
    let (body, fresh) ← compileCalls tree v
    let rec testTime : Dispatch Call → Nat
      | .leaf _ => 0
      | .branch e yes no => e.steps + 1 + max (testTime yes) (testTime no)
    overhead.mvarId!.assign (mkNatLit (testTime tree))
    let costs ← instantiateMVars costs
    withLocalDeclD `x inputType fun x => do
      let cost := mkApp costs x
      let b ← mkAppM ``Bounds.mk #[← mkLambdaFVars #[x] (← mkAppM ``Prod.fst #[cost]),
        ← mkLambdaFVars #[x] (← mkAppM ``Prod.snd #[cost])]
      unless ← isDefEq bounds b do throwError "source calls: cannot infer budgets"
    let program ← Term.elabTerm (← `(fun $v : Value => $body)) none
    let (certificate, finish) ← certifySourceGoal goal args program bounds
    setGoals [certificate]
    evalTactic (← `(tactic| constructor))
    let [freshGoal, correctGoal] ← getGoals | throwError "source calls: unexpected goals"
    setGoals [freshGoal]
    evalTactic (← `(tactic| intro $v n hv; exact ⟨(Nat.le_succ _).trans (($fresh) n), ($fresh) n⟩))
    let (locals, correctGoal) ← correctGoal.introN 6 [`v, `n, `s, `x, `hv, inputName]
    let replayed ← replayCases (← splits.get) budgetRoot correctGoal
      (({} : FVarSubst).insert x (mkFVar locals[3]!))
    let proofCases ← choices.mapM fun branch => do
      let some (g, subst) := replayed[branch.goal]? |
        throwError "source calls: missing branch proof"
      g.withContext do
        let inputCode := subst.apply branch.inputCode
        let decl ← (subst.get locals[5]!).fvarId!.getDecl
        trace[source.translation] "derive branch encoding equations"
        let (_, _, g, equations) ← caseEquations g f outputType outputInst decl inputCode
          (subst.apply branch.output) ctx.ctx ctx.simprocs
        let selected := subst.apply (← instantiateMVars branch.cost)
        let target ← instantiateMVars (← g.getType)
        unless target.isAppOfArity ``Code.Bounded 7 do
          throwError "source calls: expected a code verification goal"
        let target := mkAppN target.getAppFn
          (target.getAppArgs.set! 4 selected.getAppArgs[2]! |>.set! 5 selected.getAppArgs[3]!)
        let g ← g.replaceTargetDefEq target
        return (g, branch.call, subst.apply branch.value, selected.getAppArgs[3]!,
          inputCode, equations)
    for (g, c, value, space, inputCode, equations) in proofCases do
      setGoals [g]
      withMainContext do
        let v ← Term.exprToSyntax (mkFVar locals[0]!)
        let e ← exprSyntax c.argument v
        let h ← Term.exprToSyntax c.implementation
        let n ← Term.exprToSyntax (mkFVar locals[1]!)
        let s ← Term.exprToSyntax (mkFVar locals[2]!)
        let value ← Term.exprToSyntax value
        let space ← Term.exprToSyntax space
        let inputCode ← Term.exprToSyntax inputCode
        let boundsEq ← Term.exprToSyntax c.bounds_eq
        let some (_, _, budget) := (← inferType c.bounds_eq).eq? |
          throwError "source calls: expected a certified budget equation"
        let budget ← Term.exprToSyntax budget
        let outputEq ← Term.exprToSyntax equations[2]!
        let equations ← equations.mapM fun equation => do
          let term ← Term.exprToSyntax equation
          `(Lean.Parser.Tactic.simpLemma| $term:term)
        trace[source.translation] "verify compiled call branch"
        evalTactic (← `(tactic|
          (have source_call := ($h).call_bounded $e $n $s $value (space := $space)
            (b := $budget) (hbound := $boundsEq)
            (by simp [sourcePair, $equations,*] <;> rfl)
            (by
              apply le_trans (b := max ($inputCode).size (encode Tree $value).size)
              · simp [sourcePair, $equations,*] <;> omega
              · exact max_le_max le_rfl (Nat.le_max_left _ _))
            (by
              exact (Nat.le_max_right _ _).trans (Nat.le_max_right _ _))
          )))
        trace[source.translation] "simplify compiled call branch"
        if choices.size == 1 then
          let steps := quote c.argument.assignSteps
          evalTactic (← `(tactic|
            (have source_steps : ($e).assignSteps = $steps := by simp
             apply source_call.mono (by omega) le_rfl
             intro z t h
             refine ⟨Eq.trans ?_ ($outputEq).symm, h.2⟩
             first
             | exact h.1
             | simpa [encode_unit, encode_prod, List.ofFn_succ, sourcePair] using h.1)))
        else
          evalTactic (← `(tactic|
            (simp +contextual (disch := omega) [Code.Bounded, Code.block, sourcePair, $equations,*]
               at source_call ⊢
             all_goals (repeat' apply And.intro)
             all_goals (first |
               exact source_call.mono (by omega) le_rfl (fun _ h => h) | omega))))
      unless (← getGoals).isEmpty do throwError "source calls: failed to verify branch"
    finish
    setGoals rest

end FiniteCases

open Lean Meta in
private def normalizeSourceBounds (implementation : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  let some ext ← getSimpExtension? `source_bounds | throwError "missing source budget projections"
  let ctx ← Simp.mkContext (simpTheorems := #[← ext.getTheorems])
    (congrTheorems := ← getSimpCongrTheorems)
  let bounds ← mkAppM ``Implementation.bounds #[implementation]
  let (result, _) ← simp bounds ctx
  return (result.expr, ← result.getProof)

open Lean Meta Elab Tactic in
private def sourceCallsWith (query : Lean.Expr → MetaM (Option Lean.Expr)) : TacticM Unit :=
  FiniteCases.sourceCalls fun f => do
    let target ← mkAppM ``Implementation #[f]
    if let some implementation ← query target then
      let implementation ← instantiateMVars implementation
      let (_, equality) ← normalizeSourceBounds implementation
      return (implementation, equality)
    let bounds ← mkFreshExprMVar (← mkAppM ``Bounds #[target.getAppArgs[0]!])
    let legacy ← mkAppOptM ``Realizes ((target.getAppArgs.map some).push (some bounds))
    let some proof ← query legacy |
      Search.unsupported m!"source calls: no implementation for branch {f}"
    let args := ((← instantiateMVars legacy).getAppArgs.map some).push (some proof)
    return (← mkAppOptM ``Realizes.implementation args,
      ← mkAppOptM ``Realizes.bounds_implementation args)

open Lean Meta Mathlib.Meta.FunProp in
private def sourceQuery (search : Lean.Expr → FunPropM (Option Result))
    (context : Mathlib.Meta.FunProp.Context) (target : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let env ← getEnv
  let state : Mathlib.Meta.FunProp.State :=
    { morTheorems := morTheoremsExt.getState env,
      transitionTheorems := transitionTheoremsExt.getState env }
  let (result, _) ← (search target context).run state
  return result.map (·.proof)

open Lean Meta Mathlib.Meta.FunProp in
private def localSourceCertificate (unfolded : IO.Ref (Array Name × Bool))
    (goal : Lean.Expr) : FunPropM (Option Result) := do
  unless goal.isAppOfArity ``Implementation 5 || goal.isAppOfArity ``Realizes 6 do return none
  if goal.getAppArgs[4]!.hasExprMVar then return none
  let locals := (← getLCtx).foldl (fun ds d => d :: ds) []
  for decl in locals do
    if decl.kind == .auxDecl then continue
    let type ← instantiateMVars decl.type
    unless type.isAppOfArity ``Implementation 5 || type.isAppOfArity ``Realizes 6 do continue
    if let some result ← Search.attempt unfolded do
        let proof := decl.toExpr
        for (actual, expected) in (type.getAppArgs.extract 0 5).zip
            (goal.getAppArgs.extract 0 5) do
          unless ← withReducible (isDefEq actual expected) do return none
        if ← withReducible (isDefEq type goal) then return some ⟨proof⟩
        if goal.isAppOfArity ``Implementation 5 && type.isAppOfArity ``Realizes 6 then
          let args := (goal.getAppArgs.map some).push (some type.getAppArgs[5]!)
          unless ← withReducible (isDefEq type (← mkAppOptM ``Realizes args)) do return none
          return some ⟨← mkAppOptM ``Realizes.implementation (args.push (some proof))⟩
        if goal.isAppOfArity ``Realizes 6 && type.isAppOfArity ``Implementation 5 then
          let proof ← mkAppM ``Implementation.realizes #[proof]
          if ← withReducible (isDefEq (← inferType proof) goal) then return some ⟨proof⟩
        return none then
      return some result
  return none

open Lean Mathlib.Meta.FunProp in
private structure SourceRuleCandidates where
  target : Lean.Expr
  decl : FunPropDecl
  rules : Array FunctionTheorem

open Lean Meta Mathlib.Meta.FunProp in
private def legacySourceCandidates (target : Lean.Expr) (data : FunctionData) :
    FunPropM (Option SourceRuleCandidates) := do
  unless target.isAppOfArity ``Implementation 5 do return none
  let bounds ← mkFreshExprMVar (← mkAppM ``Bounds #[target.getAppArgs[0]!])
  let target ← mkAppOptM ``Realizes ((target.getAppArgs.map some).push (some bounds))
  let some (decl, _) ← getFunProp? target | return none
  return some ⟨target, decl, ← Search.functionTheorems decl data⟩

open Lean Meta Mathlib.Meta.FunProp in
private def adaptSourceCertificate (target certificate : Lean.Expr) (result : Result) :
    MetaM Result := do
  unless target.isAppOfArity ``Implementation 5 && certificate.isAppOfArity ``Realizes 6 do
    return result
  let args := ((← instantiateMVars certificate).getAppArgs.map some).push (some result.proof)
  return ⟨← mkAppOptM ``Realizes.implementation args⟩

open Lean Meta in
private def typedSourceImplementation (target implementation : Lean.Expr) : MetaM Lean.Expr := do
  unless target.isAppOfArity ``Implementation 5 do return implementation
  let actual ← inferType implementation
  if ← withReducible (isDefEq actual target) then return implementation
  unless ← withDefault (isDefEq actual target) do
    throwError "source translation: the implementation has a different source type or encoding"
  let source := actual.getAppArgs[4]!
  let desired := target.getAppArgs[4]!
  let equality ← typedSourceProof (← mkEq source desired) (← mkEqRefl source)
  mkAppM ``Implementation.congr #[implementation, equality]

open Lean Meta Elab Tactic Mathlib.Meta.FunProp in
private partial def sourceSearch (session : Search.Session) (nested : Bool)
    (ancestors : Array Lean.Expr) (goal : Lean.Expr) : FunPropM (Option Result) := do
  let unfolded := session.unfolded
  let goal ← instantiateMVars goal
  session.step
  trace[Meta.Tactic.fun_prop] "source step {← session.steps.get}: {goal}"
  if let some result ← localSourceCertificate unfolded goal then return some result
  if let some { proof? := some proof, .. } := (← get).cache.find? goal then
    return some ⟨proof⟩
  if (← get).failureCache.contains goal then return none
  -- Bounds are synthesized afresh on each call; compare the source function to detect cycles.
  let key := if goal.isAppOfArity ``Realizes 6 then
    mkAppN (mkConst ``Implementation goal.getAppFn.constLevels!) (goal.getAppArgs.extract 0 5)
    else goal
  if ancestors.contains key then return none
  let ancestors := ancestors.push key
  increaseSteps
  let restore ← Search.checkpoint unfolded
  let search := sourceSearch session true ancestors
  let context ← read
  -- A branch has a different local context: only fuel, path and diagnostics cross this boundary.
  let query := sourceQuery search context
  let structureWith (allowCalls : Bool) : FunPropM (Option Result) := Search.attempt unfolded do
    -- A speculative lambda rule may leave an unencodable function-valued result.
    -- Such a premise cannot be compiled structurally, but another candidate may apply.
    for encoder in goal.getAppArgs.extract 2 4 do
      let encoder ← instantiateMVars encoder
      if encoder.isMVar then
        let some encoderProof ← synthInstance? (← inferType encoder) | return none
        unless ← isDefEq encoder encoderProof do return none
    let solve : TacticM Unit := withMainContext do
      let goal ← getMainGoal
      let some proof ← query (← goal.getType) |
        Search.unsupported "source translation: dependent result has no implementation"
      goal.assign proof
      replaceMainGoal []
    let actions := if allowCalls then
      [FiniteCases.sourceCases, sourceDependent *> solve, sourceCallsWith query]
      else [FiniteCases.sourceCases]
    for action in actions do
      if let some proof ← session.discharge ancestors action goal then
        unless nested do unfolded.modify fun (names, _) => (names, true)
        return some ⟨proof⟩
    return none
  let structural := structureWith true
  let finish (result : Option Result) : FunPropM (Option Result) := do
    if let some r := result then
      let proof ← typedSourceImplementation (← instantiateMVars goal) (← instantiateMVars r.proof)
      return some (← cacheResult goal { r with proof })
    restore
    cacheFailure goal
    return none
  match goal with
  | .forallE .. =>
    return ← finish (← forallTelescope goal fun xs body => do
      let some proof ← query body | return none
      return some ⟨← mkLambdaFVars xs proof⟩)
  | .letE .. =>
    return ← finish (← letTelescope goal fun xs body => do
      let some proof ← query body | return none
      return some ⟨← mkLambdaFVars (generalizeNondepLet := false) xs proof⟩)
  | _ => pure ()
  let some (decl, f) ← getFunProp? goal | return ← finish none
  -- Encoding an unsupported source call is not an instruction to translate its encoder.
  let encodedCall ← lambdaTelescope f fun _ body => do
    unless body.isAppOfArity ``UniqueEncoding.encode 4 do return none
    let some name := body.appArg!.getAppFn.constName? | return none
    return if ← isRecursiveDefinition name then some name else none
  -- A runtime-dependent encoder is representation metadata, not another runtime argument.
  -- Expose its source constructor or case split before generic function decomposition.
  let dependentStructure ← lambdaTelescope f fun xs body => do
    unless body.isAppOfArity ``UniqueEncoding.encode 4 do return false
    unless xs.any (fun x => body.getAppArgs[1]!.containsFVar x.fvarId!) do return false
    let value ← whnf body.appArg!
    if ← isConstructorApp value then return true
    return !(← FiniteCases.caseDiscriminators value).isEmpty
  if dependentStructure then
    if let some result ← structural then return ← finish (some result)
  -- Rules recursively use this driver, including callbacks; no preliminary scan is needed.
  let data ← getFunctionData? f defaultUnfoldPred
  let result ← match data with
    | .lam f => Search.lambdaRules unfolded search decl .pi (goal.setArg decl.funArgId f)
    | .letE f => Search.letRule unfolded search decl (goal.setArg decl.funArgId f) f
    | .data d => withLCtx d.lctx d.insts do
      let target := goal.setArg decl.funArgId (← d.toExpr)
      if d.isIdentityFun then return ← Search.lambdaRules unfolded search decl .id target
      if d.isConstantFun then
        if let some r ← Search.lambdaRules unfolded search decl .const target then return some r
      let candidates : SourceRuleCandidates := ⟨target, decl, ← Search.functionTheorems decl d⟩
      let env ← getEnv
      let rules (candidate : SourceRuleCandidates) (fallback : Bool) :
          FunPropM (Option Result) := Search.attempt unfolded do
        let some result ← Search.functionRules unfolded search candidate.decl
          candidate.target d (candidate.rules.filter
            (fun rule => Search.isFallback env rule == fallback)) | return none
        return some (← adaptSourceCertificate target candidate.target result)
      -- This driver owns every stage; queries and certificate adapters do not schedule work.
      if let some r ← rules candidates false then return some r
      -- Query existential specifications only when a direct implementation did not apply.
      let legacy ← legacySourceCandidates target d
      if let some c := legacy then
        if let some r ← rules c false then return some r
        if c.rules.any (Search.isFallback env) then
          -- Reuse a stored field before adapting a table operation or reconstruction.
          -- Recursive structural calls here could reconstruct that same table prematurely.
          if let some r ← structureWith false then return some r
          if let some r ← rules c true then return some r
      if let some name := encodedCall then
        if let some r ← rules candidates true then return some r
        session.reject ancestors (Search.recursionMessage name) .specification (some name)
        return none
      -- Root constructors use their encoding equations; nested structural helpers remain atomic.
      if let .const name _ := d.fn then
        if !nested && (← getConstInfo name).isCtor then
          if let some r ← Search.transitionRules unfolded search target then return some r
      -- A nonmatching candidate must not block structural field extraction.
      if nested || !candidates.rules.isEmpty then
        if let some r ← structural then return some r
      -- Subcall specifications need structural decomposition before their fallback rules:
      -- otherwise lookup of a composite table can recursively request rebuilding that table.
      if let some r ← rules candidates true then return some r
      let decomposition ← d.decomposition
      if let .failed := decomposition then
        if ← d.args.anyM fun arg => do
            return (← inferType arg.expr).containsFVar d.mainVar.fvarId! then
          if let some r ← Search.attempt unfolded do
              let some (outer, inner) ← Environment.decomposition? (← d.toExpr) | return none
              Search.lambdaRules unfolded search decl .comp target (some (outer, inner)) then
            return some r
      if let some f ← d.unfoldHeadFVar? then
        return ← sourceSearch session nested ancestors (target.setArg decl.funArgId f)
      if let .const name _ := d.fn then
        if ← isRecursiveDefinition name then
          session.reject ancestors (Search.recursionMessage name) .specification (some name)
          return none
        unless (← getMatcherInfo? name).isSome do
          if let some body ← unfoldDefinition? (Mor.mkAppN d.fn d.args) then
            unfolded.modify (fun (names, structural) =>
              (if names.contains name then names else names.push name, structural))
            return ← sourceSearch session nested ancestors
              (target.setArg decl.funArgId (← mkLambdaFVars #[d.mainVar] body))
      if let .comp outer inner := decomposition then
        if let some r ← Search.lambdaRules unfolded search decl .comp target
            (some (outer, inner)) then
          return some r
      return none
  if result.isSome then return ← finish result
  restore
  return ← finish (← structural)

open Lean Meta Elab Tactic Mathlib.Meta.FunProp in
private def withSourceSpecs {α : Type} (action : TacticM α) : TacticM α := do
  pushScope
  try
    activateScoped `Complexity.TreeProgram.Source
    action
  finally
    popScope

open Lean Meta Elab Tactic Mathlib.Meta.FunProp in
private def sourceContext : MetaM Mathlib.Meta.FunProp.Context := do
  let tactic ← `(tactic| first | with_reducible assumption | infer_param | source_encoding)
  let config := { maxSteps := source.maxSteps.get (← getOptions) : Mathlib.Meta.FunProp.Config }
  return { disch := tacticToDischarge tactic, config }

open Lean Meta Elab Tactic Mathlib.Meta.FunProp in
private def proveSource : TacticM (Array Ident × Bool) := withSourceSpecs <| withMainContext do
  let goal ← getMainGoal
  let saved ← saveState
  let session ← Search.Session.create
  let unfolded := session.unfolded
  let context ← sourceContext
  try
    let target ← instantiateMVars (← goal.getType)
    let search : FunPropM (Option Result) := do
      -- Inferred budgets come from the chosen certified implementation. Fixed-budget
      -- specifications still use the same rules' existential compatibility interface.
      if target.isAppOfArity ``Realizes 6 && target.getAppArgs[5]!.isMVar then
        let certified ← mkAppOptM ``Implementation (target.getAppArgs.extract 0 5 |>.map some)
        if let some result ← Search.attempt unfolded do
            let some result ← sourceSearch session false #[] certified | return none
            let implementation ← instantiateMVars result.proof
            let (bounds, equality) ← normalizeSourceBounds implementation
            unless ← isDefEq target.getAppArgs[5]! bounds do return none
            let proof ← mkAppM ``Implementation.realizes #[implementation]
            let property ← withLocalDeclD `b (← mkAppM ``Bounds #[target.getAppArgs[0]!])
                fun b => do
                  mkLambdaFVars #[b] (← mkAppOptM ``Realizes
                    ((target.getAppArgs.extract 0 5 |>.map some).push (some b)))
            let proof ← mkEqMP (← mkCongrArg property equality) proof
            unless ← isDefEq (← inferType proof) target do return none
            return some ⟨proof⟩ then return some result
      sourceSearch session false #[] target
    let some proof ← sourceQuery (fun _ => search) context target | session.report
    goal.assign proof
    replaceMainGoal []
    let (names, structural) ← unfolded.get
    return (names.map mkIdent, structural)
  catch ex =>
    saved.restore
    throw ex

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| source_fun_prop) => discard proveSource

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| source_calls) => withSourceSpecs <| withMainContext do
    let session ← Search.Session.create
    let goal ← getMainGoal
    let target ← goal.getType
    let query := sourceQuery (sourceSearch session true #[target]) (← sourceContext)
    let some proof ← session.discharge #[target] (sourceCallsWith query) target | session.report
    goal.assign proof
    replaceMainGoal []

open Lean Elab Tactic in
/-- Translate a source function and reduce its model time-space bound to arithmetic goals. -/
elab (name := modelFunProp) "model_fun_prop" : tactic => do
  evalTactic (← `(tactic| apply Realizes.computableInTimeAndSpace))
  let args ← withMainContext do pure (← (← getMainGoal).getType).getAppArgs
  let (names, structural) ← proveSource
  if structural then
    FiniteCases.simplifyBudget args[0]! args[1]! args[2]! args[3]! args[4]!
  else
    let lemmas ← names.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $n:term)
    evalTactic (← `(tactic|
      (intro xs
       all_goals
         first
         | solve | dsimp only [$lemmas,*]; (repeat' apply And.intro) <;> omega
         | (simp_all [$lemmas,*] <;> (repeat' apply And.intro) <;>
             try (solve | (try simp_all [Complexity.Tree, Unit]) <;> omega)))))
  evalTactic (← `(tactic|
    all_goals try grind only [length_le_codeSize, usr size_encode_list_append,
      usr size_encode_reverse, size_encode_prod, Tree.size_pos, Nat.max_def]))


end Complexity.TreeProgram.Source
