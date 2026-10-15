/-
Copyright (c) 2024 Tomáš Skřivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomáš Skřivan, Yuyang Zhao
-/
module

public meta import Mathlib.Tactic.FunProp
public meta import Complexity.Tactic.TreeProgram.Attributes

/-!
Transactional candidate routing adapted from `Mathlib.Tactic.FunProp.Core`.
The theorem registry, source decomposition and theorem application remain mathlib's;
this layer makes failure rollback uniform inside the lambda and composition rule loops.
-/

public meta section

initialize Lean.registerTraceClass `source.translation

/-- Maximum source-search steps, shared by recursive branch translation. -/
register_option source.maxSteps : Nat := {
  defValue := 100000
  descr := "maximum number of source translation search steps, including branch callbacks"
}

namespace Complexity.TreeProgram.Source.Search
open Lean Meta Mathlib.Meta.FunProp

/-- An expected unsupported source form, as opposed to an elaboration or implementation error. -/
def unsupported {m : Type → Type} {α : Type} [Monad m] [MonadError m]
    (message : MessageData) : m α :=
  Lean.throwError (.tagged `sourceCandidateFailure message)

def recursionMessage (name : Name) : MessageData :=
  m!"source translation: `{privateToUserName name}` needs a registered implementation \
    (choose replacement source with `via`, or register a function equality with `[source]`)"

/-- Which part of a candidate could not be certified. -/
inductive FailureStage where
  | structure
  | specification
  deriving BEq

/-- A rejected candidate retains its source path independently of message formatting. -/
structure Failure where
  stage : FailureStage
  sourcePath : Array MessageData
  declaration : Option Name
  message : MessageData

/-- One user request shares fuel and diagnostics, but not caches across local contexts. -/
structure Session where
  /-- Successfully unfolded definitions and whether structural compilation was used. -/
  unfolded : IO.Ref (Array Name × Bool)
  /-- Attempts are charged even when their metavariable state is rolled back. -/
  steps : IO.Ref Nat
  /-- The most informative unsuccessful subgoal and its source path. -/
  failure : IO.Ref (Option Failure)
  /-- The limit is read once at the outer entry. -/
  maxSteps : Nat

/-- Start one translation request. -/
def Session.create : MetaM Session :=
  return ⟨← IO.mkRef (#[], false), ← IO.mkRef 0, ← IO.mkRef none,
    source.maxSteps.get (← getOptions)⟩

/-- Charge a source subgoal. This failure must not be treated as a rejected candidate. -/
def Session.step (session : Session) : MetaM Unit := do
  let steps ← session.steps.get
  if steps ≥ session.maxSteps then
    throwError "source translation: maximum number ({session.maxSteps}) of search steps exceeded"
  session.steps.set (steps + 1)

/-- Keep a missing-specification diagnostic in preference to a structural fallback rejection. -/
def Session.reject (session : Session) (path : Array Expr) (message : MessageData)
    (stage := FailureStage.structure) (declaration : Option Name := none) : MetaM Unit := do
  if let some previous ← session.failure.get then
    if previous.stage == .specification || stage != .specification then return
  let path ← path.mapM fun goal =>
    addMessageContext (MessageData.ofExpr (goal.getAppArgs[4]?.getD goal))
  session.failure.set (some ⟨stage, path, declaration, ← addMessageContext message⟩)

/-- Report the remembered reason only after all candidates have failed. -/
def Session.report {α : Type} (session : Session) : MetaM α := do
  let some failure ← session.failure.get |
    throwError "source translation: no uniform implementation found"
  let path := failure.sourcePath
  let message := if path.size ≤ 1 then failure.message else
    m!"{failure.message}\nsource path: {MessageData.joinSep path.toList " → "}"
  throwError message

/-- Run a structural proof attempt, catching only explicitly unsupported source forms. -/
def Session.discharge (session : Session) (path : Array Expr)
    (action : Elab.Tactic.TacticM Unit) (target : Expr) : MetaM (Option Expr) := do
  let saved ← saveState
  let unfolded ← session.unfolded.get
  let restore : MetaM Unit := do
    saved.restore
    session.unfolded.set unfolded
  try
    let goal ← mkFreshExprSyntheticOpaqueMVar target
    let run : Elab.TermElabM Unit := Elab.Term.withSynthesize (postpone := .no) do
      discard <| Elab.Tactic.run goal.mvarId! (action *> Elab.Tactic.pruneSolvedGoals)
    discard <| run.run {} {}
    let proof ← instantiateMVars goal
    if proof.hasExprMVar || proof.hasSorry then
      trace[source.translation] "unfinished structural certificate: \
        metavariables={proof.hasExprMVar}, sorry={proof.hasSorry}"
      for mvar in ← getMVars proof do
        trace[source.translation] "remaining obligation: {← mvar.getType}"
      restore
      return none
    return some proof
  catch ex =>
    restore
    if ex.toMessageData.kind == `sourceCandidateFailure then
      trace[source.translation] "rejected structure: {ex.toMessageData}"
      session.reject path ex.toMessageData
      return none
    throw ex

/-- Restore failed attempts without refunding their search steps. -/
def checkpoint (unfolded : IO.Ref (Array Name × Bool)) : FunPropM (FunPropM Unit) := do
  let saved ← Meta.saveState
  let state ← get
  let names ← unfolded.get
  return do
    let numSteps := (← get).numSteps
    saved.restore
    set { state with numSteps }
    unfolded.set names

/-- Run a candidate, restoring search and metavariable state if it fails. -/
def attempt (unfolded : IO.Ref (Array Name × Bool))
    (action : FunPropM (Option Result)) : FunPropM (Option Result) := do
  let restore ← checkpoint unfolded
  try
    let result ← action
    if result.isNone then restore
    return result
  catch ex =>
    restore
    throw ex

variable (unfolded : IO.Ref (Array Name × Bool))
  (search : Expr → FunPropM (Option Result))

/-- Query candidates without choosing a translation stage. Local certificates come first;
registered priorities retain mathlib's specificity order for ties. -/
def functionTheorems (decl : FunPropDecl) (data : FunctionData) :
    FunPropM (Array FunctionTheorem) := do
  let locals ← getLocalTheorems decl data.getFnOrigin data.mainArgs data.args.size
  let globals ← match data.fn with
    | .const name _ => getDeclTheorems decl name data.mainArgs data.args.size
    | _ => pure #[]
  return locals ++ (globals.toList.mergeSort (fun a b => a.priority ≥ b.priority)).toArray

/-- A rule's purpose is independent of its numerical priority. -/
def isFallback (env : Environment) (rule : FunctionTheorem) : Bool :=
  match rule.thmOrigin with
  | .decl name => (sourceFallbackAttr.getState env).contains name
  | .fvar _ => false

/-- Mathlib supplies rule indexing and theorem application; only attempts are transactional. -/
def lambdaRules (decl : FunPropDecl) (kind : LambdaTheoremType) (goal : Expr)
    (functions : Option (Expr × Expr) := none) : FunPropM (Option Result) := do
  let saved := sourceSavedImplementationExt.getState (← getEnv)
  let thms ← getLambdaTheorems decl.funPropName kind
  let thms := thms.filter (fun thm => saved.contains thm.thmName) ++
    thms.filter (fun thm => !saved.contains thm.thmName)
  for thm in thms do
    let hints ← match thm.thmArgs, functions with
      | .comp i j, some (f, g) => pure #[(i, f), (j, g)]
      | .comp .., none => throwError "missing composition arguments"
      | _, _ => pure #[]
    if let some result ← attempt unfolded <|
        tryTheoremWithHint? goal (.decl thm.thmName) hints search then
      return some result
  return none

private def generalRules (goal : Expr) (thms : Array GeneralTheorem) :
    FunPropM (Option Result) := do
  for thm in thms do
    if let some result ← attempt unfolded <| tryTheorem? goal (.decl thm.thmName) search then
      return some result
  return none

/-- Try indexed transition rules within the transition-depth limit. -/
def transitionRules (goal : Expr) : FunPropM (Option Result) :=
  withIncreasedTransitionDepth do
    generalRules unfolded search goal (← getTransitionTheorems goal)

private def removeArg (decl : FunPropDecl) (goal : Expr) (data : FunctionData) :
    FunPropM (Option Result) := do
  let some last := data.args.back? | return none
  if last.coe.isSome then
    if let some result ← generalRules unfolded search goal (← getMorphismTheorems goal) then
      return some result
    match ← data.isMorApplication with
    | .underApplied => return ← lambdaRules unfolded search decl .pi goal
    | .exact => return none
    | .none => throwError "invalid morphism application"
    | .overApplied => pure ()
  let .comp f g ← data.peeloffArgDecomposition | return none
  lambdaRules unfolded search decl .comp goal (some (f, g))

/-- The small routing part of mathlib's `tryTheorems`, using transactional lambda rules. -/
def functionRules (decl : FunPropDecl) (goal : Expr) (data : FunctionData)
    (thms : Array FunctionTheorem) : FunPropM (Option Result) := do
  for thm in thms do
    let result ← attempt unfolded do
      match compare thm.appliedArgs data.args.size with
      | .lt => removeArg unfolded search decl goal data
      | .gt => lambdaRules unfolded search decl .pi goal
      | .eq =>
        if thm.form == .comp then return ← tryTheorem? goal thm.thmOrigin search
        let parts ← if thm.mainArgs.size == data.mainArgs.size then do
            match ← data.decomposition with
            | .comp f g => pure (some (f, g))
            | _ => return ← tryTheorem? goal thm.thmOrigin search
          else data.decompositionOverArgs thm.mainArgs
        let some (f, g) := parts | return none
        lambdaRules unfolded search decl .comp goal (some (f, g))
    if result.isSome then return result
  return none

/-- Preserve mathlib's shared-let decomposition while routing composition through one policy. -/
def letRule (decl : FunPropDecl) (goal fn : Expr) : FunPropM (Option Result) := do
  let .lam xName xType (.letE yName yType yValue yBody _) xBi := fn |
    throwError "expected a source let"
  let yType := yType.consumeMData.headBeta
  let yValue := yValue.consumeMData
  let yBody := yBody.consumeMData
  if yType.hasLooseBVar 0 then return none
  if !yValue.hasLooseBVar 0 then
    return ← search <| mkLet yName yType yValue <|
      goal.setArg decl.funArgId (.lam xName xType (yBody.swapBVars 0 1) xBi)
  if !yBody.hasLooseBVar 0 then
    return ← search <| goal.setArg decl.funArgId <|
      .lam xName xType (yBody.lowerLooseBVars 1 1) xBi
  let (f, g) ← if yBody.hasLooseBVar 1 then do
      let f ← mkUncurryFun 2 (.lam xName xType (.lam yName yType yBody default) xBi)
      let g := .lam xName xType
        (mkAppN (← mkConstWithFreshMVarLevels ``Prod.mk) #[xType, yType, .bvar 0, yValue]) default
      pure (f, g)
    else pure (.lam yName yType yBody default, .lam xName xType yValue default)
  lambdaRules unfolded search decl .comp goal (some (f, g))

end Complexity.TreeProgram.Source.Search
