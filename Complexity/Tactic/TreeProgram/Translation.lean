/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Tactic.TreeProgram.Rules
public import Complexity.Tactic.TreeProgram.Recursion
public meta import Complexity.Tactic.TreeProgram.Search
public meta import Complexity.Tactic.TreeProgram.Environment
public import Complexity.Models.TreeMachine.Language.Derive
public meta import Complexity.Models.TreeMachine.Language.Semantics
public import Complexity.Resources.TreeMachine.Program
public import Complexity.Classes.Functions.Basic
public import Complexity.Encoding.TreeSize
public meta import Lean.Meta.Match.MatcherApp.Basic
public meta import Lean.Meta.RecExt

/-! # Certified translation of Lean source functions -/

@[expose] public section

open Complexity TreeProgram

namespace Complexity.TreeProgram.Source

/-- Compile a fixed source program with budgets indexed by its actual input. -/
theorem Implements.computableWithin {α β : Type*}
    [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {p : Value → Code Value} {f : α → β} {b : Bounds α} {time space : α → ℕ}
    (hp : Implements p f b)
    (hb : ∀ x, b.time x + 4 ≤ time x ∧ max ⌜x⌝ₜ.size (b.peak x) + 2 ≤ space x) :
    TimeSpaceModel.tree.ComputableWithin f time
      (fun x => (p .input).registers * space x) := by
  refine ⟨_, ⟨(p .input).registers, inferInstance, _, inferInstance,
    (p .input).compile, rfl⟩, ?_⟩
  apply Encoding.Computes.iff_of_uniqueEncoding.mpr
  intro x
  have hr := (hp.2 .input 1 (Function.update (fun _ => Tree.nil) 0 ⌜x⌝ₜ) x
    le_rfl (by simp)).mono le_rfl (Nat.le_max_right ⌜x⌝ₜ.size _) (fun _ _ h => h.1)
  exact (hr.compile (Nat.le_max_left _ _)).mono (hb x).1
    (Nat.mul_le_mul_left _ (hb x).2)

/-- Keep loading, controller and peak costs when hiding the fixed machine's register factor. -/
theorem Implementation.HasGrowth.computableWithGrowth {α β : Type*}
    [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {f : α → β} {hf : Implementation f} {t p : α → ℕ} (h : hf.HasGrowth t p) :
    TimeSpaceModel.tree.ComputableWithGrowth f (fun x => t x + 4)
      (fun x => max ⌜x⌝ₜ.size (p x) + 2) := by
  refine ⟨fun x => hf.bounds.time x + 4,
    fun x => (hf.program .input).registers * (max ⌜x⌝ₜ.size (hf.bounds.peak x) + 2),
    hf.implements.computableWithin (fun _ => ⟨le_rfl, le_rfl⟩),
    h.1.add (Dominated.refl _), ?_⟩
  exact (((Dominated.refl _).max h.2).add (Dominated.refl _)).const_mul_left _

/-- Compare the input budgets at the machine boundary, retaining the original source
specification for later calls. Loading and storage overheads remain explicit. -/
theorem Implementation.HasGrowth.computableWithGrowth_of_dominated {α β : Type*}
    [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {f : α → β} {hf : Implementation f} {t p T S : α → ℕ} (h : hf.HasGrowth t p)
    (ht : Dominated (fun x => t x + 4) T)
    (hp : Dominated (fun x => max ⌜x⌝ₜ.size (p x) + 2) S) :
    TimeSpaceModel.tree.ComputableWithGrowth f T S :=
  h.computableWithGrowth.mono ht hp

end Complexity.TreeProgram.Source

namespace Complexity

namespace TreeProgram.Source.Implementation

variable {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
  {f : α → β} {T S : ℕ → ℕ}

theorem HasGrowth.mem_ftisp {hf : Implementation f}
    (h : hf.HasGrowth (fun x => T ⌜x⌝ₜ.size) (fun x => S ⌜x⌝ₜ.size))
    (input : Dominated (fun x : α => ⌜x⌝ₜ.size) (fun x => S ⌜x⌝ₜ.size))
    (time_overhead : Dominated (fun _ : α => 4) (fun x => T ⌜x⌝ₜ.size))
    (space_overhead : Dominated (fun _ : α => 2) (fun x => S ⌜x⌝ₜ.size)) :
    f ∈ FTISP .tree T S :=
  (h.computableWithGrowth_of_dominated
    ((Dominated.refl _).add_same time_overhead)
    ((input.max_same (Dominated.refl _)).add_same space_overhead)).mem_ftisp

/-- A calculated structural budget may be compared at the model boundary without
exposing the coefficients of its saved calls. Local model overheads remain explicit. -/
theorem HasGrowth.mem_ftisp_of_dominated {hf : Implementation f} {t p : α → ℕ}
    (h : hf.HasGrowth t p)
    (ht : Dominated (fun x => t x + 4) (fun x => T ⌜x⌝ₜ.size))
    (hp : Dominated (fun x => max ⌜x⌝ₜ.size (p x) + 2) (fun x => S ⌜x⌝ₜ.size)) :
    f ∈ FTISP .tree T S :=
  (h.computableWithGrowth_of_dominated ht hp).mem_ftisp

/-- Exact-size envelopes are used only where an eventual scale comparison is required.
This permits finite input types to inhabit a zero eventual class without weakening their
all-input program or machine specifications. -/
theorem HasGrowth.mem_ftisp_of_sizeEnvelope {hf : Implementation f} {t p : α → ℕ}
    (h : hf.HasGrowth t p)
    (ht : DominatedAtTop (sizeEnvelope (fun x => t x + 4)) T)
    (hp : DominatedAtTop (sizeEnvelope (fun x => max ⌜x⌝ₜ.size (p x) + 2)) S) :
    f ∈ FTISP .tree T S := by
  have hm := h.computableWithGrowth.mono
    (Dominated.of_le (le_sizeEnvelope (fun x => t x + 4)))
    (Dominated.of_le (le_sizeEnvelope (fun x => max ⌜x⌝ₜ.size (p x) + 2)))
  exact FTISP.mono ht hp hm.mem_ftisp

/-- The usual positive powers of encoding size absorb the model's input storage,
fixed controller overheads and fixed register factor. -/
theorem HasGrowth.mem_ftisp_pow {hf : Implementation f} {t s : ℕ}
    (h : hf.HasGrowth (fun x => ⌜x⌝ₜ.size ^ t) (fun x => ⌜x⌝ₜ.size ^ s))
    (hs : 0 < s) : f ∈ FTISP .tree (fun n => n ^ t) (fun n => n ^ s) := by
  apply h.mem_ftisp
  · exact (Dominated.of_le fun x => Nat.le_self_pow (by omega) _)
  · exact (Dominated.const_of_pos 4 (fun x => Nat.pow_pos (Tree.size_pos ⌜x⌝ₜ)))
  · exact (Dominated.const_of_pos 2 (fun x => Nat.pow_pos (Tree.size_pos ⌜x⌝ₜ)))

end TreeProgram.Source.Implementation

end Complexity

end

public meta section

set_option linter.style.longFile 1800

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
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOfArity ``Implementation 5 do
    throwError "source translation: expected Implementation, got {target}"
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
    goal.assign implementation)
open Lean Meta Elab Tactic in
private def sourceDependent : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let (args, _) ← sourceGoalArgs goal
  let #[input, output, inputInst, outputInst, f] := args |
    throwError "source dependent: invalid source arguments"
  let (g, proof) ← withLocalDeclD `x input fun x => do
    let lhs ← mkAppM ``encode #[mkConst ``Tree, mkApp f x]
    let (code, proof) ← structuralResult x.fvarId! lhs true
    let proof ← typedSourceProof (← mkEq lhs code) proof
    return (← mkLambdaFVars #[x] code.appArg!, ← mkLambdaFVars #[x] proof)
  let next ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``Implementation #[g])
  goal.assign (← mkAppOptM ``Implementation.ofEncode #[some input, some output, none,
    some inputInst, some outputInst, none, some f, some g, some proof, some next])
  replaceMainGoal [next.mvarId!]

/-- Reinterpret a dependent source result through its structural encoding. -/
elab (name := sourceDependentTactic) "source_dependent" : tactic => sourceDependent

/-- Certify source branches with previously registered function implementations. -/
syntax (name := sourceCalls) "source_calls" : tactic
/-- Compose source-function specifications and synthesize their resource budget.
`using ns` activates the namespace's scoped rules for this translation and its callbacks. -/
syntax (name := sourceFunProp) "source_fun_prop" (" using " ident)?
  (" via " term)? : tactic

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
  if e.isConstOf ``Tree.nil || e.isAppOfArity ``BinaryTree.nil 1 then ([(path, false)], [])
  else if e.isAppOfArity ``Tree.pair 2 then
    let (ls, lf) := inputLayout e.getAppArgs[0]! (path ++ [false])
    let (rs, rf) := inputLayout e.getAppArgs[1]! (path ++ [true])
    ((path, true) :: ls ++ rs, lf ++ rf)
  else ([], [(e, path)])

private partial def outputExpr (e : Lean.Expr) (fields : List (Lean.Expr × List Bool)) :
    MetaM (TreeProgram.Expr Unit) := do
  if e.isConstOf ``Tree.nil || e.isAppOfArity ``BinaryTree.nil 1 then return .nil
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
  let goal ← getMainGoal
  let rest := (← getGoals).tail
  let (args, bounds) ← sourceGoalArgs goal
  let #[inputType, outputType, inputInst, outputInst, f] := args |
    throwError "source cases: invalid source arguments"
  if let .const name _ := f.eta.getAppFn then
    if ← isRecursiveDefinition name then
      Search.unsupported (Search.recursionMessage name)
  let program ← mkFreshExprMVar (← mkArrow (mkConst ``Value)
    (← mkAppM ``Code #[mkConst ``Value]))
  let (certificate, finish) ← certifySourceGoal goal args program bounds
  setGoals [certificate]
  evalTactic (← `(tactic| constructor))
  let [freshGoal, correctGoal] ← getGoals | throwError "unexpected source goals"
  let inputName ← mkFreshUserName `source_input
  let (_, correctGoal) ← correctGoal.introN 6 [`v, `n, `s, `x, `hv, inputName]
  let ctx ← mkSimpContext
    (← `(tactic| simp [encode_unit, encode_prod, List.ofFn_succ, sourcePair])) false
  let cases ← collectCases correctGoal f outputType outputInst inputName ctx.ctx ctx.simprocs
    (fun _ _ _ => pure ())
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
      let time := mkNatLit time
      let b ← mkAppM ``Bounds.mk #[← mkLambdaFVars #[x] time, ← mkLambdaFVars #[x] peak]
      unless ← isDefEq bounds b do throwError "source cases: cannot infer budgets"
  setGoals [freshGoal]
  evalTactic (← `(tactic| intro v n hv; exact ⟨Nat.le_succ _, le_rfl⟩))
  setGoals (cases.toList.map (·.goal))
  evalTactic (← `(tactic| all_goals
    (simp +contextual (disch := omega) [Code.Bounded, Code.block, sourcePair, *] <;> omega)))
  finish
  setGoals ((← getGoals) ++ rest)

/-- Certify a finite source case split with structural branch results. -/
elab (name := sourceCasesTactic) "source_cases" : tactic => sourceCases

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
      unless ← isDefEq bounds b do
        Search.unsupported "source calls: generated budgets do not match the requested budgets"
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
        -- Use the concrete encoding equations already obtained for this branch. Matching
        -- the generic injection projection here can launch an expensive inverse-law discharge.
        evalTactic (← `(tactic|
          (have source_call := ($h).call_bounded $e $n $s $value (space := $space)
            (b := $budget) (hbound := $boundsEq)
            (by simp [-UniqueEncoding.ofLeftInjection_encode, -sup_of_le_left, -sup_of_le_right,
              -Nat.max_eq_left, -Nat.max_eq_right, sourcePair, $equations,*] <;> rfl)
            (by
              apply le_trans (b := max ($inputCode).size (encode Tree $value).size)
              · simp [-UniqueEncoding.ofLeftInjection_encode, -sup_of_le_left, -sup_of_le_right,
                  -Nat.max_eq_left, -Nat.max_eq_right, sourcePair, $equations,*] <;> omega
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
            (simp +contextual (disch := omega)
               [-UniqueEncoding.ofLeftInjection_encode, -sup_of_le_left, -sup_of_le_right,
                 -Nat.max_eq_left, -Nat.max_eq_right, Code.Bounded, Code.block, sourcePair,
                 $equations,*]
               at source_call ⊢
             all_goals (repeat' apply And.intro)
             all_goals (first |
               exact source_call.mono (by omega) le_rfl (fun _ h => h) | omega))))
      unless (← getGoals).isEmpty do throwError "source calls: failed to verify branch"
    finish
    setGoals rest

end FiniteCases
open Lean Meta Elab Tactic in
/-- Read a saved specification for this implementation; this never searches for a program. -/
private def savedSourceGrowth? (implementation : Lean.Expr) (preserveImplementation := true)
    : MetaM (Option Lean.Expr) := withoutExporting do
  let locals ← (← getLCtx).foldlM (init := #[]) fun proofs declaration => do
    if declaration.isImplementationDetail then return proofs
    let type := declaration.type
    if type.isAppOfArity ``Implementation.HasGrowth 8 then
      return proofs.push declaration.toExpr
    return proofs
  let specs := sourceGrowthExt.getState (← getEnv)
  -- Read the declaration first; only follow an alias when it has no saved specification.
  let mut rhs := implementation
  for _ in [:8] do
    let candidate ← match rhs.getAppFn with
      | .const name _ =>
        match specs[name]? with
        | some (some theoremName) => some <$> mkConstWithFreshMVarLevels theoremName
        | some none => throwError "source budget: conflicting imported specifications for {name}"
        | none => pure none
      | .fvar id =>
        let matching ← locals.filterM fun proof => do
          return (← inferType proof).getAppArgs[5]!.getAppFn == .fvar id
        if matching.size > 1 then
          throwError "source budget: callback {rhs} has multiple uniform specifications; \
            supply one callback specification and weaken it with mono"
        pure matching[0]?
      | _ => pure none
    if let some candidate := candidate then
      let (parameters, _, conclusion) ← forallMetaTelescope (← inferType candidate)
      unless ← withDefault <| isDefEq conclusion.getAppArgs[5]! rhs do
        throwError "source budget: the registered specification does not match {rhs}"
      let proof ← instantiateMVars (mkAppN candidate parameters)
      let allowed ← getMVars implementation
      if (← getMVars proof).any (!allowed.contains ·) then
        throwError "source budget: the registered specification has unresolved parameters"
      let type ← inferType proof
      let selected := type.getAppArgs[5]!
      if !preserveImplementation || selected == implementation then return some proof
      let eq ← mkAuxTheorem (← mkEq implementation selected) (← mkEqRefl implementation)
      let property ← withLocalDeclD `hf (← inferType selected) fun hf =>
        mkLambdaFVars #[hf] (type.setArg 5 hf)
      return some (← mkEqMPR (← mkCongrArg property eq) proof)
    if rhs.isAppOf ``Implementation.ofImplements || rhs.isAppOf ``Implementation.mk then break
    let some expanded ← unfoldDefinition? rhs (ignoreTransparency := true) | break
    rhs := expanded.headBeta
  return none
open Lean Meta in
private def implementationOfBounds? (e : Lean.Expr) : Option Lean.Expr := do
  if e.isAppOfArity ``Implementation.bounds 6 then return e.appArg!
  if let .proj ``Bounds _ b := e.getAppFn then
    if b.isAppOfArity ``Implementation.bounds 6 then return b.appArg!
  if e.isAppOf ``Bounds.time || e.isAppOf ``Bounds.peak then
    let b ← e.getAppArgs[1]?
    if b.isAppOfArity ``Implementation.bounds 6 then return b.appArg!
  none
open Lean Meta in
def normalizeSourceBounds (implementation : Lean.Expr) (expandFields := false) :
    MetaM (Lean.Expr × Lean.Expr) := do
  let some ext ← getSimpExtension? `source_bounds | throwError "missing source budget projections"
  -- Keep budget equalities explicit: kernel conversion through a composed evaluator
  -- can be much more expensive than checking its projection theorem.
  let ctx ← Simp.mkContext (config := { implicitDefEqProofs := false, zetaDelta := true })
    (simpTheorems := #[← ext.getTheorems])
    (congrTheorems := ← getSimpCongrTheorems)
  let bounds ← mkAppM ``Implementation.bounds #[implementation]
  let methods := Simp.mkDefaultMethodsCore #[]
  let methods := { methods with pre := fun e => do
    if let some hf := implementationOfBounds? e then
      if let some growth ← savedSourceGrowth? hf false then
        let selected := (← inferType growth).getAppArgs[5]!
        let some oldBounds := e.find? (fun b =>
          b.isAppOfArity ``Implementation.bounds 6 && b.appArg! == hf) |
          return .done { expr := e }
        let newBounds ← mkAppM ``Implementation.bounds #[selected]
        if oldBounds == newBounds then return .done { expr := e }
        let equation ← mkAuxTheorem (← mkEq hf selected) (← mkEqRefl hf)
        let projection ← withLocalDeclD `hf (← inferType hf) fun h =>
          mkLambdaFVars #[h] (oldBounds.setArg 5 h)
        let boundsEq ← mkAuxTheorem (← mkEq oldBounds newBounds)
          (← mkCongrArg projection equation)
        let property ← withLocalDeclD `budget (← inferType oldBounds) fun b =>
          mkLambdaFVars #[b] (e.replace fun part => if part == oldBounds then some b else none)
        let expr := e.replace fun part => if part == oldBounds then some newBounds else none
        return .done { expr, proof? := some (← mkCongrArg property boundsEq) }
    if e.isAppOfArity ``Implementation.bounds 6 &&
        e.appArg!.isAppOf ``Recursion.implementation then
      -- Instantiate the dependent callback parameters from the chosen implementation.
      -- Simp's higher-order matcher need not recover them from its encoded result type.
      let hf := e.appArg!
      let proof := mkAppN (mkConst ``Recursion.bounds_implementation
        hf.getAppFn.constLevels!) hf.getAppArgs
      return .visit { expr := (← inferType proof).appArg!, proof? := some proof }
    let step ← methods.pre e
    if e.isAppOfArity ``Implementation.bounds 6 then
      if let .continue none := step then
        if let some expanded ← unfoldDefinition? e.appArg! (ignoreTransparency := true) then
          let equation ← mkAuxTheorem (← mkEq e.appArg! expanded) (← mkEqRefl e.appArg!)
          let property ← withLocalDeclD `hf (← inferType expanded) fun hf =>
            mkLambdaFVars #[hf] (e.setArg 5 hf)
          let proof ← mkCongrArg property equation
          return .visit { expr := e.setArg 5 expanded, proof? := some proof }
    return step }
  let (result, _) ← Simp.main bounds ctx (methods := methods)
  if !expandFields then return (result.expr, ← result.getProof)
  let domain := (← inferType bounds).getAppArgs[0]!
  withLocalDeclD `x domain fun x => do
    let (time, _) ← Simp.main (← mkAppM ``Bounds.time #[result.expr, x]) ctx (methods := methods)
    let (peak, _) ← Simp.main (← mkAppM ``Bounds.peak #[result.expr, x]) ctx (methods := methods)
    let b ← mkAppM ``Bounds.mk #[← mkLambdaFVars #[x] time.expr, ← mkLambdaFVars #[x] peak.expr]
    let equality ← mkAppOptM ``Bounds.ext #[some domain, some result.expr, some b,
      some (← mkFunExt (← mkLambdaFVars #[x] (← time.getProof))),
      some (← mkFunExt (← mkLambdaFVars #[x] (← peak.getProof)))]
    return (b, ← mkEqTrans (← result.getProof) equality)
open Lean Meta in
/-- Share certificates at cost nodes, keeping kernel checking independent of the depth of
the generated implementation term. Pending mathematical obligations remain local. -/
private def sourceCostProof (proof : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  let proof ← instantiateMVars proof
  let type ← inferType proof
  let saved ← if proof.hasExprMVar then pure proof else do
    try mkAuxTheorem type proof
    catch ex => throwError "source budget: certificate for {proof.getAppFn} failed:\n\
      {ex.toMessageData}"
  return (type.getAppArgs.back!, saved)
open Lean Meta in
/-- Check the harmless beta/projection conversions with call budgets abstracted. This keeps
conversion from evaluating a saved implementation merely to compare two cost functions. -/
private def sourceCostCast (f proof : Lean.Expr) : MetaM Lean.Expr := do
  let type ← inferType proof
  let original := type.getAppArgs[type.getAppArgs.size - 2]!
  if f == original then return proof
  let leavesRef ← IO.mkRef (#[] : Array Lean.Expr)
  for expression in #[f, original] do
    expression.forEach' fun e => do
      if e.isAppOfArity ``Implementation.bounds 6 && !e.hasLooseBVars then
        leavesRef.modify fun leaves => if leaves.contains e then leaves else leaves.push e
        return false
      return true
  let leaves := (← leavesRef.get).filter fun leaf =>
    (f.find? (· == leaf)).isSome && (original.find? (· == leaf)).isSome
  let declarations ← leaves.mapM fun e => return (`budget, ← inferType e)
  let equation ← withLocalDeclsDND declarations fun vars => do
    let abstract (e : Lean.Expr) := e.replace fun term => do
      let i ← leaves.idxOf? term
      vars[i]?
    let lhs := abstract f
    let rhs := abstract original
    let h ← mkAuxTheorem (← mkEq lhs rhs) (← mkEqRefl lhs)
    return h.replaceFVars vars leaves
  let property ← withLocalDeclD `cost (← inferType f) fun cost => do
    mkLambdaFVars #[cost] (← mkAppM ``Dominated #[cost, type.getAppArgs.back!])
  let result ← mkEqMPR (← mkCongrArg property equation) proof
  if result.hasExprMVar then return result
  mkAuxTheorem (← mkAppM ``Dominated #[f, type.getAppArgs.back!]) result
open Lean Meta in
/-- Calculate with the existing cost operators. Only saved call budgets are replaced; every
other atom, local constant, sum and maximum is retained literally. -/
private partial def calculateSourceCost (f : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) :=
  withIncRecDepth do
  let type ← whnf (← inferType f)
  withLocalDeclD `x type.bindingDomain! fun x => do
    let mut body := (mkApp f x).headBeta.consumeMData
    while body.headBeta != body do body := body.headBeta
    if let some hf := implementationOfBounds? body then
      unless hf.containsFVar x.fvarId! do
        if let some growth ← savedSourceGrowth? hf then
          let peak := body.getAppFn.isConstOf ``Bounds.peak ||
            match body.getAppFn with | .proj ``Bounds 1 _ => true | _ => false
          let bound := mkProj ``And (if peak then 1 else 0) growth
          let input ← mkLambdaFVars #[x] body.appArg!
          let proof ← mkAppM ``Dominated.comp #[bound, input]
          return ← sourceCostProof proof
    -- Reduce only the outer budget projection. Traversing the whole expression here
    -- would unfold saved call budgets before their own calculation step sees them.
    let projection := body.getAppFn
    if projection.isProj then
      if let some reduced ← reduceProj? projection then
        return ← calculateSourceCost (← mkLambdaFVars #[x]
          (mkAppN reduced body.getAppArgs).headBeta)
    else if let some info ← getProjectionFnInfo? (projection.constName?.getD .anonymous) then
      let args := body.getAppArgs
      if !info.fromClass && args.size > info.numParams then
        let some reduced ← unfoldDefinition? (mkAppN projection args[:info.numParams + 1]) |
          return (f, ← mkAppM ``Dominated.refl #[f])
        let next := (mkAppN reduced args[info.numParams + 1:]).headBeta
        if next != body then return ← calculateSourceCost (← mkLambdaFVars #[x] next)
    let binary? : Option Name :=
      if body.isAppOf ``HAdd.hAdd || body.isAppOf ``Nat.add then some ``Dominated.add
      else if body.isAppOf ``Max.max || body.isAppOf ``Nat.max then some ``Dominated.max
      else if body.isAppOf ``HMul.hMul || body.isAppOf ``Nat.mul then some ``Dominated.mul
      else none
    if let some rule := binary? then
      let args := body.getAppArgs
      let (_, left) ← calculateSourceCost (← mkLambdaFVars #[x] args[args.size - 2]!)
      let (_, right) ← calculateSourceCost (← mkLambdaFVars #[x] args.back!)
      let proof ← mkAppM rule #[left, right]
      return ← sourceCostProof proof
    if body.isAppOf ``HPow.hPow || body.isAppOf ``Nat.pow then
      let args := body.getAppArgs
      unless args.back!.containsFVar x.fvarId! do
        let (_, base) ← calculateSourceCost (← mkLambdaFVars #[x] args[args.size - 2]!)
        let proof ← mkAppM ``Dominated.pow #[base, args.back!]
        return ← sourceCostProof proof
    let traversal (xs callback : Lean.Expr) (rule : Name) : MetaM (Lean.Expr × Lean.Expr) := do
      let element := (← whnf (← inferType xs)).getAppArgs[0]!
      let family ← mkLambdaFVars #[x] element
      let domain ← mkAppM ``Sigma #[family]
      let lifted ← withLocalDeclD `z domain fun z => do
        let a ← mkAppM ``Sigma.fst #[z]
        let i ← mkAppM ``Sigma.snd #[z]
        let callback := callback.replaceFVar x a
        mkLambdaFVars #[z] (mkApp callback i)
      let (g, proof) ← calculateSourceCost lifted
      let proof ← sourceCostCast lifted proof
      let b ← withLocalDeclD `i element fun i => do
        let arg ← mkAppOptM ``Sigma.mk #[some type.bindingDomain!, some family, some x, some i]
        mkLambdaFVars #[x, i] (mkApp g arg)
      let proof ← mkAppOptM rule #[some type.bindingDomain!, some family,
        some (← mkLambdaFVars #[x] xs), some (← mkLambdaFVars #[x] callback), some b, some proof]
      return ← sourceCostProof proof
    if body.isAppOf ``List.sum then
      let list := body.appArg!
      if list.isAppOf ``List.map then
        let args := list.getAppArgs
        return ← traversal args.back! args[args.size - 2]! ``Dominated.sum_map
    if body.isAppOf ``List.foldr then
      let args := body.getAppArgs
      if (← getNatValue? args[args.size - 2]!) == some 0 then
        let callback ← lambdaTelescope args[args.size - 3]! fun ys value => do
          if ys.size != 2 then return none
          unless value.isAppOf ``Max.max || value.isAppOf ``Nat.max do return none
          let a := value.getAppArgs
          unless a.back! == ys[1]! do return none
          return some (← mkLambdaFVars #[ys[0]!] a[a.size - 2]!)
        if let some callback := callback then
          return ← traversal args.back! callback ``Dominated.foldr_max
    let f ← mkLambdaFVars #[x] body
    return (f, ← mkAppM ``Dominated.refl #[f])
open Lean Meta in
/-- The normal budget projection and the call specifications certify one already chosen
implementation. Budget failure never invokes the program selector again. -/
partial def calculateSourceBounds (implementation : Lean.Expr) :
    MetaM (Lean.Expr × Lean.Expr) := do
  if let some growth ← savedSourceGrowth? implementation then
    let type ← inferType growth
    let bounds ← mkAppM ``Bounds.mk #[type.getAppArgs[6]!, type.getAppArgs[7]!]
    return (bounds, growth)
  -- Compose the specification at the selected constructor before projecting its costs.
  -- Unregistered leaf certificates still use their explicit structural budget equations.
  let mut selected := implementation
  for _ in [:32] do
    selected ← instantiateMVars selected
    selected := selected.headBeta.consumeMData
    -- Local names in a constructor proof must not force the budget-projection fallback:
    -- after substituting the let, the same saved callback boundaries remain visible.
    if let .letE _ _ value body _ := selected.getAppFn then
      selected := mkAppN (body.instantiate1 value) selected.getAppArgs
      continue
    let args := selected.getAppArgs
    let binary? := if selected.isAppOf ``Implementation.comp then
        some ``Implementation.HasGrowth.comp
      else if selected.isAppOf ``Implementation.pair then some ``Implementation.HasGrowth.pair
      else if selected.isAppOf ``Implementation.mapDependentWith then
        some ``Implementation.HasGrowth.mapDependentWith
      else if selected.isAppOf ``Implementation.mapWith then some ``Implementation.HasGrowth.mapWith
      -- These constructors live in Library, which imports this translator. Resolve their
      -- ordinary growth lemmas only when the corresponding constructor is present.
      else if selected.isAppOf `Complexity.TreeProgram.Source.Implementation.finFunction then
        some `Complexity.TreeProgram.Source.Implementation.HasGrowth.finFunction
      else if selected.isAppOf `Complexity.TreeProgram.Source.Implementation.finApplyEncoded then
        some `Complexity.TreeProgram.Source.Implementation.HasGrowth.finApplyEncoded
      else if selected.isAppOf `Complexity.TreeProgram.Source.Implementation.finValApply then
        some `Complexity.TreeProgram.Source.Implementation.HasGrowth.finValApply
      else none
    let proof? ← if let some rule := binary? then do
        let (_, left) ← calculateSourceBounds args[args.size - 2]!
        let (_, right) ← calculateSourceBounds args.back!
        if selected.isAppOf `Complexity.TreeProgram.Source.Implementation.finFunction ||
            selected.isAppOf ``Implementation.mapDependentWith ||
            selected.isAppOf ``Implementation.mapWith then
          -- Retain the selected callback's parameter types, including unused captures.
          -- Inferring them anew from a constant callback loses this information.
          let lt := (← inferType left).getAppArgs
          let rt := (← inferType right).getAppArgs
          let parameters := args ++ #[lt[6]!, lt[7]!, rt[6]!, rt[7]!, left, right]
          some <$> mkAppOptM rule (parameters.map some)
        else
          some <$> mkAppM rule #[left, right]
      else if selected.isAppOf ``Implementation.ite ||
          selected.isAppOf ``Implementation.iteProp then do
        let (_, test) ← calculateSourceBounds args[args.size - 3]!
        let (_, left) ← calculateSourceBounds args[args.size - 2]!
        let (_, right) ← calculateSourceBounds args.back!
        let rule := if selected.isAppOf ``Implementation.ite then
            ``Implementation.HasGrowth.ite else ``Implementation.HasGrowth.iteProp
        some <$> mkAppM rule #[test, left, right]
      else if selected.isAppOf ``Implementation.mapDependent then do
        let (_, growth) ← calculateSourceBounds args.back!
        some <$> mkAppM ``Implementation.HasGrowth.mapDependent #[growth]
      else if selected.isAppOf ``Implementation.mapInput ||
          selected.isAppOf ``Implementation.mapOutput then do
        let (_, growth) ← calculateSourceBounds args[args.size - 3]!
        let rule := if selected.isAppOf ``Implementation.mapInput then
            ``Implementation.HasGrowth.mapInput else ``Implementation.HasGrowth.mapOutput
        some <$> mkAppM rule #[growth, args[args.size - 2]!, args.back!]
      else if selected.isAppOf `Complexity.TreeProgram.Source.Implementation.ofSome then do
        let (_, growth) ← calculateSourceBounds args[args.size - 2]!
        some <$> mkAppM `Complexity.TreeProgram.Source.Implementation.HasGrowth.ofSome
          #[growth, args.back!]
      else if selected.isAppOf ``Recursion.implementation then do
        let recursion := args[args.size - 5]!
        let mut budgets := #[]
        let mut proofs := #[]
        for callback in args[args.size - 4:] do
          let (budget, proof) ← calculateSourceBounds callback
          budgets := budgets.push budget
          proofs := proofs.push proof
        let cost ← mkAppM ``Recursion.cost (#[recursion] ++ budgets)
        let domain := (← whnf (← inferType cost)).bindingDomain!
        let estimate ← withLocalDeclD `x domain fun x => do
          let time ← mkLambdaFVars #[x] (← mkAppM ``Cost.time #[mkApp cost x])
          let peak ← mkLambdaFVars #[x] (← mkAppM ``Cost.peak #[mkApp cost x])
          mkAppM ``And.intro #[← mkAppM ``Dominated.refl #[time],
            ← mkAppM ``Dominated.refl #[peak]]
        some <$> mkAppM ``Recursion.hasGrowth_of_growth (#[recursion] ++ proofs ++ #[estimate])
      else if selected.isAppOf ``Implementation.congr then do
        let (_, growth) ← calculateSourceBounds args[args.size - 2]!
        some <$> mkAppM ``Implementation.HasGrowth.congr #[growth, args.back!]
      else if selected.isAppOf ``Implementation.ofEncode then do
        let (_, growth) ← calculateSourceBounds args.back!
        some <$> mkAppM ``Implementation.HasGrowth.ofEncode #[growth, args[args.size - 2]!]
      else pure none
    if let some proof := proof? then
      let type ← inferType proof
      let proof ← if selected == implementation then pure proof else do
        let equation ← mkAuxTheorem (← mkEq implementation selected) (← mkEqRefl implementation)
        let property ← withLocalDeclD `hf (← inferType selected) fun hf =>
          mkLambdaFVars #[hf] (type.setArg 5 hf)
        pure (← mkEqMPR (← mkCongrArg property equation) proof)
      return (← mkAppM ``Bounds.mk #[type.getAppArgs[6]!, type.getAppArgs[7]!], proof)
    if selected.isAppOf ``Implementation.ofImplements || selected.isAppOf ``Implementation.mk then
      break
    let some expanded ← unfoldDefinition? selected (ignoreTransparency := true) | break
    selected := expanded.headBeta
  let (bounds, eq) ← normalizeSourceBounds implementation true
  let eq ← mkAuxTheorem (← inferType eq) eq
  let (time, ht) ← calculateSourceCost (← mkAppM ``Bounds.time #[bounds])
  let (peak, hp) ← calculateSourceCost (← mkAppM ``Bounds.peak #[bounds])

  let ht ← sourceCostCast (← mkAppM ``Bounds.time #[bounds]) ht
  let hp ← sourceCostCast (← mkAppM ``Bounds.peak #[bounds]) hp
  let proof ← mkAppM ``Implementation.HasGrowth.of_bounds #[implementation, eq, ht, hp]
  return (← mkAppM ``Bounds.mk #[time, peak], proof)
open Lean Meta Elab Tactic in
private def sourceCallsWith (query : Lean.Expr → MetaM (Option Lean.Expr)) : TacticM Unit :=
  FiniteCases.sourceCalls fun f => do
    let target ← mkAppM ``Implementation #[f]
    let some implementation ← query target |
      Search.unsupported m!"source calls: no implementation for branch {f}"
    let implementation ← instantiateMVars implementation
    let (_, equality) ← normalizeSourceBounds implementation
    return (implementation, equality)

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
  unless goal.isAppOfArity ``Implementation 5 do return none
  if goal.getAppArgs[4]!.hasExprMVar then return none
  let locals := (← getLCtx).foldl (fun ds d => d :: ds) []
  for decl in locals do
    if decl.kind == .auxDecl then continue
    let type ← instantiateMVars decl.type
    unless type.isAppOfArity ``Implementation 5 do continue
    if let some result ← Search.attempt unfolded do
        if ← withReducible (isDefEq type goal) then return some ⟨decl.toExpr⟩
        return none then
      return some result
  return none
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
  trace[source.translation] "implementation query: {goal}"
  session.step
  trace[Meta.Tactic.fun_prop] "source step {← session.steps.get}: {goal}"
  if let some result ← localSourceCertificate unfolded goal then return some result
  if let some { proof? := some proof, .. } := (← get).cache.find? goal then
    return some ⟨proof⟩
  if (← get).failureCache.contains goal then return none
  if ancestors.contains goal then return none
  let ancestors := ancestors.push goal
  increaseSteps
  let restore ← Search.checkpoint unfolded
  let search := sourceSearch session true ancestors
  let context ← read
  -- A branch has a different local context: only fuel, path and diagnostics cross this boundary.
  let query := sourceQuery search context
  let structural : FunPropM (Option Result) := Search.attempt unfolded do
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
    for action in [FiniteCases.sourceCases, sourceDependent *> solve, sourceCallsWith query] do
      if let some proof ← session.discharge ancestors action goal then
        unless nested do unfolded.modify fun (names, _) => (names, true)
        return some ⟨proof⟩
    return none
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
  -- Certify a specified source; a speculative rule must not invent missing callbacks.
  if f.hasExprMVar then return ← finish none
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
      let candidates ← Search.functionTheorems decl d
      let env ← getEnv
      let rules (fallback : Bool) : FunPropM (Option Result) := do
        for rule in candidates do
          if Search.isFallback env rule != fallback then continue
          if let some result ← Search.functionRules unfolded search decl target d #[rule] then
            return some result
        return none
      -- This driver owns every stage; queries and certificate adapters do not schedule work.
      if let some r ← rules false then return some r
      if let some name := encodedCall then
        if let some r ← rules true then return some r
        session.reject ancestors (Search.recursionMessage name) .specification (some name)
        return none
      -- Root constructors use their encoding equations; nested structural helpers remain atomic.
      if let .const name _ := d.fn then
        if !nested && (← getConstInfo name).isCtor then
          if let some r ← Search.transitionRules unfolded search target then return some r
      -- A nonmatching candidate must not block structural field extraction.
      if nested || !candidates.isEmpty then
        if let some r ← structural then return some r
      -- Subcall specifications need structural decomposition before their fallback rules:
      -- otherwise lookup of a composite table can recursively request rebuilding that table.
      if let some r ← rules true then return some r
      -- An encoder describes representation; unfolding it does not select an algorithm.
      if d.fn.isConstOf ``UniqueEncoding.encode then
        session.reject ancestors m!"source translation: no implementation for the encoded result; \
          select a rule scope with `using`, or register a function equality with `[source]`"
          .specification
        return none
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
private def withSourceSpecs {α : Type} (scope : Option Ident) (action : TacticM α) : TacticM α := do
  pushScope
  try
    activateScoped `Complexity.TreeProgram.Source
    if let some scope := scope then
      for ns in ← resolveNamespace scope do activateScoped ns
    action
  finally
    popScope

open Lean Meta Elab Tactic Mathlib.Meta.FunProp in
private def sourceContext : MetaM Mathlib.Meta.FunProp.Context := do
  let tactic ← `(tactic| first | with_reducible assumption | infer_param | source_encoding)
  let config := { maxSteps := source.maxSteps.get (← getOptions) : Mathlib.Meta.FunProp.Config }
  return { disch := tacticToDischarge tactic, config }

open Lean Meta Elab Tactic Mathlib.Meta.FunProp in
private def proveSource (scope : Option Ident := none) (replacement : Option Term := none) :
    TacticM (Array Ident × Bool × Lean.Expr × List MVarId) :=
    withSourceSpecs scope <| withMainContext do
  let goal ← getMainGoal
  let saved ← saveState
  let session ← Search.Session.create
  let unfolded := session.unfolded
  let context ← sourceContext
  try
    let original := (← instantiateMVars (← goal.getType)).consumeMData
    let (target, equality) ← match replacement with
      | none => pure (original, none)
      | some replacement =>
        let f := original.getAppArgs[4]!
        let g ← elabTermEnsuringType replacement (← inferType f)
        Term.synthesizeSyntheticMVarsNoPostponing
        let g ← instantiateMVars g
        if g.hasExprMVar then
          throwError "provide a concrete source function after `via`"
        let h ← mkFreshExprSyntheticOpaqueMVar (← mkEq f g) (tag := `source_eq)
        pure (original.setArg 4 g, some h)
    let some result ← sourceQuery (sourceSearch session false #[]) context target |
      session.report
    let proof ← match equality with
      | none => pure result
      | some h => mkAppM ``Implementation.congr #[result, ← mkEqSymm h]
    goal.assign proof
    replaceMainGoal []
    let (names, structural) ← unfolded.get
    return (names.map mkIdent, structural, target.getAppArgs[4]!, equality.toList.map (·.mvarId!))
  catch ex =>
    saved.restore
    throw ex

/-- A recursion method supplies ordinary callbacks and mathematical resource allowances. -/
declare_syntax_cat sourceRecursion
syntax "recursion" " (" &"test" " := " term ")" " (" &"next" " := " term ")"
  " (" &"finish" " := " term ")" " (" &"resume" " := " term ")"
  " (" &"measure" " := " term ")" " (" &"decreases" " := " term ")" : sourceRecursion

open Lean Meta Elab Tactic Mathlib.Meta.FunProp in
private def proveRecursion (method : TSyntax `sourceRecursion) (scope : Option Ident := none) :
    TacticM (Array Ident × Bool × Lean.Expr × List MVarId) :=
    withSourceSpecs scope <| withMainContext do
  let `(sourceRecursion| recursion (test := $test) (next := $next)
    (finish := $finish) (resume := $resume) (measure := $measure) (decreases := $decreases)) :=
    method | throwUnsupportedSyntax
  let goal ← getMainGoal
  let rest := (← getGoals).drop 1
  let (args, _) ← sourceGoalArgs goal
  let source := args[4]!
  let allowanceType ← mkArrow args[0]! (mkConst ``Nat)
  -- An encoded dependent result still describes an ordinary dependent source function.
  let f ← lambdaTelescope source fun xs body => do
    if body.isAppOfArity ``UniqueEncoding.encode 4 then
      mkLambdaFVars xs body.appArg!
    else pure source
  let constructor ← mkConstWithFreshMVarLevels ``Recursion.mk
  let (fields, _, resultType) ← forallMetaTelescope (← inferType constructor)
  unless ← isDefEq resultType (← mkAppM ``Recursion #[f]) do
    throwError "source recursion: could not determine the source function type"
  let r := mkAppN constructor fields
  for (index, value) in #[(3, test), (4, next), (5, finish), (6, resume)] do
    let value ← elabTermEnsuringType value (← inferType fields[index]!)
    fields[index]!.mvarId!.assign value
  Term.synthesizeSyntheticMVarsNoPostponing
  fields[9]!.mvarId!.assign (← elabTermEnsuringType measure allowanceType)
  fields[10]!.mvarId!.assign (← elabTermEnsuringType decreases (← inferType fields[10]!))
  Term.synthesizeSyntheticMVarsNoPostponing
  let mut obligations := []
  for (index, tag) in #[(7, `finish_eq), (8, `resume_eq)] do
    let h ← mkFreshExprSyntheticOpaqueMVar (← instantiateMVars (← inferType fields[index]!))
      (tag := tag)
    fields[index]!.mvarId!.assign h
    obligations := obligations ++ [h.mvarId!]
  let r ← instantiateMVars r
  let session ← Search.Session.create
  let context ← sourceContext
  let certify (name : Name) (callback : Lean.Expr) : TacticM Lean.Expr := do
    if callback.hasExprMVar then
      throwError "source recursion: provide a concrete `{name}` callback"
    session.failure.set none
    let target ← mkAppM ``Implementation #[callback]
    let some proof ← sourceQuery (sourceSearch session false #[]) context target |
      try session.report catch ex => throwError "source recursion `{name}`: {ex.toMessageData}"
    let proof ← instantiateMVars proof
    if proof.hasExprMVar || proof.hasSorry then
      throwError "source recursion: the `{name}` callback has unfinished obligations"
    trace[source.translation] "source recursion: translating {name} complete"
    return proof
  let hc ← certify `test (← instantiateMVars fields[3]!)
  let hs ← certify `next (← instantiateMVars fields[4]!)
  let encodeResult (callback : Lean.Expr) : MetaM Lean.Expr := do
    forallTelescope (← inferType callback) fun xs _ => do
      let result ← mkAppM ``encode #[mkConst ``Tree, mkAppN callback xs]
      mkLambdaFVars xs result
  let hd ← certify `finish (← encodeResult (← instantiateMVars fields[5]!))
  let resume ← instantiateMVars fields[6]!
  let returnType ← forallTelescope (← inferType resume) fun xs _ => do
    mkAppM ``Sigma #[← mkLambdaFVars #[xs[0]!] (← inferType xs[1]!)]
  let resume ← withLocalDeclD `x returnType fun x => do
    let call := mkAppN resume #[← mkAppM ``Sigma.fst #[x], ← mkAppM ``Sigma.snd #[x]]
    mkLambdaFVars #[x] (← mkAppM ``encode #[mkConst ``Tree, call])
  let hr ← certify `resume resume
  let implementation ← mkAppM ``Recursion.implementation #[r, hc, hs, hd, hr]
  let proof ← mkAppM ``Implementation.implements #[implementation]
  let actual := (← inferType proof).getAppArgs
  let equality ← withLocalDeclD `x args[0]! fun x => do
    let lhs ← mkAppM ``encode #[mkConst ``Tree, mkApp source x]
    let rhs ← mkAppM ``encode #[mkConst ``Tree, mkApp actual[5]! x]
    let proof ← typedSourceProof (← mkEq lhs rhs) (← mkEqRefl lhs)
    mkLambdaFVars #[x] proof
  let result ← mkAppOptM ``Implementation.ofEncode #[some args[0]!, some args[1]!, none,
    some args[2]!, some args[3]!, none, some source, some actual[5]!,
    some equality, some implementation]
  let target ← instantiateMVars (← goal.getType)
  unless ← isDefEq (← inferType result) target do
    throwError "source recursion: the selected implementation does not match the requested bound"
  goal.assign result
  trace[source.translation] "source recursion: program combined"
  setGoals obligations
  let (names, _) ← session.unfolded.get
  let names := names.map mkIdent
  setGoals rest
  return (names, false, source, obligations)
open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| source_fun_prop $[using $scope:ident]? $[via $replacement]?) => do
    let target := (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
    if target.isAppOf ``Implementation.HasGrowth then
      if replacement.isSome then throwError "source budget: the implementation is already selected"
      withMainContext do
        let (_, growth) ← calculateSourceBounds target.getAppArgs[5]!
        let mono := ``Implementation.HasGrowth.mono
        let parameters := (← inferType growth).getAppArgs ++ target.getAppArgs[6:8] ++ #[growth]
        let goals ← (← getMainGoal).apply (← mkAppOptM mono (parameters.map some))
        replaceMainGoal goals
    else if target.isAppOf ``Dominated then
      if replacement.isSome then throwError "source budget: the implementation is already selected"
      withMainContext do
        let args := target.getAppArgs
        let f := args[args.size - 2]!
        let g := args.back!
        unless ← isDefEq target (← mkAppM ``Dominated #[f, g]) do
          throwError "source budget: callback substitution requires a uniform comparison"
        let (bound, growth) ← calculateSourceCost f
        if ← withReducible (isDefEq f bound) then
          throwError "source budget: no saved callback specification applies"
        let comparison ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``Dominated #[bound, g])
        (← getMainGoal).assign (← mkAppM ``Dominated.trans #[growth, comparison])
        replaceMainGoal [comparison.mvarId!]
    else
      let (_, _, _, obligations) ← proveSource scope replacement
      setGoals (obligations ++ (← getGoals))
open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| source_calls) => withSourceSpecs none <| withMainContext do
    let session ← Search.Session.create
    let goal ← getMainGoal
    let target ← goal.getType
    let query := sourceQuery (sourceSearch session true #[target]) (← sourceContext)
    let some proof ← session.discharge #[target] (sourceCallsWith query) target | session.report
    goal.assign proof
    replaceMainGoal []
open Lean Meta Elab Tactic in
/-- Translate a source function and reduce its model time-space bound to arithmetic goals. -/
private def modelFunPropCore
    (translate : TacticM (Array Ident × Bool × Lean.Expr × List Lean.MVarId))
    : TacticM Unit := do
  let originalGoals ← getGoals
  setGoals (originalGoals.take 1)
  let target ← (← getMainGoal).getType
  let machine := target.isAppOf ``TimeSpaceModel.ComputableWithGrowth
  let asymptotic := (target.find? (·.isConstOf ``FTISP)).isSome
  unless machine || asymptotic do
    throwError "model_fun_prop expects a tree ComputableWithGrowth or FTISP target"
  let powers ← if let some application := target.find? (·.isAppOf ``FTISP) then do
      let args := application.getAppArgs
      let exponent (f : Lean.Expr) : MetaM (Option Nat) :=
        withLocalDeclD `n (mkConst ``Nat) fun n => do
          let body := (mkApp (← whnf f) n).headBeta
          if body.isAppOf ``HPow.hPow || body.isAppOf ``Nat.pow then
            let args := body.getAppArgs
            if args[args.size - 2]! == n then return ← getNatValue? args.back!
          return none
      let t ← exponent args[args.size - 2]!
      let s ← exponent args.back!
      pure (do let t ← t; let s ← s; if s > 0 then some (t, s) else none)
    else pure none
  if machine then
    evalTactic (← `(tactic| refine Implementation.HasGrowth.computableWithGrowth_of_dominated
      (hf := ?implementation) (t := ?time_bound) (p := ?peak_bound) ?growth ?time ?peak))
  else if let some (t, s) := powers then
    evalTactic (← `(tactic| refine Implementation.HasGrowth.mem_ftisp_pow
      (hf := ?implementation) (t := $(quote t)) (s := $(quote s)) ?growth (by decide)))
  else
    evalTactic (← `(tactic| refine Implementation.HasGrowth.mem_ftisp_of_dominated
      (hf := ?implementation) (t := ?time_bound) (p := ?peak_bound) ?growth ?time ?peak))
  let implementationGoal ← getMainGoal
  let pending ← getGoals
  let (_, _, _, obligations) ← translate
  if powers.isSome then
    let [_, growthGoal] := pending | throwError "source model: unexpected power obligations"
    let comparisons ← growthGoal.withContext do
      let implementation ← instantiateMVars (mkMVar implementationGoal)
      let (_, growth) ← calculateSourceBounds implementation
      let target ← instantiateMVars (← growthGoal.getType)
      let parameters := (← inferType growth).getAppArgs ++ target.getAppArgs[6:8] ++ #[growth]
      growthGoal.apply (← mkAppOptM ``Implementation.HasGrowth.mono (parameters.map some))
    setGoals (obligations ++ comparisons ++ originalGoals.drop 1)
    return
  let [_, timeBound, peakBound, growthGoal, timeGoal, peakGoal] := pending |
    throwError "source model: unexpected budget obligations"
  growthGoal.withContext do
    let implementation ← instantiateMVars (mkMVar implementationGoal)
    let (bounds, growth) ← calculateSourceBounds implementation
    timeBound.assign (← whnf (← mkAppM ``Bounds.time #[bounds]))
    peakBound.assign (← whnf (← mkAppM ``Bounds.peak #[bounds]))
    growthGoal.assign growth
  setGoals (obligations ++ [timeGoal, peakGoal] ++ originalGoals.drop 1)

open Lean Elab Tactic in
def modelFunProp
    (translate : TacticM (Array Ident × Bool × Lean.Expr × List Lean.MVarId))
    : TacticM Unit := do
  let saved ← saveState
  try modelFunPropCore translate
  catch ex => saved.restore; throw ex
syntax "model_fun_prop" (" using " ident)? (" via " term)? : tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| model_fun_prop $[using $scope:ident]? $[via $replacement]?) =>
    modelFunProp (proveSource scope replacement)

syntax "model_fun_prop" " using " sourceRecursion (" using " ident)? : tactic
syntax "source_fun_prop" " using " sourceRecursion (" using " ident)? : tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| model_fun_prop using $method:sourceRecursion $[using $scope:ident]?) =>
    modelFunProp (proveRecursion method scope)
  | `(tactic| source_fun_prop using $method:sourceRecursion $[using $scope:ident]?) => do
    let (_, _, _, obligations) ← proveRecursion method scope
    setGoals (obligations ++ (← getGoals))
open Lean Meta in
private def withSourceEncodings (parameters : List Lean.Expr) (action : MetaM Unit) :
    MetaM Unit := do
  match parameters with
  | [] => action
  | parameter :: rest =>
    if (← inferType parameter).isSort && !(← isProp parameter) then
      let type ← mkAppM ``UniqueEncoding #[mkConst ``Tree, parameter]
      if (← synthInstance? type).isNone then
        withLocalDecl `sourceEncoding .instImplicit type fun _ =>
          withSourceEncodings rest action
      else withSourceEncodings rest action
    else withSourceEncodings rest action

/-- Save an equality's right-hand implementation, or the same program with the budget proved
directly by `model_fun_prop`. Arbitrary model existence theorems are not source certificates.
Local and scoped registrations use `fun_prop`; `using ns` selects rules for an equality. -/
syntax (name := sourceAttribute) "source" (" using " ident)? : attr

open Lean Meta Elab Tactic Mathlib.Meta.FunProp in
initialize registerBuiltinAttribute {
  name := `sourceAttribute
  descr := "save a source implementation, including a directly certified model budget"
  applicationTime := .afterCompilation
  add := fun name stx kind => MetaM.run' do
    let saved ← getEnv
    try
      let `(attr| source $[using $scope:ident]?) := stx | throwUnsupportedSyntax
      let info ← getConstInfo name
      let equality := mkConst name (info.levelParams.map mkLevelParam)
      forallTelescope info.type fun parameters type =>
        withSourceEncodings parameters.toList do
          for parameter in parameters do
            let parameterDecl ← parameter.fvarId!.getDecl
            if !parameterDecl.binderInfo.isInstImplicit && (← isProp parameterDecl.type) then
              throwError "`source` needs an unconditional function equality; \
                use a local `via` proof for a replacement depending on a hypothesis"
          let (result, growth) ← if let some (_, f, g) := type.eq? then do
            unless (← whnf (← inferType f)).isForall do
              throwError "`source` expects a function equality; \
                use `funext` for pointwise equations"
            let target ← mkAppM ``Implementation #[g]
            let goal ← mkFreshExprSyntheticOpaqueMVar target
            let action : TermElabM Unit := do
              discard <| Tactic.run goal.mvarId! do
                discard <| proveSource scope
            discard <| action.run {} {}
            let proof ← instantiateMVars goal
            if proof.hasExprMVar || proof.hasSorry then
              throwError "the selected source implementation has unfinished obligations"
            let result ← mkAppM ``Implementation.congr
              #[proof, ← mkEqSymm (mkAppN equality parameters)]
            let (_, growth) ← calculateSourceBounds result
            pure (result, growth)
          else withoutExporting do
            let proofInfo ← getConstInfo name
            let some value := proofInfo.value? (allowOpaque := true) |
              throwError "`source` needs a function equality or a direct `model_fun_prop` proof"
            let proof ← sourceModelProof (mkAppN value parameters)
            let directGrowth ← if proof.isAppOfArity
                ``Implementation.HasGrowth.computableWithGrowth 9 then
                pure (some proof.getAppArgs[8]!)
              else if proof.isAppOfArity
                  ``Implementation.HasGrowth.computableWithGrowth_of_dominated 13 then
                pure (some proof.getAppArgs[10]!)
              else if proof.isAppOfArity ``Implementation.HasGrowth.mem_ftisp 12 ||
                proof.isAppOfArity ``Implementation.HasGrowth.mem_ftisp_pow 10 then
                pure (some proof.getAppArgs[8]!)
              else if proof.isAppOfArity ``Implementation.HasGrowth.mem_ftisp_of_dominated 13 ||
                  proof.isAppOfArity ``Implementation.HasGrowth.mem_ftisp_of_sizeEnvelope 13 then
                pure (some proof.getAppArgs[10]!)
              else pure none
            let some growth := directGrowth |
              throwError "`source` needs an equality or a direct growth-specification exit; \
                it cannot recover a source program from an arbitrary model theorem"
            if proof.hasSorry then
              throwError "the model budget proof has unfinished obligations"
            if scope.isSome then
              throwError "select the scope with `model_fun_prop using`, before saving its budget"
            pure ((← inferType growth).getAppArgs[5]!, growth)
          -- Keep private proof dependencies behind the saved definition. Consumers use an
          -- explicit budget equation instead of unfolding its evaluator or certification.
          let (certificate, projection, programProjection) ← withoutExporting do
            let certificate ← mkAuxDefinition (← mkFreshUserName (name ++ `sourceImplementation))
              (← inferType result) result (compile := false)
            -- The saved logical certificate may contain classically chosen cost witnesses.
            modifyEnv (addNoncomputable · certificate.getAppFn.constName!)
            let bounds ← mkAppM ``Implementation.bounds #[result]
            let proof ← mkEqRefl bounds
            let type ← mkEq (← mkAppM ``Implementation.bounds #[certificate]) bounds
            let closed ← Closure.mkValueTypeClosure type proof false
            let projection ← mkFreshUserName (name ++ `bounds_sourceImplementation)
            addDecl <| .thmDecl {
              name := projection
              levelParams := closed.levelParams.toList
              type := closed.type
              value := closed.value }
            let program ← mkAppM ``Implementation.program #[result]
            let type ← mkEq (← mkAppM ``Implementation.program #[certificate]) program
            let closed ← Closure.mkValueTypeClosure type (← mkEqRefl program) false
            let programBase := name ++ `program_sourceImplementation
            let programProjection ← if kind == .local || (← getEnv).contains programBase then
                mkFreshUserName programBase
              else pure programBase
            addDecl <| .thmDecl {
              name := programProjection
              levelParams := closed.levelParams.toList
              type := closed.type
              value := closed.value }
            -- Preserve the implementation's own specification across the private saved
            -- alias. A weaker model exit must not become a second callback candidate.
            let original ← savedSourceGrowth? result
            let growth ← match original with
              | some h => pure h
              | none => pure growth
            let growthBase := name ++ `hasGrowth_sourceImplementation
            let growthName ← if kind == .local || (← getEnv).contains growthBase then
                mkFreshUserName growthBase
              else pure growthBase
            let type := (← inferType growth).setArg 5 certificate
            let closed ← Closure.mkValueTypeClosure type growth false
            addDecl <| .thmDecl {
              name := growthName
              levelParams := closed.levelParams.toList
              type := closed.type
              value := closed.value }
            registerSourceGrowth growthName kind
            pure (certificate.getAppFn.constName!, projection, programProjection)
          for attr in #[`simp, `source_bounds] do
            let some ext ← getSimpExtension? attr | throwError "missing {attr} simplifier"
            addSimpTheorem ext projection (post := false) (inv := false) .global 1000
          let some simpExt ← getSimpExtension? `simp | throwError "missing simp simplifier"
          addSimpTheorem simpExt programProjection (post := false) (inv := false) .global 1000
          sourceSavedImplementationExt.add certificate kind
          addTheorem certificate kind 1001
    catch ex =>
      setEnv saved
      throw ex
}

end Complexity.TreeProgram.Source
