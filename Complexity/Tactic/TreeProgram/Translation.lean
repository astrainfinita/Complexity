/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Tactic.TreeProgram.Rules
public import Complexity.Tactic.TreeProgram.Recursion
public import Complexity.Tactic.TreeProgram.Growth
public meta import Complexity.Tactic.TreeProgram.Search
public meta import Complexity.Tactic.TreeProgram.Environment
public import Complexity.Models.TreeMachine.Language.Derive
public meta import Complexity.Models.TreeMachine.Language.Semantics
public import Complexity.Resources.TreeMachine.Program
public import Complexity.Classes.Functions.Basic
public import Complexity.Encoding.TreeSize
public meta import Lean.Meta.Match.MatcherApp.Basic
public meta import Lean.Meta.RecExt

/-! # Certified translation of Lean source functions

Translation selects one program by composing implementation rules. The growth of the result is
the one stated by those rules; it is never recomputed from a finished implementation term.
-/

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

namespace Implementation

variable {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β] {f : α → β}
  {t p : α → ℕ}

/-- Keep loading, controller and peak costs when hiding the fixed machine's register factor. -/
theorem computableWithGrowth (hf : Implementation f t p) :
    TimeSpaceModel.tree.ComputableWithGrowth f (fun x => t x + 4)
      (fun x => max ⌜x⌝ₜ.size (p x) + 2) := by
  obtain ⟨b, h, ht, hp⟩ := hf.sound
  exact ⟨fun x => b.time x + 4,
    fun x => (hf.program .input).registers * (max ⌜x⌝ₜ.size (b.peak x) + 2),
    h.computableWithin (fun _ => ⟨le_rfl, le_rfl⟩), ht.add (Dominated.refl _),
    (((Dominated.refl _).max hp).add (Dominated.refl _)).const_mul_left _⟩

/-- Compare the input budgets at the machine boundary. Loading and storage overheads remain
explicit. -/
theorem computableWithGrowth_of_dominated {T S : α → ℕ} (hf : Implementation f t p)
    (ht : Dominated (fun x => t x + 4) T)
    (hp : Dominated (fun x => max ⌜x⌝ₜ.size (p x) + 2) S) :
    TimeSpaceModel.tree.ComputableWithGrowth f T S :=
  hf.computableWithGrowth.mono ht hp

end Implementation

end Complexity.TreeProgram.Source

namespace Complexity

namespace TreeProgram.Source.Implementation

variable {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
  {f : α → β} {t p : α → ℕ} {T S : ℕ → ℕ}

theorem mem_ftisp (hf : Implementation f (fun x => T ⌜x⌝ₜ.size) (fun x => S ⌜x⌝ₜ.size))
    (input : Dominated (fun x : α => ⌜x⌝ₜ.size) (fun x => S ⌜x⌝ₜ.size))
    (time_overhead : Dominated (fun _ : α => 4) (fun x => T ⌜x⌝ₜ.size))
    (space_overhead : Dominated (fun _ : α => 2) (fun x => S ⌜x⌝ₜ.size)) :
    f ∈ FTISP .tree T S :=
  (hf.computableWithGrowth_of_dominated
    ((Dominated.refl _).add_same time_overhead)
    ((input.max_same (Dominated.refl _)).add_same space_overhead)).mem_ftisp

/-- Compare the structural growth with the scale functions at the model boundary. -/
theorem mem_ftisp_of_dominated (hf : Implementation f t p)
    (ht : Dominated (fun x => t x + 4) (fun x => T ⌜x⌝ₜ.size))
    (hp : Dominated (fun x => max ⌜x⌝ₜ.size (p x) + 2) (fun x => S ⌜x⌝ₜ.size)) :
    f ∈ FTISP .tree T S :=
  (hf.computableWithGrowth_of_dominated ht hp).mem_ftisp

/-- Exact-size envelopes are used only where an eventual scale comparison is required.
This permits finite input types to inhabit a zero eventual class without weakening their
all-input program or machine specifications. -/
theorem mem_ftisp_of_sizeEnvelope (hf : Implementation f t p)
    (ht : DominatedAtTop (sizeEnvelope (fun x => t x + 4)) T)
    (hp : DominatedAtTop (sizeEnvelope (fun x => max ⌜x⌝ₜ.size (p x) + 2)) S) :
    f ∈ FTISP .tree T S := by
  have hm := hf.computableWithGrowth.mono
    (Dominated.of_le (le_sizeEnvelope (fun x => t x + 4)))
    (Dominated.of_le (le_sizeEnvelope (fun x => max ⌜x⌝ₜ.size (p x) + 2)))
  exact FTISP.mono ht hp hm.mem_ftisp

/-- The usual positive powers of encoding size absorb the model's input storage,
fixed controller overheads and fixed register factor. -/
theorem mem_ftisp_pow {t s : ℕ}
    (hf : Implementation f (fun x => ⌜x⌝ₜ.size ^ t) (fun x => ⌜x⌝ₜ.size ^ s))
    (hs : 0 < s) : f ∈ FTISP .tree (fun n => n ^ t) (fun n => n ^ s) := by
  apply hf.mem_ftisp
  · exact (Dominated.of_le fun x => Nat.le_self_pow (by omega) _)
  · exact (Dominated.const_of_pos 4 (fun x => Nat.pow_pos (Tree.size_pos ⌜x⌝ₜ)))
  · exact (Dominated.const_of_pos 2 (fun x => Nat.pow_pos (Tree.size_pos ⌜x⌝ₜ)))

end TreeProgram.Source.Implementation

end Complexity

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
open Lean Meta Elab Tactic in
private def sourceGoalArgs (goal : MVarId) : MetaM (Array Lean.Expr) := do
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOfArity ``Implementation 7 do
    throwError "source translation: expected Implementation, got {target}"
  return target.getAppArgs
open Lean Meta in
/-- Assign a translation result, unifying the requested growth with the produced one. -/
private def assignImplementation (goal : MVarId) (value : Lean.Expr) : MetaM Unit := do
  unless ← isDefEq (← goal.getType) (← inferType value) do
    Search.unsupported m!"source translation: the produced growth does not match the request"
  goal.assign value
open Lean Meta Elab Tactic in
private def sourceDependent : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let #[input, _, _, _, f, time, peak] ← sourceGoalArgs goal |
    throwError "source dependent: invalid source arguments"
  let (g, proof) ← withLocalDeclD `x input fun x => do
    let lhs ← mkAppM ``encode #[mkConst ``Tree, mkApp f x]
    let (code, proof) ← structuralResult x.fvarId! lhs true
    let proof ← typedSourceProof (← mkEq lhs code) proof
    return (← mkLambdaFVars #[x] code.appArg!, ← mkLambdaFVars #[x] proof)
  let next ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``Implementation #[g, time, peak])
  goal.assign (← mkAppM ``Implementation.ofEncode #[proof, next])
  replaceMainGoal [next.mvarId!]

/-- Reinterpret a dependent source result through its structural encoding. -/
elab (name := sourceDependentTactic) "source_dependent" : tactic => sourceDependent

/-- Certify source branches with previously registered function implementations. -/
syntax (name := sourceCalls) "source_calls" : tactic
/-- Compose source-function implementations and their growth.
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
  let #[inputType, outputType, inputInst, outputInst, f, _, _] ← sourceGoalArgs goal |
    throwError "source cases: invalid source arguments"
  if let .const name _ := f.eta.getAppFn then
    if ← isRecursiveDefinition name then
      Search.unsupported (Search.recursionMessage name)
  let program ← mkFreshExprMVar (← mkArrow (mkConst ``Value)
    (← mkAppM ``Code #[mkConst ``Value]))
  let bounds ← mkFreshExprMVar (← mkAppM ``Bounds #[inputType])
  let type ← mkAppOptM ``Implements #[some inputType, some outputType, some inputInst,
    some outputInst, some program, some f, some bounds]
  let certificate ← mkFreshExprSyntheticOpaqueMVar type
  setGoals [certificate.mvarId!]
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
  let time := mkNatLit time
  let (timeFn, peak) ← withLocalDeclD `x inputType fun x => do
    let input ← mkAppOptM ``encode
      #[some (mkConst ``Tree), some inputType, some inputInst, some x]
    let output ← mkAppOptM ``encode
      #[some (mkConst ``Tree), some outputType, some outputInst, some (mkApp f x).headBeta]
    let peak ← mkAppM ``max #[← mkAppM ``Tree.size #[input], ← mkAppM ``Tree.size #[output]]
    return (← mkLambdaFVars #[x] time, ← mkLambdaFVars #[x] peak)
  bounds.mvarId!.assign (← mkAppM ``Bounds.mk #[timeFn, peak])
  setGoals [freshGoal]
  evalTactic (← `(tactic| intro v n hv; exact ⟨Nat.le_succ _, le_rfl⟩))
  setGoals (cases.toList.map (·.goal))
  evalTactic (← `(tactic| all_goals
    (simp +contextual (disch := omega) [Code.Bounded, Code.block, sourcePair, *] <;> omega)))
  let proof ← typedSourceProof (← instantiateMVars type) (← instantiateMVars certificate)
  let implementation ← mkAppOptM ``Implementation.ofImplements #[some inputType, some outputType,
    some inputInst, some outputInst, some f, some program, some bounds, some proof]
  -- The fixed number of controller steps is absorbed into the hidden coefficient.
  let value ← mkAppM ``Implementation.mono #[implementation,
    ← mkAppOptM ``Dominated.const #[some inputType, some time], ← mkAppM ``Dominated.refl #[peak]]
  assignImplementation goal value
  setGoals rest

/-- Certify a finite source case split with structural branch results. -/
syntax (name := sourceCasesTactic) "source_cases" : tactic
private structure Call where
  argument : TreeProgram.Expr Unit
  implementation : Lean.Expr

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
    return (← `(callCode ($h).program $e), ← `(fun n => ($h).callCode_fresh $e n))
  | .branch e yes no =>
    let (yes, fresh) ← compileCalls yes v
    let (no, _) ← compileCalls no v
    let e ← exprSyntax e v
    return (← `((⟨fun n => (.var n,
      max (($yes).build n).2.1 (($no).build n).2.1,
      [Cmd.branch $e (Code.block (($yes).build n).2.2)
        (Code.block (($no).build n).2.2)])⟩ : Code Value)),
      ← ``(fun n => Nat.le_trans (($fresh) n) (Nat.le_max_left _ _)))

/-- Each branch is charged its callee's growth at the branch argument. The certificate scales
all callees and fixed controller steps by one coefficient chosen after the callees'. -/
private def sourceCalls (certify : Lean.Expr → MetaM Lean.Expr) :
    TacticM Unit := withMainContext do
  trace[source.translation] "analyze call branches"
  let goal ← getMainGoal
  let rest := (← getGoals).tail
  let #[inputType, outputType, inputInst, outputInst, f, _, _] ← sourceGoalArgs goal |
    throwError "source calls: invalid source arguments"
  if let .const name _ := f.eta.getAppFn then
    if ← isRecursiveDefinition name then
      Search.unsupported (Search.recursionMessage name)
  let outer ← getLCtx
  let outerInstances ← getLocalInstances
  let nat := mkConst ``Nat
  let costs ← mkFreshExprMVar
    (← mkArrow inputType (← mkAppM ``Prod #[nat, ← mkAppM ``Prod #[nat, nat]]))
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
      let implementation ← withLCtx outer outerInstances (certify branch)
      let specification ← inferType implementation
      unless specification.isAppOfArity ``Implementation 7 do
        throwError "source calls: expected a certified implementation"
      let escapes := fun e : Lean.Expr =>
        (collectFVars {} e).fvarIds.any (!outer.contains ·)
      if escapes specification || escapes implementation then
        for e in #[specification, implementation] do
          for id in (collectFVars {} e).fvarSet do
            unless outer.contains id do
              trace[source.translation] "escaping variable: {mkFVar id} : {← inferType (mkFVar id)}"
        Search.unsupported "source calls: branch certificate depends on runtime data"
      let ri := (← simp inputCode ctx.ctx ctx.simprocs).1
      trace[source.translation] "extract branch argument"
      let code ← mkAppM ``encode #[mkConst ``Tree, value]
      let rv := (← simp code ctx.ctx ctx.simprocs).1
      let (tests, fields) := inputLayout ri.expr
      let argument ← outputExpr rv.expr fields
      -- The callee's growth is charged at its argument. Stored input and argument sizes are
      -- kept apart from the callee's peak, which alone is scaled by the coefficient.
      let time ← mkAppM ``HAdd.hAdd
        #[(mkApp specification.getAppArgs[5]! value).headBeta, mkNatLit 1]
      let storage ← mkAppM ``max #[← mkAppM ``Tree.size #[inputCode], ← mkAppM ``Tree.size #[code]]
      let peak := (mkApp specification.getAppArgs[6]! value).headBeta
      let cost ← mkAppM ``Prod.mk #[time, ← mkAppM ``Prod.mk #[storage, peak]]
      g.assign cost
      return (⟨tests, ⟨argument, implementation⟩, g, value, inputCode, out, cost⟩ : CallCase)
    return (budgetGoal, choices)
  let tree ← dispatchCases (choices.map fun c => (c.tests, c.call))
  let v := mkIdent (← mkFreshUserName `input)
  let (body, fresh) ← compileCalls tree v
  let rec testTime : Dispatch Call → Nat
    | .leaf _ => 0
    | .branch e yes no => e.steps + 1 + max (testTime yes) (testTime no)
  let overhead := testTime tree +
    choices.foldl (fun n c => max n (c.call.argument.assignSteps + 2)) 0 + 1
  let costs ← instantiateMVars costs
  let (time, storage, calls) ← withLocalDeclD `x inputType fun x => do
    let cost := (mkApp costs x).headBeta
    let rest ← mkAppM ``Prod.snd #[cost]
    return (← mkLambdaFVars #[x] (← mkAppM ``Prod.fst #[cost]),
      ← mkLambdaFVars #[x] (← mkAppM ``Prod.fst #[rest]),
      ← mkLambdaFVars #[x] (← mkAppM ``Prod.snd #[rest]))
  let peak ← withLocalDeclD `x inputType fun x => do
    mkLambdaFVars #[x] (← mkAppM ``max #[(mkApp storage x).headBeta, (mkApp calls x).headBeta])
  let program ← Term.elabTerm (← `(fun $v : Value => $body)) none
  let constructor ← mkAppOptM ``Implementation.mk #[some inputType, some outputType, some inputInst,
    some outputInst, some f, some time, some peak, some program]
  let soundGoal ← mkFreshExprSyntheticOpaqueMVar (← whnf (← inferType constructor)).bindingDomain!
  -- One coefficient covers every callee and every fixed controller step.
  let mut callees : Array (Lean.Expr × Ident) := #[]
  for c in choices do
    unless callees.any (·.1 == c.call.implementation) do
      callees := callees.push (c.call.implementation, mkIdent (← mkFreshUserName `source_call))
  let coefficients ← callees.mapM fun _ => return mkIdent (← mkFreshUserName `source_coeff)
  setGoals [soundGoal.mvarId!]
  let storageTerm ← Term.exprToSyntax storage
  let callsTerm ← Term.exprToSyntax calls
  evalTactic (← `(tactic|
    refine Implementation.sound_of_mul_max (s := $storageTerm) (q := $callsTerm) ?_))
  for (implementation, h) in callees, C in coefficients do
    -- Eliminate the existential directly: `obtain` would re-elaborate the callee and
    -- re-check the large program goal, which is very slow for dependent input types.
    let type ← whnfR (← inferType implementation)
    let coefficient ← mkAppOptM ``Implementation.exists_implements_mul
      ((type.getAppArgs.push implementation).map some)
    let some (_, predicate) := (← whnfR (← inferType coefficient)).app2? ``Exists |
      throwError "source calls: unexpected callee coefficient {coefficient}"
    let goal ← getMainGoal
    let next ← goal.withContext do
      let target ← goal.getType
      let body ← withLocalDeclD C.getId (mkConst ``Nat) fun c => do
        mkForallFVars #[c] (← mkArrow (predicate.beta #[c]) target)
      let next ← mkFreshExprSyntheticOpaqueMVar body
      goal.assign (← mkAppM ``Exists.elim #[coefficient, next])
      return next.mvarId!
    replaceMainGoal [next]
    evalTactic (← `(tactic| intro $C:ident $h:ident))
  let total ← coefficients.foldlM (fun s C => `($s + $C)) (quote overhead)
  evalTactic (← `(tactic| refine ⟨$total, ?_⟩))
  let certificate ← getMainGoal
  let coefficient ← certificate.withContext do
    let bounds := (← instantiateMVars (← certificate.getType)).appArg!
    lambdaTelescope bounds.getAppArgs[1]! fun _ body => return body.getAppArgs[4]!
  withMainContext do
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
        let time ← mkAppM ``HMul.hMul #[coefficient, selected.getAppArgs[2]!]
        let split := selected.getAppArgs[3]!
        let space ← mkAppM ``max #[split.getAppArgs[2]!,
          ← mkAppM ``HMul.hMul #[coefficient, split.getAppArgs[3]!]]
        let target := mkAppN target.getAppFn
          (target.getAppArgs.set! 4 time |>.set! 5 space)
        let g ← g.replaceTargetDefEq target
        let some (_, h) := callees.find? (·.1 == branch.call.implementation) |
          throwError "source calls: missing callee certificate"
        return (g, branch.call, h, subst.apply branch.value, space, inputCode, equations)
    for (g, c, h, value, space, inputCode, equations) in proofCases do
      setGoals [g]
      tryCatch (withoutRecover <| withMainContext do
        let v ← Term.exprToSyntax (mkFVar locals[0]!)
        let e ← exprSyntax c.argument v
        let n ← Term.exprToSyntax (mkFVar locals[1]!)
        let s ← Term.exprToSyntax (mkFVar locals[2]!)
        let value ← Term.exprToSyntax value
        let space ← Term.exprToSyntax space
        let inputCode ← Term.exprToSyntax inputCode
        let coefficient ← Term.exprToSyntax coefficient
        let outputEq ← Term.exprToSyntax equations[2]!
        let equations ← equations.mapM fun equation => do
          let term ← Term.exprToSyntax equation
          `(Lean.Parser.Tactic.simpLemma| $term:term)
        trace[source.translation] "verify compiled call branch"
        -- Use the concrete encoding equations already obtained for this branch. Matching
        -- the generic injection projection here can launch an expensive inverse-law discharge.
        evalTactic (← `(tactic|
          (have source_call := Implements.callCode_bounded ($h $coefficient (by omega))
            $e $n $s $value (space := $space)
            (by simp [-UniqueEncoding.ofLeftInjection_encode, -sup_of_le_left, -sup_of_le_right,
              -Nat.max_eq_left, -Nat.max_eq_right, sourcePair, $equations,*] <;> rfl)
            (by
              apply le_trans (b := max ($inputCode).size (encode Tree $value).size)
              · simp [-UniqueEncoding.ofLeftInjection_encode, -sup_of_le_left, -sup_of_le_right,
                  -Nat.max_eq_left, -Nat.max_eq_right, sourcePair, $equations,*] <;> omega
              · exact Nat.le_max_left _ _)
            (Nat.le_max_right _ _))))
        -- The selected callee certificate is in `source_call`; the others must not drive `simp`.
        evalTactic (← `(tactic| clear $(callees.map (·.2)):ident*))
        trace[source.translation] "simplify compiled call branch"
        if choices.size == 1 then
          let steps := quote c.argument.assignSteps
          evalTactic (← `(tactic|
            (have source_steps : ($e).assignSteps = $steps := by simp
             apply source_call.mono (by simp only [Nat.mul_add, Nat.mul_one]; omega) le_rfl
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
                 Nat.mul_add, Nat.mul_one, $equations,*]
               at source_call ⊢
             all_goals (repeat' apply And.intro)
             all_goals (first
               | exact source_call.mono (by omega) le_rfl (fun _ h => h)
               | omega)))))
        fun ex =>
          Search.unsupported m!"source calls: branch verification failed: {ex.toMessageData}"
      unless (← getGoals).isEmpty do throwError "source calls: failed to verify branch"
  assignImplementation goal (mkApp constructor (← instantiateMVars soundGoal))
  setGoals rest

end FiniteCases
open Lean Meta in
/-- An implementation request whose growth is left to the selected rules. -/
def implementationGoal (f : Lean.Expr) : MetaM Lean.Expr := do
  let growth ← mkArrow (← whnf (← inferType f)).bindingDomain! (mkConst ``Nat)
  mkAppM ``Implementation #[f, ← mkFreshExprMVar growth, ← mkFreshExprMVar growth]

open Lean Meta in
/-- Close an implementation request. Growth placeholders take the produced growth; a stated
growth leaves the two `Dominated` comparisons for the same program. -/
def finishImplementation (goal : MVarId) (result : Lean.Expr) : MetaM (List MVarId) :=
    goal.withContext do
  let target := (← whnfR (← instantiateMVars (← goal.getType))).consumeMData
  let actual := (← whnfR (← instantiateMVars (← inferType result))).consumeMData
  unless target.isAppOfArity ``Implementation 7 && actual.isAppOfArity ``Implementation 7 do
    throwError "source translation: expected an Implementation goal, got {target} and {actual}"
  let mut obligations := []
  let mut comparisons := #[]
  for i in [5, 6], tag in [`time, `peak] do
    let requested := target.getAppArgs[i]!
    -- Structural growth is shown with beta redexes and constructor projections reduced.
    let produced := (← dsimp actual.getAppArgs[i]! (← Simp.mkContext
      (config := { zeta := false, zetaDelta := false, iota := false }))).1
    -- A named growth placeholder takes the produced growth, like an anonymous one.
    if let .mvar id := requested then
      unless ← id.isAssigned do id.assign produced
    if ← withReducible (isDefEq requested produced) then
      comparisons := comparisons.push (← mkAppM ``Dominated.refl #[produced])
    else
      let h ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``Dominated #[produced, requested])
        (tag := tag)
      comparisons := comparisons.push h
      obligations := obligations ++ [h.mvarId!]
  let value ← if obligations.isEmpty then pure result
    else mkAppM ``Implementation.mono #[result, comparisons[0]!, comparisons[1]!]
  unless ← isDefEq (← goal.getType) (← inferType value) do
    throwError "source translation: the implementation does not match the requested source"
  goal.assign value
  return obligations

open Lean Meta Elab Tactic in
private def sourceCallsWith (query : Lean.Expr → MetaM (Option Lean.Expr)) : TacticM Unit :=
  FiniteCases.sourceCalls fun f => do
    let some implementation ← query (← implementationGoal f) |
      Search.unsupported m!"source calls: no implementation for branch {f}"
    instantiateMVars implementation

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
  unless goal.isAppOfArity ``Implementation 7 do return none
  if goal.getAppArgs[4]!.hasExprMVar then return none
  let locals := (← getLCtx).foldl (fun ds d => d :: ds) []
  for decl in locals do
    if decl.kind == .auxDecl then continue
    let type ← instantiateMVars decl.type
    unless type.isAppOfArity ``Implementation 7 do continue
    if let some result ← Search.attempt unfolded do
        if ← withReducible (isDefEq type goal) then return some ⟨decl.toExpr⟩
        return none then
      return some result
  return none
open Lean Meta in
private def typedSourceImplementation (target implementation : Lean.Expr) : MetaM Lean.Expr := do
  unless target.isAppOfArity ``Implementation 7 do return implementation
  let actual ← inferType implementation
  if ← withReducible (isDefEq actual target) then return implementation
  unless ← withDefault (isDefEq actual target) do
    throwError "source translation: the implementation has a different source type or encoding"
  let source := actual.getAppArgs[4]!
  let desired := (← instantiateMVars target).getAppArgs[4]!
  let equality ← typedSourceProof (← mkEq source desired) (← mkEqRefl source)
  mkAppM ``Implementation.congr #[implementation, equality]

open Lean in
/-- Growth arguments are results of a query, so they do not distinguish cached requests. -/
private def implementationKey (goal : Lean.Expr) : Lean.Expr :=
  if goal.isAppOfArity ``Implementation 7 then mkAppN goal.getAppFn (goal.getAppArgs.extract 0 5)
  else goal

open Lean Meta Elab Tactic Mathlib.Meta.FunProp in
private partial def sourceSearch (session : Search.Session) (nested : Bool)
    (ancestors : Array Lean.Expr) (goal : Lean.Expr) : FunPropM (Option Result) := do
  let unfolded := session.unfolded
  let goal ← instantiateMVars goal
  trace[source.translation] "implementation query: {goal}"
  session.step
  trace[Meta.Tactic.fun_prop] "source step {← session.steps.get}: {goal}"
  if let some result ← localSourceCertificate unfolded goal then return some result
  let key := implementationKey goal
  if let some { proof? := some proof, .. } := (← get).cache.find? key then
    if ← isDefEq goal (← inferType proof) then return some ⟨proof⟩
  -- Only requests with unconstrained growth are failures of the source function itself.
  let unconstrained := !goal.isAppOfArity ``Implementation 7 ||
    (goal.getAppArgs[5]!.isMVar && goal.getAppArgs[6]!.isMVar)
  if unconstrained && (← get).failureCache.contains key then return none
  if ancestors.contains key then return none
  let ancestors := ancestors.push key
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
      return some (← cacheResult key { r with proof })
    restore
    if unconstrained then cacheFailure key
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
open Lean Meta Elab Tactic Mathlib.Meta.FunProp in
def withSourceSpecs {α : Type} (scope : Option Ident) (action : TacticM α) : TacticM α := do
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
/-- Certify a callback named in a method syntax completely, sharing the method's session.
The source rules in scope are those activated by `withSourceSpecs`. -/
def certifyCallback (session : Search.Session) (method name : Name) (callback : Lean.Expr) :
    TacticM Lean.Expr := do
  if callback.hasExprMVar then
    throwError "source {method}: provide a concrete `{name}` callback"
  session.failure.set none
  let some proof ← sourceQuery (sourceSearch session false #[]) (← sourceContext)
      (← implementationGoal callback) |
    try session.report catch ex => throwError "source {method} `{name}`: {ex.toMessageData}"
  let proof ← instantiateMVars proof
  if proof.hasExprMVar || proof.hasSorry then
    throwError "source {method}: the `{name}` callback has unfinished obligations"
  trace[source.translation] "source {method}: translating {name} complete"
  return proof

open Lean Elab Tactic in
/-- Elaborate a user-supplied source term. Its errors are reported, never replaced by `sorry`. -/
def elabSourceTerm (stx : Syntax) (type : Lean.Expr) : TacticM Lean.Expr :=
  Term.withoutErrToSorry <| elabTermEnsuringType stx type

open Lean Meta Elab Tactic Mathlib.Meta.FunProp in
/-- Translate the main `Implementation` goal and return the remaining obligations. -/
private def proveSource (scope : Option Ident := none) (replacement : Option Term := none) :
    TacticM (List MVarId) :=
    withSourceSpecs scope <| withMainContext do
  let goal ← getMainGoal
  let saved ← saveState
  let session ← Search.Session.create
  let context ← sourceContext
  try
    let original := (← instantiateMVars (← goal.getType)).consumeMData
    unless original.isAppOfArity ``Implementation 7 do
      throwError "source_fun_prop expects an Implementation goal, got {original}"
    let f := original.getAppArgs[4]!
    let (source, equality) ← match replacement with
      | none => pure (f, none)
      | some replacement =>
        let g ← elabSourceTerm replacement (← inferType f)
        Term.synthesizeSyntheticMVarsNoPostponing
        let g ← instantiateMVars g
        if g.hasExprMVar then
          throwError "provide a concrete source function after `via`"
        let h ← mkFreshExprSyntheticOpaqueMVar (← mkEq f g) (tag := `source_eq)
        pure (g, some h)
    let growth ← mkArrow original.getAppArgs[0]! (mkConst ``Nat)
    let target := (original.setArg 4 source).setArg 5 (← mkFreshExprMVar growth)
      |>.setArg 6 (← mkFreshExprMVar growth)
    let some result ← sourceQuery (sourceSearch session false #[]) context target |
      session.report
    let result ← match equality with
      | none => pure result
      | some h => mkAppM ``Implementation.congr #[result, ← mkEqSymm h]
    let obligations ← finishImplementation goal result
    replaceMainGoal []
    return equality.toList.map (·.mvarId!) ++ obligations
  catch ex =>
    saved.restore
    throw ex

/-- A recursion method supplies ordinary callbacks and a decreasing measure. -/
declare_syntax_cat sourceRecursion
syntax "recursion" " (" &"test" " := " term ")" " (" &"next" " := " term ")"
  " (" &"finish" " := " term ")" " (" &"resume" " := " term ")"
  " (" &"measure" " := " term ")" " (" &"decreases" " := " term ")" : sourceRecursion

open Lean Meta Elab Tactic Mathlib.Meta.FunProp in
private def proveRecursion (method : TSyntax `sourceRecursion) (scope : Option Ident := none) :
    TacticM (List MVarId) :=
    withSourceSpecs scope <| withMainContext do
  let `(sourceRecursion| recursion (test := $test) (next := $next)
    (finish := $finish) (resume := $resume) (measure := $measure) (decreases := $decreases)) :=
    method | throwUnsupportedSyntax
  let goal ← getMainGoal
  let rest := (← getGoals).drop 1
  let args ← sourceGoalArgs goal
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
    let value ← elabSourceTerm value (← inferType fields[index]!)
    fields[index]!.mvarId!.assign value
  Term.synthesizeSyntheticMVarsNoPostponing
  fields[9]!.mvarId!.assign (← elabSourceTerm measure allowanceType)
  fields[10]!.mvarId!.assign (← elabSourceTerm decreases (← inferType fields[10]!))
  Term.synthesizeSyntheticMVarsNoPostponing
  let mut obligations := []
  for (index, tag) in #[(7, `finish_eq), (8, `resume_eq)] do
    let h ← mkFreshExprSyntheticOpaqueMVar (← instantiateMVars (← inferType fields[index]!))
      (tag := tag)
    fields[index]!.mvarId!.assign h
    obligations := obligations ++ [h.mvarId!]
  let r ← instantiateMVars r
  let session ← Search.Session.create
  let certify := certifyCallback session `recursion
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
  let actual := (← inferType implementation).getAppArgs[4]!
  let equality ← withLocalDeclD `x args[0]! fun x => do
    let lhs ← mkAppM ``encode #[mkConst ``Tree, mkApp source x]
    let rhs ← mkAppM ``encode #[mkConst ``Tree, mkApp actual x]
    let proof ← typedSourceProof (← mkEq lhs rhs) (← mkEqRefl lhs)
    mkLambdaFVars #[x] proof
  let result ← mkAppM ``Implementation.ofEncode #[equality, implementation]
  let comparisons ← finishImplementation goal result
  trace[source.translation] "source recursion: program combined"
  setGoals rest
  return obligations ++ comparisons
open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| source_fun_prop $[using $scope:ident]? $[via $replacement]?) => do
    let obligations ← proveSource scope replacement
    setGoals (obligations ++ (← getGoals))
open Lean Meta Elab Tactic in
/-- Run a structural translation for the main goal's source function, then compare its growth
with the stated one. -/
private def withFreshGrowth (action : TacticM Unit) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let rest := (← getGoals).tail
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOfArity ``Implementation 7 do
    throwError "expected an Implementation goal, got {target}"
  let growth ← mkArrow target.getAppArgs[0]! (mkConst ``Nat)
  let fresh ← mkFreshExprSyntheticOpaqueMVar ((target.setArg 5 (← mkFreshExprMVar growth)).setArg
    6 (← mkFreshExprMVar growth))
  setGoals [fresh.mvarId!]
  action
  let obligations ← finishImplementation goal (← instantiateMVars fresh)
  setGoals (obligations ++ rest)
open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| source_cases) => withFreshGrowth FiniteCases.sourceCases
  | `(tactic| source_calls) => withSourceSpecs none <| withFreshGrowth <| withMainContext do
    let session ← Search.Session.create
    let goal ← getMainGoal
    let target ← goal.getType
    let query := sourceQuery (sourceSearch session true #[target]) (← sourceContext)
    let some proof ← session.discharge #[target] (sourceCallsWith query) target | session.report
    goal.assign proof
    replaceMainGoal []
open Lean Meta Elab Tactic in
/-- Translate a source function and reduce its model time-space bound to arithmetic goals. -/
private def modelFunPropCore (translate : TacticM (List Lean.MVarId)) : TacticM Unit := do
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
    evalTactic (← `(tactic| refine Implementation.computableWithGrowth_of_dominated
      (hf := ?implementation) (t := ?time_bound) (p := ?peak_bound) ?time ?peak))
  else if let some (t, s) := powers then
    evalTactic (← `(tactic| refine Implementation.mem_ftisp_pow
      (hf := ?implementation) (t := $(quote t)) (s := $(quote s)) (by decide)))
  else
    evalTactic (← `(tactic| refine Implementation.mem_ftisp_of_dominated
      (hf := ?implementation) (t := ?time_bound) (p := ?peak_bound) ?time ?peak))
  let pending ← getGoals
  let some implementation ← pending.findM? fun g =>
      return (← g.getType).consumeMData.isAppOf ``Implementation |
    throwError "source model: missing implementation"
  setGoals [implementation]
  let obligations ← translate
  let remaining ← (pending.erase implementation).filterM fun g => return !(← g.isAssigned)
  setGoals (obligations ++ remaining ++ originalGoals.drop 1)

open Lean Elab Tactic in
def modelFunProp (translate : TacticM (List Lean.MVarId)) : TacticM Unit := do
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
    let obligations ← proveRecursion method scope
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

open Lean Meta in
/-- One selected implementation per source function; a second one would make calls ambiguous. -/
private def checkUniqueSource (name : Name) : MetaM Unit := do
  let function (name : Name) : MetaM Lean.Expr := do
    let (_, _, type) ← forallMetaTelescopeReducing (← inferType (← mkConstWithFreshMVarLevels name))
    return type.getAppArgs[4]!
  for other in sourceSavedImplementationExt.getState (← getEnv) do
    if ← withNewMCtxDepth <| withReducible do isDefEq (← function name) (← function other) then
      throwError "`source` already has a selected implementation of {← function name}: \
        {.ofConstName other}; choose another one at a call with a local hypothesis or `via`"

/-- Save a source implementation for later translations: either a named implementation, or
the implementation of an equality's right-hand side for its left-hand side. Local and scoped
registrations use `fun_prop`; `using ns` selects rules for an equality. -/
syntax (name := sourceAttribute) "source" (" using " ident)? : attr

open Lean Meta Elab Tactic Mathlib.Meta.FunProp in
initialize registerBuiltinAttribute {
  name := `sourceAttribute
  descr := "save a source implementation for later translations"
  applicationTime := .afterCompilation
  add := fun name stx kind => MetaM.run' do
    let saved ← getEnv
    try
      let `(attr| source $[using $scope:ident]?) := stx | throwUnsupportedSyntax
      let info ← getConstInfo name
      if ← forallTelescope info.type fun _ type =>
          return type.isAppOfArity ``Implementation 7 then
        if scope.isSome then
          throwError "`source using` selects rules for a function equality"
        checkUniqueSource name
        sourceSavedImplementationExt.add name kind
        addTheorem name kind 1001
        return
      let equality := mkConst name (info.levelParams.map mkLevelParam)
      forallTelescope info.type fun parameters type =>
        withSourceEncodings parameters.toList do
          for parameter in parameters do
            let parameterDecl ← parameter.fvarId!.getDecl
            if !parameterDecl.binderInfo.isInstImplicit && (← isProp parameterDecl.type) then
              throwError "`source` needs an unconditional function equality; \
                use a local `via` proof for a replacement depending on a hypothesis"
          let some (_, _, g) := type.eq? |
            throwError "`source` expects a function equality or a named implementation"
          unless (← whnf (← inferType g)).isForall do
            throwError "`source` expects a function equality; use `funext` for pointwise equations"
          let goal ← mkFreshExprSyntheticOpaqueMVar (← implementationGoal g)
          let action : TermElabM Unit := do
            discard <| Tactic.run goal.mvarId! do
              discard <| proveSource scope
          discard <| action.run {} {}
          let proof ← instantiateMVars goal
          if proof.hasExprMVar || proof.hasSorry then
            throwError "the selected source implementation has unfinished obligations"
          let result ← mkAppM ``Implementation.congr
            #[proof, ← mkEqSymm (mkAppN equality parameters)]
          let certificate ← withoutExporting do
            let certificate ← mkAuxDefinition (← mkFreshUserName (name ++ `sourceImplementation))
              (← inferType result) result (compile := false)
            modifyEnv (addNoncomputable · certificate.getAppFn.constName!)
            pure certificate.getAppFn.constName!
          checkUniqueSource certificate
          sourceSavedImplementationExt.add certificate kind
          addTheorem certificate kind 1001
    catch ex =>
      setEnv saved
      throw ex
}

end Complexity.TreeProgram.Source
