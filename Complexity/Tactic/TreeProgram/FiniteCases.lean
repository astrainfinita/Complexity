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
public meta import Lean.Meta.Match.MatcherApp.Transform
public meta import Lean.Meta.RecExt

/-! # Finite source cases and source call branches

`source_cases` compiles a source function with finitely many cases on the shape of its encoded
input into one program; `source_calls` certifies the branches of a source function with the
implementations selected for its callees.
-/

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

/-- The tree a closed tree term evaluates to at default transparency. A finite source case is a
table on the shape of the input, so a closed value in it is a constant of the table, computed by
the translation rather than by the program. -/
partial def closedTree (t : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let t ← withTransparency .default <| whnf t
  match t.getAppFn.constName?, t.getAppArgs with
  | some ``BinaryTree.nil, _ => return mkConst ``Tree.nil
  | some ``BinaryTree.node, #[_, _, l, r] =>
    let some l ← closedTree l | return none
    let some r ← closedTree r | return none
    return mkApp2 (mkConst ``Tree.pair) l r
  | _, _ => return none

/-- The code of a closed value, as a constant tree of a finite source case. -/
simproc_decl sourceConstant (encode Tree _) := fun e => do
  unless e.isAppOfArity ``UniqueEncoding.encode 4 && !e.hasFVar && !e.hasMVar do return .continue
  let some t ← closedTree e | return .continue
  return .done { expr := t }

end FiniteCases
open Lean Meta in
/-- `proof` as a proof of `type`: itself when the types agree reducibly, otherwise an auxiliary
theorem stated at `type`, which the kernel checks. -/
def typedSourceProof (type proof : Lean.Expr) : MetaM Lean.Expr := do
  if ← withReducible (isDefEq type (← inferType proof)) then return proof
  mkAuxTheorem type proof
open Lean Meta Elab Tactic in
/-- The arguments of a goal `HasProgram f program time peak`, with its implicit types and
encodings. -/
def sourceGoalArgs (goal : MVarId) : MetaM (Array Lean.Expr) := do
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOfArity ``HasProgram 8 do
    throwError "source translation: expected HasProgram, got {target}"
  return target.getAppArgs
open Lean Meta in
/-- Assign a translation result, unifying the requested program and growth with the produced
ones. -/
private def assignResult (goal : MVarId) (value : Lean.Expr) : MetaM Unit := do
  unless ← isDefEq (← goal.getType) (← inferType value) do
    Search.unsupported m!"source translation: the produced growth does not match the request"
  goal.assign value
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

/-- The values a `match`, `casesOn` or non-recursive `rec` at the head of `e` inspects (through
the matcher's own definition), or the structure a projection at the head reads. -/
partial def caseDiscriminators (e : Lean.Expr) (fromMatcher := false) :
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

/-- The lemmas registered with `source_case_simp`, `sourcePair` and `sourceConstant`, as `simp`
arguments, so that they are one index rather than an index per set. -/
private def caseLemmas : MetaM (Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) := do
  let lemmas ← (← Growth.attrDecls `source_case_simp).mapM fun (n, inv) =>
    if inv then `(Lean.Parser.Tactic.simpLemma| ← $(mkCIdent n):term)
    else `(Lean.Parser.Tactic.simpLemma| $(mkCIdent n):term)
  return lemmas ++ #[← `(Lean.Parser.Tactic.simpLemma| sourcePair),
    ← `(Lean.Parser.Tactic.simpLemma| sourceConstant)]

private def caseEquations (g : MVarId) (f outputType outputInst : Lean.Expr)
    (decl : LocalDecl) (inputCode out : Lean.Expr)
    (ctx : Simp.Context) (procs : Simp.SimprocsArray) :
    MetaM (Lean.Expr × Lean.Expr × MVarId × Array Lean.Expr) := do
  let input := inputCode.appArg!
  -- The output type may depend on the input.
  let outputType := outputType.beta #[input]
  let outputInst := outputInst.beta #[input]
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

/-- Compile a source function with finitely many cases on the shape of its encoded input: tests
on the input tree select the case, and the output is built from constants and input subtrees. -/
def sourceCases : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let rest := (← getGoals).tail
  let #[inputType, outputType, inputInst, outputInst, f, _, _, _] ← sourceGoalArgs goal |
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
  let ctx ← mkSimpContext (← `(tactic| simp [$(← caseLemmas),*])) false
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
      #[some (mkConst ``Tree), some (outputType.beta #[x]), some (outputInst.beta #[x]),
        some (mkApp f x).headBeta]
    let peak ← mkAppM ``max #[← mkAppM ``Tree.size #[input], ← mkAppM ``Tree.size #[output]]
    return (← mkLambdaFVars #[x] time, ← mkLambdaFVars #[x] peak)
  bounds.mvarId!.assign (← mkAppM ``Bounds.mk #[timeFn, peak])
  setGoals [freshGoal]
  evalTactic (← `(tactic| intro v n hv; exact ⟨Nat.le_succ _, le_rfl⟩))
  setGoals (cases.toList.map (·.goal))
  evalTactic (← `(tactic| all_goals
    (simp +contextual (disch := omega)
      [Code.Bounded, Code.block, sourcePair, *] <;> omega)))
  let proof ← typedSourceProof (← instantiateMVars type) (← instantiateMVars certificate)
  let certified ← mkAppM ``HasProgram.ofImplements #[bounds, proof]
  -- The fixed number of controller steps is absorbed into the hidden coefficient.
  let value ← mkAppM ``HasProgram.mono #[certified,
    ← mkAppOptM ``Dominated.const #[some inputType, some time], ← mkAppM ``Dominated.refl #[peak]]
  assignResult goal value
  setGoals rest

/-- Certify a finite source case split with structural branch results. -/
syntax (name := sourceCasesTactic) "source_cases" : tactic
private structure Call where
  argument : TreeProgram.Expr Unit
  certificate : Lean.Expr
  program : Lean.Expr

private structure CallCase where
  tests : List (List Bool × Bool)
  call : Call
  goal : MVarId
  value : Lean.Expr
  inputCode : Lean.Expr
  output : Lean.Expr
  cost : Lean.Expr

/-- A leaf of the call analysis, with the values there of the variables bound on the way to it,
starting with the input. -/
private structure CallLeaf where
  goal : MVarId
  inputCode : Lean.Expr
  output : Lean.Expr
  bindings : Array (Lean.Expr × Lean.Expr)

/-- An expression of a source branch, read in a leaf of the branch. -/
private def CallLeaf.inLeaf (leaf : CallLeaf) (e : Lean.Expr) : Lean.Expr :=
  e.replaceFVars (leaf.bindings.map (·.1)) (leaf.bindings.map (·.2))

/-- The values in a leaf of an alternative's parameters, if the leaf's discriminants match the
alternative's patterns. Parameters that the leaf does not determine are `none`. -/
private def leafAlternative (leaf : CallLeaf) (discrs patterns : Array Lean.Expr) :
    MetaM (Option (Array (Option Lean.Expr))) := leaf.goal.withContext do
  let some first := patterns[0]? | return none
  let saved ← saveState
  try
    let (params, _, _) ← lambdaMetaTelescope (leaf.inLeaf first)
    for discr in discrs, pattern in patterns do
      unless ← isDefEq ((leaf.inLeaf pattern).beta params) (leaf.inLeaf discr) do return none
    -- Thunks take `()`; the equations of `match h : e with` hold by reduction in the leaf.
    for p in params do
      unless ← p.mvarId!.isAssigned do
        let type ← instantiateMVars (← inferType p)
        if type.isConstOf ``Unit then discard <| isDefEq p (mkConst ``Unit.unit)
        else if let some (_, a, _) := type.eq? then discard <| isDefEq p (← mkEqRefl a)
        else if let some (_, a, _, _) := type.heq? then discard <| isDefEq p (← mkHEqRefl a)
    params.mapM fun p => do
      let p ← instantiateMVars p
      return if p.hasMVar then none else some p
  finally saved.restore

/-- `dsimp` reducing only projections of constructor applications. -/
private def fieldProjections : Simp.Config where
  beta := false
  eta := false
  etaStruct := .none
  iota := false
  zeta := false
  zetaDelta := false

/-- Rebind a branch's variables at the shape all its leaves give them, as the case analysis
does: a variable that every leaf builds with one structure constructor becomes its fields.
`k` receives the substitution of the variables and, for each new variable, its expression in the
variables and its values in the leaves. -/
private partial def withLeafShape {α : Type} (vars : List Lean.Expr) (leaves : List CallLeaf)
    (k : Array (Lean.Expr × Lean.Expr) →
      Array (Lean.Expr × Lean.Expr × List (Option Lean.Expr)) → MetaM α) : MetaM α :=
  go vars #[] #[]
where
  -- Only projections of constructor applications are reduced, as `cases` exposes them.
  reduce (e : Lean.Expr) : MetaM Lean.Expr := do
    return (← dsimp e (← Simp.mkContext (config := fieldProjections))).1
  go (vars : List Lean.Expr) (subst : Array (Lean.Expr × Lean.Expr))
      (fields : Array (Lean.Expr × Lean.Expr × List (Option Lean.Expr))) : MetaM α := do
    let v :: vars := vars | k subst fields
    let type ← reduce ((← inferType v).replaceFVars (subst.map (·.1)) (subst.map (·.2)))
    -- A variable a leaf does not determine, such as a proof bound by a pattern, has no value.
    let values ← leaves.mapM fun leaf => do
      unless leaf.bindings.any (·.1 == v) do return none
      leaf.goal.withContext do return some (← whnf (leaf.inLeaf v))
    bind (← v.fvarId!.getUserName) type v values fields fun term fields =>
      go vars (subst.push (v, term)) fields
  bind (name : Name) (type source : Lean.Expr) (values : List (Option Lean.Expr))
      (fields : Array (Lean.Expr × Lean.Expr × List (Option Lean.Expr)))
      (k : Lean.Expr → Array (Lean.Expr × Lean.Expr × List (Option Lean.Expr)) → MetaM α) :
      MetaM α := do
    let keep := withLocalDeclD name type fun x => k x (fields.push (x, source, values))
    let some values := values.mapM id | keep
    let some (Lean.Expr.const ctor levels) := values.head?.map (·.getAppFn) | keep
    let some (.ctorInfo info) := (← getEnv).find? ctor | keep
    unless values.all (·.getAppFn.isConstOf ctor) && !(← isProp type) do return ← keep
    let some structInfo := getStructureInfo? (← getEnv) info.induct | keep
    let .const _ _ := (← whnf type).getAppFn | keep
    let params := (← whnf type).getAppArgs.extract 0 info.numParams
    let rec fieldsOf (i : Nat) (ctorType : Lean.Expr) (terms : Array Lean.Expr)
        (fields : Array (Lean.Expr × Lean.Expr × List (Option Lean.Expr))) : MetaM α := do
      let .forallE _ fieldType rest _ := ctorType |
        k (mkAppN (mkConst ctor levels) (params ++ terms)) fields
      let fieldName := structInfo.fieldNames[i]!
      let fieldSource ← mkAppM (info.induct ++ fieldName) #[source]
      bind fieldName (← reduce fieldType) fieldSource
        (values.map (some ·.getAppArgs[info.numParams + i]!)) fields fun term fields =>
        fieldsOf (i + 1) (rest.instantiate1 term) (terms.push term) fields
    fieldsOf 0 (← instantiateForall (← inferType (mkConst ctor levels)) params) #[] fields

/-- Unfold a definition being translated; any other definition only as notation (reducible
definitions and instances), since its cost is that of its own selected implementation. -/
def unfoldSource? (roots : NameSet) (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let some name := e.getAppFn.constName? | return none
  if roots.contains name then unfoldDefinition? e
  else withReducibleAndInstances (unfoldDefinition? e)

/-- Unfold to the next `if` or `match` of a source branch, looking inside encoders; the type of
the encoded value, if an encoder was entered. -/
private partial def exposeBranch (roots : NameSet) (e : Lean.Expr) :
    MetaM (Option Lean.Expr × Lean.Expr) := do
  let e ← whnfCore e
  if e.isAppOfArity ``UniqueEncoding.encode 4 then
    return (some (e.getArg! 1), (← exposeBranch roots e.appArg!).2)
  if e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5 then return (none, e)
  if (← matchMatcherApp? e (alsoCasesOn := true)).isSome then return (none, e)
  let some e ← unfoldSource? roots e | return (none, e)
  exposeBranch roots e

/-- Follow the source's own `if` and `match` structure down to the branches separating the
leaves, as functional induction does (`Lean.Meta.FunInd`): each matcher keeps its discriminants
and patterns and gets the motive `ℕ`, and `tail` gives the value of a branch from its body, the
variables bound on the way (the input first) and its leaves. Under an entered encoder, a body is
encoded at its expected type: the source match's motive at the branch's patterns. -/
private partial def alongBranches (roots : NameSet)
    (tail : Lean.Expr → Array Lean.Expr → List CallLeaf → MetaM Lean.Expr)
    (encoded : Option Lean.Expr) (body : Lean.Expr) (vars : Array Lean.Expr)
    (leaves : List CallLeaf) : MetaM Lean.Expr := do
  let stop : MetaM Lean.Expr := do
    let body ← match encoded with
      | some type => mkAppOptM ``encode #[some (mkConst ``Tree), some type, none, some body]
      | none => pure body
    tail body vars leaves
  if leaves.isEmpty then return ← tail body vars []
  let nat := mkConst ``Nat
  let (entered, e) ← exposeBranch roots body
  let encoded := entered <|> encoded
  if e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5 then
    let #[_, c, h, yes, no] := e.getAppArgs | unreachable!
    let mut chosen : Array (Bool × CallLeaf × Lean.Expr) := #[]
    for leaf in leaves do
      let decision ← leaf.goal.withContext do whnf (leaf.inLeaf h)
      if decision.isAppOfArity ``Decidable.isTrue 2 then
        chosen := chosen.push (true, leaf, decision.appArg!)
      else if decision.isAppOfArity ``Decidable.isFalse 2 then
        chosen := chosen.push (false, leaf, decision.appArg!)
      else return ← stop
    let side (b : Bool) := (chosen.filter (·.1 == b)).toList.map (·.2)
    if e.isAppOfArity ``ite 5 then
      return mkApp5 (mkConst ``ite [1]) nat c h
        (← alongBranches roots tail encoded yes vars ((side true).map (·.1)))
        (← alongBranches roots tail encoded no vars ((side false).map (·.1)))
    let branch (b : Bool) (k : Lean.Expr) : MetaM Lean.Expr := do
      let .lam n t k bi := k | throwError "source calls: expected a branch abstraction"
      withLocalDecl n bi t fun hc => do
        let leaves := (side b).map fun (leaf, proof) =>
          { leaf with bindings := leaf.bindings.push (hc, proof) }
        mkLambdaFVars #[hc]
          (← alongBranches roots tail encoded (k.instantiate1 hc) (vars.push hc) leaves)
    return mkApp5 (mkConst ``dite [1]) nat c h (← branch true yes) (← branch false no)
  let some app ← matchMatcherApp? e (alsoCasesOn := true) | stop
  let patterns ← Growth.alternativePatterns app
  let matcher := mkAppN (mkConst app.matcherName app.matcherLevels.toList) app.params
  let types ← inferArgumentTypesN app.alts.size (mkAppN (mkApp matcher app.motive) app.discrs)
  let mut groups :=
    Array.replicate app.alts.size ([] : List (CallLeaf × Array (Option Lean.Expr)))
  for leaf in leaves do
    let some (i, values) ← (List.range app.alts.size).findSomeM? fun i => do
        return (← leafAlternative leaf app.discrs patterns[i]!).map (i, ·) | return ← stop
    groups := groups.modify i (· ++ [(leaf, values)])
  let app ← app.transform (onMotive := fun _ _ => pure nat) (onRemaining := fun _ => pure #[])
    (onAlt := fun i _ fvars alt => do
      let leaves := groups[i]!.map fun (leaf, values) => { leaf with
        bindings := leaf.bindings ++ (fvars.args.zip values).filterMap fun (y, v) => v.map (y, ·) }
      let encoded ← encoded.mapM fun _ => do
        let type ← instantiateForall types[i]! fvars.args
        return (← instantiateForall type app.remaining).headBeta
      alongBranches roots tail encoded (mkAppN alt app.remaining) (vars ++ fvars.args) leaves)
  return app.toExpr

private partial def compileCalls (p : Dispatch Call) (v : Term) :
    TermElabM (Term × Term) := do
  match p with
  | .leaf c =>
    let h ← Term.exprToSyntax c.certificate
    let program ← Term.exprToSyntax c.program
    let e ← exprSyntax c.argument v
    return (← `(callCode $program $e), ← `(fun n => ($h).callCode_fresh $e n))
  | .branch e yes no =>
    let (yes, fresh) ← compileCalls yes v
    let (no, _) ← compileCalls no v
    let e ← exprSyntax e v
    return (← `((⟨fun n => (.var n,
      max (($yes).build n).2.1 (($no).build n).2.1,
      [Cmd.branch $e (Code.block (($yes).build n).2.2)
        (Code.block (($no).build n).2.2)])⟩ : Code Value)),
      ← ``(fun n => Nat.le_trans (($fresh) n) (Nat.le_max_left _ _)))

open Lean Meta in
/-- The branches are verified from the certificates `h` of the callees alone: the programs of the
callees become variables, which `simp` does not look into. -/
private def generalizePrograms (goal : MVarId) (callees : Array (Call × Ident)) :
    MetaM MVarId := goal.withContext do
  let certificates ← callees.mapM fun (_, h) => return (← getLocalDeclFromUserName h.getId).fvarId
  let programs := callees.map fun (c, _) => ({ expr := c.program } : GeneralizeArg)
  return (← goal.generalizeHyp programs certificates).2.2

/-- Each branch is charged its callee's growth at the branch argument. The certificate scales
all callees and fixed controller steps by one coefficient chosen after the callees'. -/
def sourceCalls (roots : NameSet) (certify : Lean.Expr → MetaM Lean.Expr) :
    TacticM Unit := withMainContext do
  trace[source.translation] "analyze call branches"
  let goal ← getMainGoal
  let rest := (← getGoals).tail
  let #[inputType, outputType, inputInst, outputInst, f, _, _, _] ← sourceGoalArgs goal |
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
  let ctx ← mkSimpContext (← `(tactic| simp [$(← caseLemmas),*])) false
  let splits ← IO.mkRef (#[] : Array CaseSplit)
  let (budgetRoot, leaves) ← budgetGoal.withContext do
    let input ← mkAppOptM ``encode
      #[some (mkConst ``Tree), some inputType, some inputInst, some (mkFVar x)]
    let (_, budgetGoal) ← budgetGoal.note inputName (← mkEqRefl input)
    let leaves ← visitCases budgetGoal f inputName ctx.ctx ctx.simprocs (requireBranch := true)
      (record := fun goal major branches => splits.modify (·.push ⟨goal, major, branches⟩))
      fun g _ inputCode out => pure (g, inputCode, out)
    return (budgetGoal, leaves)
  -- As in functional induction, each branch of the source is one callee: its body, as a function
  -- of the variables bound on the way. A leaf calls it at the values these variables have there.
  let tails ← IO.mkRef (#[] : Array (Option (Lean.Expr × Lean.Expr)))
  let choices ← IO.mkRef (#[] : Array CallCase)
  let (time, storage, calls) ← withLocalDeclD `x inputType fun x => do
    let leaves := leaves.toList.map fun (goal, inputCode, output) =>
      ({ goal, inputCode, output, bindings := #[(x, inputCode.appArg!)] } : CallLeaf)
    let callee (body : Lean.Expr) (vars : Array Lean.Expr) (leaves : List CallLeaf) :
        MetaM Lean.Expr := do
      -- A branch without leaves is impossible.
      if leaves.isEmpty then
        tails.modify (·.push none)
        return mkNatLit 0
      -- The callee takes the fields the branch uses, as for a case split of its input.
      let (branch, value, fields) ← withLeafShape vars.toList leaves fun subst fields => do
        let mut body ← withLeafShape.reduce
          (body.replaceFVars (subst.map (·.1)) (subst.map (·.2)))
        -- An encoded result is stated by its constructor, as for a dependent encoder.
        if body.isAppOfArity ``UniqueEncoding.encode 4 then
          let source ← whnf body.appArg!
          if ← isConstructorApp source then
            body := mkAppN body.getAppFn (body.getAppArgs.set! 3 source)
        let (branch, value) ← branchFunction outer body
        let free := fields.map (·.1)
        return (branch, ← mkLambdaFVars free value,
          fields.map fun (_, source, values) => (source, values))
      trace[source.translation] "certify branch callback"
      let certificate ← withLCtx outer outerInstances (certify branch)
      let specification ← inferType certificate
      unless specification.isAppOfArity ``HasProgram 8 do
        throwError "source calls: expected a certified program"
      let escapes := fun e : Lean.Expr =>
        (collectFVars {} e).fvarIds.any (!outer.contains ·)
      if escapes specification || escapes certificate then
        for e in #[specification, certificate] do
          for id in (collectFVars {} e).fvarSet do
            unless outer.contains id do
              trace[source.translation] "escaping variable: {mkFVar id} : {← inferType (mkFVar id)}"
        Search.unsupported "source calls: branch certificate depends on runtime data"
      -- Shown without the type ascriptions of the packed environment.
      let shown := (value.beta (fields.map (·.1))).replace fun e =>
        if e.isAppOfArity ``id 2 then some e.appArg! else none
      tails.modify (·.push (some (certificate, ← mkLambdaFVars vars shown)))
      for leaf in leaves, i in [0:leaves.length] do
        leaf.goal.withContext do
        -- A variable without a value in the leaf leaves its own name, which is then rejected.
        let value := value.beta (fields.map fun ((source, values) : Lean.Expr × _) =>
          values[i]!.getD source)
        if (collectFVars {} value).fvarIds.any fun id => vars.any (·.fvarId! == id) then
          Search.unsupported "source calls: a branch uses a variable no case determines"
        let ri := (← simp leaf.inputCode ctx.ctx ctx.simprocs).1
        trace[source.translation] "extract branch argument"
        let code ← mkAppM ``encode #[mkConst ``Tree, value]
        let rv := (← simp code ctx.ctx ctx.simprocs).1
        let (tests, fields) := inputLayout ri.expr
        let argument ← outputExpr rv.expr fields
        -- The callee's growth is charged at its argument. Stored input and argument sizes are
        -- kept apart from the callee's peak, which alone is scaled by the coefficient.
        let time ← mkAppM ``HAdd.hAdd
          #[(mkApp specification.getAppArgs[6]! value).headBeta, mkNatLit 1]
        let storage ← mkAppM ``max
          #[← mkAppM ``Tree.size #[leaf.inputCode], ← mkAppM ``Tree.size #[code]]
        let peak := (mkApp specification.getAppArgs[7]! value).headBeta
        let cost ← mkAppM ``Prod.mk #[time, ← mkAppM ``Prod.mk #[storage, peak]]
        leaf.goal.assign cost
        choices.modify (·.push
          ⟨tests, ⟨argument, certificate, specification.getAppArgs[5]!⟩, leaf.goal, value,
            leaf.inputCode, leaf.output, cost⟩)
      mkAppM ``HAdd.hAdd #[(mkApp specification.getAppArgs[6]! shown).headBeta, mkNatLit 1]
    let time ← mkLambdaFVars #[x] (← alongBranches roots callee none (f.beta #[x]) #[x] leaves)
    -- The other components revisit the same branches, which now have their callees.
    let along (component : Lean.Expr → Lean.Expr → MetaM Lean.Expr) : MetaM Lean.Expr := do
      let next ← IO.mkRef 0
      let tail (_ : Lean.Expr) (vars : Array Lean.Expr) (_ : List CallLeaf) := do
        let some (certificate, value) := (← tails.get)[← next.modifyGet fun i => (i, i + 1)]! |
          return mkNatLit 0
        component (← inferType certificate) (value.beta vars)
      mkLambdaFVars #[x] (← alongBranches roots tail none (f.beta #[x]) #[x] leaves)
    let storage ← along fun _ value => do
      let input ← mkAppOptM ``encode
        #[some (mkConst ``Tree), some inputType, some inputInst, some x]
      mkAppM ``max #[← mkAppM ``Tree.size #[input],
        ← mkAppM ``Tree.size #[← mkAppM ``encode #[mkConst ``Tree, value]]]
    let calls ← along fun spec value => pure (mkApp spec.getAppArgs[7]! value).headBeta
    return (time, storage, calls)
  let choices ← choices.get
  let tree ← dispatchCases (choices.map fun c => (c.tests, c.call))
  let v := mkIdent (← mkFreshUserName `input)
  let (body, fresh) ← compileCalls tree v
  let rec testTime : Dispatch Call → Nat
    | .leaf _ => 0
    | .branch e yes no => e.steps + 1 + max (testTime yes) (testTime no)
  let overhead := testTime tree +
    choices.foldl (fun n c => max n (c.call.argument.assignSteps + 2)) 0 + 1
  let peak ← withLocalDeclD `x inputType fun x => do
    mkLambdaFVars #[x] (← mkAppM ``max #[(mkApp storage x).headBeta, (mkApp calls x).headBeta])
  let program ← Term.elabTerm (← `(fun $v : Value => $body)) none
  let soundGoal ← mkFreshExprSyntheticOpaqueMVar (← mkAppOptM ``HasProgram #[some inputType,
    some outputType, some inputInst, some outputInst, some f, some program, some time, some peak])
  -- One coefficient covers every callee and every fixed controller step.
  let mut callees : Array (Call × Ident) := #[]
  for c in choices do
    unless callees.any (·.1.certificate == c.call.certificate) do
      callees := callees.push (c.call, mkIdent (← mkFreshUserName `source_call))
  let coefficients ← callees.mapM fun _ => return mkIdent (← mkFreshUserName `source_coeff)
  setGoals [soundGoal.mvarId!]
  let storageTerm ← Term.exprToSyntax storage
  let callsTerm ← Term.exprToSyntax calls
  evalTactic (← `(tactic|
    refine HasProgram.of_mul_max (s := $storageTerm) (q := $callsTerm) ?_))
  for (call, h) in callees, C in coefficients do
    -- Eliminate the existential directly: `obtain` would re-elaborate the callee and
    -- re-check the large program goal, which is very slow for dependent input types.
    let type ← whnfR (← inferType call.certificate)
    let coefficient ← mkAppOptM ``HasProgram.exists_implements_mul
      ((type.getAppArgs.push call.certificate).map some)
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
    let (locals, correctGoal) ←
      (← generalizePrograms correctGoal callees).introN 6 [`v, `n, `s, `x, `hv, inputName]
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
        let some (_, h) := callees.find? (·.1.certificate == branch.call.certificate) |
          throwError "source calls: missing callee certificate"
        return (g, branch.call, h, subst.apply branch.value, space, inputCode, equations)
    let lemmas ← caseLemmas
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
        -- Use the concrete encoding equations already obtained for this branch.
        evalTactic (← `(tactic|
          (have source_call := Implements.callCode_bounded ($h $coefficient (by omega))
            $e $n $s $value (space := $space)
            (by simp [-sup_of_le_left, -sup_of_le_right, -Nat.max_eq_left, -Nat.max_eq_right,
              sourcePair, $equations,*] <;> rfl)
            (by
              apply le_trans (b := max ($inputCode).size (encode Tree $value).size)
              · simp [-sup_of_le_left, -sup_of_le_right, -Nat.max_eq_left, -Nat.max_eq_right,
                  sourcePair, $equations,*] <;> omega
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
             | simpa [$lemmas,*] using h.1)))
        else
          evalTactic (← `(tactic|
            (simp +contextual (disch := omega)
               [-sup_of_le_left, -sup_of_le_right,
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
  assignResult goal (← instantiateMVars soundGoal)
  setGoals rest

end FiniteCases

end Complexity.TreeProgram.Source
