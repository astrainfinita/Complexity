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
public meta import Complexity.Tactic.TreeProgram.FiniteCases

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
    -- Structural growth is shown with beta redexes and constructor projections reduced, and
    -- without encoding a tree again.
    let produced := (← dsimp actual.getAppArgs[i]! (← Simp.mkContext
      (config := { zeta := false, zetaDelta := false, iota := false })
      (simpTheorems := #[← ({} : SimpTheorems).addConst ``Tree.encode_self]))).1
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
private def sourceCallsWith (roots : NameSet) (query : Lean.Expr → MetaM (Option Lean.Expr)) :
    TacticM Unit :=
  FiniteCases.sourceCalls roots fun f => do
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
private def localSourceCertificate (goal : Lean.Expr) : FunPropM (Option Result) := do
  unless goal.isAppOfArity ``Implementation 7 do return none
  if goal.getAppArgs[4]!.hasExprMVar then return none
  let locals := (← getLCtx).foldl (fun ds d => d :: ds) []
  for decl in locals do
    if decl.kind == .auxDecl then continue
    let type ← instantiateMVars decl.type
    unless type.isAppOfArity ``Implementation 7 do continue
    if let some result ← Search.attempt do
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
  let goal ← instantiateMVars goal
  trace[source.translation] "implementation query: {goal}"
  session.step
  trace[Meta.Tactic.fun_prop] "source step {← session.steps.get}: {goal}"
  if let some result ← localSourceCertificate goal then return some result
  let key := implementationKey goal
  if let some { proof? := some proof, .. } := (← get).cache.find? key then
    if ← isDefEq goal (← inferType proof) then return some ⟨proof⟩
  -- Auxiliary theorems of a failed attempt are rolled back; results using them are recomputed.
  if let some proof := (← session.results.get)[(key, nested)]? then
    if proof.getUsedConstants.all (← getEnv).contains then
      if ← isDefEq goal (← inferType proof) then return some ⟨proof⟩
  -- Only requests with unconstrained growth are failures of the source function itself.
  let unconstrained := !goal.isAppOfArity ``Implementation 7 ||
    (goal.getAppArgs[5]!.isMVar && goal.getAppArgs[6]!.isMVar)
  if unconstrained && (← get).failureCache.contains key then return none
  if ancestors.contains key then return none
  let ancestors := ancestors.push key
  increaseSteps
  let restore ← Search.checkpoint
  let search := sourceSearch session true ancestors
  let context ← read
  -- A branch has a different local context: only fuel, path and diagnostics cross this boundary.
  let query := sourceQuery search context
  let structural : FunPropM (Option Result) := Search.attempt do
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
    for action in [FiniteCases.sourceCases, sourceDependent *> solve,
        sourceCallsWith (← session.roots.get) query] do
      if let some proof ← session.discharge ancestors action goal then
        return some ⟨proof⟩
    return none
  let finish (result : Option Result) : FunPropM (Option Result) := do
    if let some r := result then
      let proof ← instantiateMVars
        (← typedSourceImplementation (← instantiateMVars goal) (← instantiateMVars r.proof))
      unless key.hasFVar || key.hasMVar || proof.hasFVar || proof.hasMVar do
        session.results.modify (·.insert (key, nested) proof)
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
    | .lam f => Search.lambdaRules search decl .pi (goal.setArg decl.funArgId f)
    | .letE f => Search.letRule search decl (goal.setArg decl.funArgId f) f
    | .data d => withLCtx d.lctx d.insts do
      let target := goal.setArg decl.funArgId (← d.toExpr)
      if d.isIdentityFun then return ← Search.lambdaRules search decl .id target
      if d.isConstantFun then
        if let some r ← Search.lambdaRules search decl .const target then return some r
      let candidates ← Search.functionTheorems decl d
      let env ← getEnv
      let rules (fallback : Bool) : FunPropM (Option Result) := do
        for rule in candidates do
          if Search.isFallback env rule != fallback then continue
          if let some result ← Search.functionRules search decl target d #[rule] then
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
          if let some r ← Search.transitionRules search target then return some r
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
          if let some r ← Search.attempt do
              let some (outer, inner) ← Environment.decomposition? (← d.toExpr) | return none
              Search.lambdaRules search decl .comp target (some (outer, inner)) then
            return some r
      if let some f ← d.unfoldHeadFVar? then
        return ← sourceSearch session nested ancestors (target.setArg decl.funArgId f)
      if let .const name _ := d.fn then
        if ← isRecursiveDefinition name then
          session.reject ancestors (Search.recursionMessage name) .specification (some name)
          return none
        unless (← getMatcherInfo? name).isSome do
          if let some body ← FiniteCases.unfoldSource? (← session.roots.get)
              (Mor.mkAppN d.fn d.args) then
            return ← sourceSearch session nested ancestors
              (target.setArg decl.funArgId (← mkLambdaFVars #[d.mainVar] body))
          if (← getConstInfo name).isDefinition then
            session.reject ancestors m!"source translation: `{.ofConstName name}` needs a \
              selected implementation (register one with `[source]`, or choose replacement \
              source with `via`)" .specification (some name)
            return none
      if let .comp outer inner := decomposition then
        if let some r ← Search.lambdaRules search decl .comp target
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

open Lean Meta in
/-- Whether `e` is `x` or a projection of it. -/
private partial def isProjectionOf (x e : Lean.Expr) : MetaM Bool := do
  if e == x then return true
  if let .proj _ _ base := e then return ← isProjectionOf x base
  let some name := e.getAppFn.constName? | return false
  let some info ← getProjectionFnInfo? name | return false
  if e.getAppNumArgs != info.numParams + 1 then return false
  isProjectionOf x e.appArg!

open Lean Meta in
/-- Record the definition a source function is, up to eta, uncurrying and an encoder: `g`,
`fun x => g x.1 x.2` or `fun x => ⌜g x⌝ₜ`, whose explicit arguments are the input or its
projections. Calling `g` on anything else is a use of `g`, which needs its own selected
implementation. -/
def addSourceRoot (session : Search.Session) (f : Lean.Expr) : MetaM Unit := do
  if let some name := f.eta.getAppFn.constName? then
    session.roots.modify (·.insert name)
    return
  let some name ← lambdaTelescope f fun xs body => do
      let body := if body.isAppOfArity ``UniqueEncoding.encode 4 then body.appArg! else body
      let some name := body.getAppFn.constName? | return none
      let #[x] := xs | return none
      let info ← getFunInfoNArgs body.getAppFn body.getAppNumArgs
      for arg in body.getAppArgs, param in info.paramInfo do
        if param.isExplicit && !(← isProjectionOf x arg) then return none
      return some name
    | return
  session.roots.modify (·.insert name)

open Lean Meta Elab Tactic Mathlib.Meta.FunProp in
/-- Certify a callback named in a method syntax completely, sharing the method's session.
The source rules in scope are those activated by `withSourceSpecs`. -/
def certifyCallback (session : Search.Session) (method name : Name) (callback : Lean.Expr) :
    TacticM Lean.Expr := do
  if callback.hasExprMVar then
    throwError "source {method}: provide a concrete `{name}` callback"
  addSourceRoot session callback
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
    addSourceRoot session source
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
    if target.isAppOfArity ``Implementation 7 then addSourceRoot session target.getAppArgs[4]!
    let query := sourceQuery (sourceSearch session true #[target]) (← sourceContext)
    let some proof ← session.discharge #[target] (sourceCallsWith (← session.roots.get) query)
      target | session.report
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
