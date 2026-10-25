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
/-- A table is built and read by the rules on its code, which have the same program. -/
private def sourceTable : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let #[_, _, _, _, f, time, peak] ← sourceGoalArgs goal |
    throwError "source table: invalid source arguments"
  let some code ← lambdaBoundedTelescope (← etaExpand f) 1 fun xs body => do
      unless xs.size == 1 && (← whnf (← inferType body)).isForall do return none
      let some code ← (observing? (mkAppM ``encode #[mkConst ``Tree, body.eta]) : MetaM _) |
        return none
      return some (← mkLambdaFVars xs code)
    | Search.unsupported "source table: not a table"
  let next ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``Implementation #[code, time, peak])
  let proof ← withLocalDeclD `x (← whnf (← inferType f)).bindingDomain! fun x => do
    mkLambdaFVars #[x] (← mkEqSymm (← mkAppM ``Tree.encode_self #[(mkApp code x).headBeta]))
  goal.assign (← mkAppM ``Implementation.ofEncode #[proof, next])
  replaceMainGoal [next.mvarId!]

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

open Lean Meta in
/-- The components of a right-nested tuple. -/
private partial def tupleComponents (e : Lean.Expr) : List Lean.Expr :=
  if e.isAppOfArity ``Prod.mk 4 then e.appFn!.appArg! :: tupleComponents e.appArg! else [e]

open Lean Meta in
/-- A stated encoding equation `⌜v⌝ₜ = ⌜w⌝ₜ` for the code `⌜v⌝ₜ`, applied at the root only:
the code `⌜w⌝ₜ` and the equation. -/
private def rootEncoding (code : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
  let candidates ← (← getSimpTheorems).post.getMatch code
  for thm in candidates.qsort (·.priority > ·.priority) do
    let value ← thm.getValue
    let (args, _, type) ← forallMetaTelescopeReducing (← inferType value)
    let some (_, l, r) := type.eq? | continue
    unless r.isAppOfArity ``UniqueEncoding.encode 4 do continue
    unless ← isDefEq l code do continue
    let r ← instantiateMVars r
    let proof ← instantiateMVars (mkAppN value args)
    if r.hasMVar || proof.hasMVar || r == code then continue
    return some (r, ← mkExpectedTypeHint proof (← mkEq code r))
  return none

open Lean Meta in
/-- The structural encoding `⌜C a⌝ₜ = ⌜v⌝ₜ` of a constructor application, with the components of
`v` and their declared types. The equation is found for the constructor alone, its fields being
local variables, and the actual fields are substituted afterwards. -/
private def constructorEncoding (body : Lean.Expr) :
    MetaM (Option (Lean.Expr × List (Lean.Expr × Lean.Expr))) := do
  let .const name _ := body.getAppFn | return none
  let some (.ctorInfo ctor) := (← getEnv).find? name | return none
  if name == ``Prod.mk then return none
  let args := body.getAppArgs
  unless args.size == ctor.numParams + ctor.numFields do return none
  let head := mkAppN body.getAppFn (args.extract 0 ctor.numParams)
  let fields := args.extract ctor.numParams args.size
  forallBoundedTelescope (← inferType head) ctor.numFields fun ys type => do
    let some inst ← synthInstance? (← mkAppM ``UniqueEncoding #[mkConst ``Tree, type]) |
      return none
    let some (r, proof) ← rootEncoding
        (← mkAppOptM ``encode #[mkConst ``Tree, type, inst, mkAppN head ys]) |
      return none
    let substitute (e : Lean.Expr) := do return (← mkLambdaFVars ys e).beta fields
    return some (← substitute proof, ← (tupleComponents r.appArg!).mapM fun c => do
      return (← substitute c, ← substitute (← inferType c)))

open Lean Meta Mathlib.Meta.FunProp in
/-- A constructor applied to computed fields, through its structural encoding: the fields are
computed in turn and paired, after a constant tag if the encoding starts with one. The growth
counts each field and the result once, so the encoding's tuple does not appear in it. -/
private def constructorRule (search : Lean.Expr → FunPropM (Option Result)) (goal : Lean.Expr) :
    FunPropM (Option Result) :=
  lambdaTelescope (goal.getArg! 4) fun xs body => do
    let #[x] := xs | return none
    -- A definition whose value is a constructor application, such as `Circuit.id`, is unfolded
    -- once to expose it; nothing else is computed.
    let body ← if ← isConstructorApp body then pure body else do
      let some value ← withTransparency .default <| unfoldDefinition? body | return none
      let value := value.headBeta
      unless (← isConstructorApp value) && (← constructorEncoding value).isSome do return none
      pure value
    let encodeTree (e : Lean.Expr) := mkAppM ``encode #[mkConst ``Tree, e]
    let encodeAs (type e : Lean.Expr) := do
      mkAppOptM ``encode #[mkConst ``Tree, type,
        ← synthInstance (← mkAppM ``UniqueEncoding #[mkConst ``Tree, type]), e]
    -- The value is encoded at the requested type.
    let code ← mkAppOptM ``encode
      #[mkConst ``Tree, (goal.getArg! 1).beta #[x], (goal.getArg! 3).beta #[x], body]
    -- A closed value whose code is the empty tree is computed by no step, like `()`.
    unless body.containsFVar x.fvarId! do
      let some T ← FiniteCases.closedTree code | return none
      unless T.isConstOf ``Tree.nil do return none
      let unit ← mkAppOptM ``Implementation.unit #[← inferType x, none]
      let empty ← mkExpectedTypeHint (← mkEqRefl code)
        (← mkEq code (← encodeTree (mkConst ``Unit.unit)))
      return some ⟨← mkAppM ``Implementation.ofEncode #[← mkLambdaFVars #[x] empty, unit]⟩
    let some (proof, components) ← constructorEncoding body | return none
    let (tag, fields) ← match components with
      | (first, type) :: rest@(_ :: _) =>
        if first.hasFVar then pure (none, components)
        else if let some T ← FiniteCases.closedTree (← encodeAs type first) then
          pure (some (first, T), rest)
        else pure (none, components)
      | _ => pure (none, components)
    if fields.isEmpty then return none
    let growth ← mkArrow (← inferType x) (mkConst ``Nat)
    let mut proofs := #[]
    for (field, type) in fields do
      -- A field is computed at its declared type, whose encoding is found by that name.
      let inst ← synthInstance (← mkAppM ``UniqueEncoding #[mkConst ``Tree, type])
      let fieldGoal ← mkAppOptM ``Implementation #[none, ← mkLambdaFVars #[x] type, none,
        ← mkLambdaFVars #[x] inst, ← mkLambdaFVars #[x] field, ← mkFreshExprMVar growth,
        ← mkFreshExprMVar growth]
      let some r ← search fieldGoal | return none
      proofs := proofs.push r.proof
    let mut chain ← mkAppM ``Implementation.withSize #[proofs.back!]
    for h in proofs.pop.reverse do
      chain ← mkAppM ``Implementation.fieldCons #[h, chain]
    let some (first, T) := tag |
      return some ⟨← mkAppM ``Implementation.ofFields #[← mkLambdaFVars #[x] proof, chain]⟩
    let tuple := ((← inferType chain).getArg! 4).beta #[x]
    let tagged ← mkEq code (mkApp2 (mkConst ``Tree.pair) T (← encodeTree tuple))
    let henc ← mkExpectedTypeHint
      (← mkEqTrans proof (← mkAppM ``encode_prod #[first, tuple])) tagged
    return some ⟨← mkAppM ``Implementation.ofTaggedFields #[T, ← mkLambdaFVars #[x] henc, chain]⟩

open Lean Meta Mathlib.Meta.FunProp in
/-- Reading a table, a local or a field of one, at an index: the table is computed as its code
and the index as its value, and the entry is looked up in the code. -/
private def tableRead (search : Lean.Expr → FunPropM (Option Result)) (goal : Lean.Expr) :
    FunPropM (Option Result) :=
  lambdaTelescope (goal.getArg! 4) fun xs body => do
    let #[x] := xs | return none
    let body ← whnfR body
    let .app table index := body | return none
    let fn := body.getAppFn
    let stored ← do
      if fn.isFVar || fn.isProj then pure (fn != x) else
      let some name := fn.constName? | pure false
      let some info ← getProjectionFnInfo? name | pure false
      pure (body.getAppNumArgs > info.numParams + 1)
    -- The lookup rule is proved with the library, after this file.
    let rule := `Complexity.TreeProgram.Source.Implementation.finApply
    unless stored && (← getEnv).contains rule do return none
    let some hf ← search (← implementationGoal
      (← mkLambdaFVars #[x] (← mkAppM ``encode #[mkConst ``Tree, table]))) | return none
    let some hi ← search (← implementationGoal
      (← mkLambdaFVars #[x] (← mkAppM ``Fin.val #[index]))) | return none
    return some ⟨← mkAppM rule #[hf.proof, hi.proof]⟩

open Lean Meta in
/-- A value as the corresponding value of codes, with the same code: lists and pairs. -/
private def codesView (type : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
  if type.isAppOfArity ``List 1 then
    let entry := type.appArg!
    let encode ← mkAppOptM ``UniqueEncoding.encode #[mkConst ``Tree, entry, none]
    return some (← mkAppM ``List.map #[encode], ← mkAppOptM ``encode_list_codes #[entry, none])
  if type.isAppOfArity ``Prod 2 then
    let code (field : Name) (z : Lean.Expr) := do
      mkAppM ``encode #[mkConst ``Tree, ← mkAppM field #[z]]
    let view ← withLocalDeclD `z type fun z => do
      mkLambdaFVars #[z] (← mkAppM ``Prod.mk #[← code ``Prod.fst z, ← code ``Prod.snd z])
    let equation ← mkAppOptM ``encode_prod_codes #[type.appFn!.appArg!, type.appArg!, none, none]
    return some (view, equation)
  return none

open Lean Meta in
/-- A registered `HasProgram` fact instantiated at the function `fn`, or at `Tree` for every type
parameter. -/
private def instantiateFact (fact : Name) (fn : Option Lean.Expr) : MetaM Lean.Expr := do
  let proof ← mkConstWithFreshMVarLevels fact
  let (args, binders, statement) ← forallMetaTelescopeReducing (← inferType proof)
  match fn with
  | some fn =>
    unless ← isDefEq (statement.getArg! 4) fn do throwError "{fact} does not apply"
  | none =>
    for arg in args do
      if (← whnf (← inferType arg)).isSort then
        unless ← isDefEq arg (mkConst ``Tree) do throwError "{fact} has no instance at codes"
  for arg in args, binder in binders do
    if binder.isInstImplicit && !(← arg.mvarId!.isAssigned) then
      arg.mvarId!.assign (← synthInstance (← inferType arg))
  instantiateMVars (mkAppN proof args)

open Lean Meta Mathlib.Meta.FunProp in
/-- A function with one program at every type (`HasProgram`, from `uniform_program`) applied to an
argument whose type depends on the input: the argument is computed and the program runs on its
code (`Implementation.compCodes`). The growth is stated on the argument, not on its code. -/
private def codesComposition (search : Lean.Expr → FunPropM (Option Result))
    (goal : Lean.Expr) : FunPropM (Option Result) := do
  let some (argument, view, equation, atCodes, atTypes) ←
      lambdaTelescope (← etaExpand (goal.getArg! 4)) fun xs body => do
        let #[x] := xs | return none
        let body := body.headBeta
        -- A projection of the input is a subtree of its code, read by the structural stage.
        if ← Search.isProjectionOf x body then return none
        let some name := body.getAppFn.constName? | return none
        unless body.isApp do return none
        unless (← inferType body.appArg!).containsFVar x.fvarId! do return none
        let some (view, equation) ← codesView (← whnfR (← inferType body.appArg!)) | return none
        for fact in ← getTheoremsForFunction name ``HasProgram do
          let .decl fact := fact.thmOrigin | continue
          let some (atType, atCodes) ← (observing? (return (← instantiateFact fact
              (some body.appFn!), ← instantiateFact fact none)) : MetaM _) | continue
          return some (← mkLambdaFVars xs body.appArg!, ← mkLambdaFVars xs view,
            ← mkLambdaFVars xs equation, atCodes, ← mkLambdaFVars xs atType)
        return none
    | return none
  let some hx ← search (← implementationGoal argument) | return none
  let result ← mkAppM ``Implementation.compCodes #[hx.proof, view, equation, atCodes, atTypes]
  let type ← whnfR (← inferType result)
  let codes ← Simp.mkContext (simpTheorems := #[← [``encode_list_codes, ``encode_prod_codes,
    ``List.length_map, ``Tree.encode_self].foldlM (·.addConst ·) ({} : SimpTheorems)])
  let comparisons ← [5, 6].mapM fun i => do
    let growth := type.getArg! i
    match (← simp growth codes).1.proof? with
    | some equation => mkAppM ``dominated_of_eq #[equation]
    | none => mkAppM ``Dominated.refl #[growth]
  return some ⟨← mkAppM ``Implementation.mono #[result, comparisons[0]!, comparisons[1]!]⟩

open Lean Meta in
/-- Whether a value is built by constructors from the input, its projections and closed values,
so that its code is assembled from subtrees of the input's code. -/
private partial def isAtHand (x e : Lean.Expr) : MetaM Bool := do
  if !e.containsFVar x.fvarId! then return true
  if ← Search.isProjectionOf x e then return true
  let some name := e.getAppFn.constName? | return false
  let some (.ctorInfo ctor) := (← getEnv).find? name | return false
  (e.getAppArgs.extract ctor.numParams e.getAppNumArgs).allM (isAtHand x)

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
  let solve : TacticM Unit := withMainContext do
    let goal ← getMainGoal
    let some proof ← query (← goal.getType) |
      Search.unsupported "source table: the table has no implementation"
    goal.assign proof
    replaceMainGoal []
  let structural : FunPropM (Option Result) := Search.attempt do
    -- A speculative lambda rule may leave an unencodable function-valued result.
    -- Such a premise cannot be compiled structurally, but another candidate may apply.
    for encoder in goal.getAppArgs.extract 2 4 do
      let encoder ← instantiateMVars encoder
      -- The output encoder is a family over the input.
      if (if encoder.isLambda then encoder.bindingBody! else encoder).getAppFn.isMVar then
        let some encoderProof ← synthInstance? (← inferType encoder) | return none
        unless ← isDefEq encoder encoderProof do return none
    for action in [FiniteCases.sourceCases, sourceTable *> solve,
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
      -- A function with one program at every type, at an argument whose type depends on the input.
      if let .const name _ := d.fn then
        unless (← getTheoremsForFunction name ``HasProgram).isEmpty do
          if let some r ← Search.attempt (codesComposition search target) then return some r
      if let some name := encodedCall then
        if let some r ← rules true then return some r
        session.reject ancestors (Search.recursionMessage name) .specification (some name)
        return none
      let info? ← match d.fn with
        | .const name _ => pure (some (← getConstInfo name))
        | _ => pure none
      -- A nested constructor of values at hand is assembled from subtrees of the input's code.
      let atHand ← if nested && info?.any (·.isCtor) then
          lambdaTelescope (target.getArg! 4) fun xs body => do
            let #[x] := xs | return false
            isAtHand x body
        else pure false
      if atHand then
        if let some r ← structural then return some r
      -- Otherwise a constructor is built from its fields, also as the value of a definition.
      if info?.any fun info => info.isCtor || info.isDefinition then
        if let some r ← Search.attempt (constructorRule search target) then return some r
      -- A nonmatching candidate must not block structural field extraction.
      if !atHand && (nested || !candidates.isEmpty) then
        if let some r ← structural then return some r
      -- Subcall specifications need structural decomposition before their fallback rules:
      -- otherwise lookup of a composite table can recursively request rebuilding that table.
      if let some r ← rules true then return some r
      if let some r ← Search.attempt (tableRead search target) then return some r
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
  let tactic ← `(tactic| first | with_reducible assumption | infer_param)
  let config := { maxSteps := source.maxSteps.get (← getOptions) : Mathlib.Meta.FunProp.Config }
  return { disch := tacticToDischarge tactic, config }

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
        if param.isExplicit && !(← Search.isProjectionOf x arg) then return none
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
  let hd ← certify `finish (← instantiateMVars fields[5]!)
  let resume ← instantiateMVars fields[6]!
  let returnType ← forallTelescope (← inferType resume) fun xs _ => do
    mkAppM ``Sigma #[← mkLambdaFVars #[xs[0]!] (← inferType xs[1]!)]
  let resume ← withLocalDeclD `x returnType fun x => do
    mkLambdaFVars #[x] (mkAppN resume #[← mkAppM ``Sigma.fst #[x], ← mkAppM ``Sigma.snd #[x]])
  let hr ← certify `resume resume
  -- The callbacks' encoding families agree with the recursion's by definition.
  let implementation ← Term.elabTerm (← `(Recursion.implementation $(← Term.exprToSyntax r)
    $(← Term.exprToSyntax hc) $(← Term.exprToSyntax hs) $(← Term.exprToSyntax hd)
    $(← Term.exprToSyntax hr))) none
  Term.synthesizeSyntheticMVarsNoPostponing
  let implementation ← instantiateMVars implementation
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
