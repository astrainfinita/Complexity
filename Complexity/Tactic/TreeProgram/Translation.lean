/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Tactic.TreeProgram.Rules
public import Complexity.Tactic.TreeProgram.Recursion
public import Complexity.Tactic.Dominated.Basic
public import Complexity.Tactic.TreeProgram.Views
public meta import Complexity.Tactic.TreeProgram.Search
public meta import Complexity.Tactic.TreeProgram.Environment
public import Complexity.Models.TreeMachine.Language.Derive
public meta import Complexity.Models.TreeMachine.Language.Semantics
public import Complexity.Resources.TreeMachine.Program
public import Complexity.Classes.Functions.Basic
public import Complexity.Encoding.TreeSize
public meta import Lean.Meta.Match.MatcherApp.Transform
public meta import Lean.Meta.RecExt
public meta import Complexity.Tactic.Hole
public import Complexity.Tactic.TreeProgram.Match
public meta import Complexity.Tactic.TreeProgram.Match
public import Complexity.Tactic.TreeProgram.Assembly
public meta import Complexity.Tactic.TreeProgram.Assembly

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

namespace HasProgram

variable {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β] {f : α → β}
  {program : Value → Code Value} {t p : α → ℕ}

/-- Keep loading, controller and peak costs when hiding the fixed machine's register factor. -/
theorem computableWithGrowth (hf : HasProgram f program t p) :
    TimeSpaceModel.tree.ComputableWithGrowth f (fun x => t x + 4)
      (fun x => max ⌜x⌝ₜ.size (p x) + 2) := by
  obtain ⟨b, h, ht, hp⟩ := hf.sound
  exact ⟨fun x => b.time x + 4,
    fun x => (program .input).registers * (max ⌜x⌝ₜ.size (b.peak x) + 2),
    h.computableWithin (fun _ => ⟨le_rfl, le_rfl⟩), ht.add (Dominated.refl _),
    (((Dominated.refl _).max hp).add (Dominated.refl _)).const_mul_left _⟩

/-- Compare the input budgets at the machine boundary. Loading and storage overheads remain
explicit. -/
theorem computableWithGrowth_of_dominated {T S : α → ℕ} (hf : HasProgram f program t p)
    (ht : Dominated (fun x => t x + 4) T)
    (hp : Dominated (fun x => max ⌜x⌝ₜ.size (p x) + 2) S) :
    TimeSpaceModel.tree.ComputableWithGrowth f T S :=
  hf.computableWithGrowth.mono ht hp

end HasProgram

end Complexity.TreeProgram.Source

namespace Complexity

namespace TreeProgram.Source.HasProgram

variable {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
  {f : α → β} {program : Value → Code Value} {t p : α → ℕ} {T S : ℕ → ℕ}

theorem mem_ftisp (hf : HasProgram f program (fun x => T ⌜x⌝ₜ.size) (fun x => S ⌜x⌝ₜ.size))
    (input : Dominated (fun x : α => ⌜x⌝ₜ.size) (fun x => S ⌜x⌝ₜ.size))
    (time_overhead : Dominated (fun _ : α => 4) (fun x => T ⌜x⌝ₜ.size))
    (space_overhead : Dominated (fun _ : α => 2) (fun x => S ⌜x⌝ₜ.size)) :
    f ∈ FTISP .tree T S :=
  (hf.computableWithGrowth_of_dominated
    ((Dominated.refl _).add_same time_overhead)
    ((input.max_same (Dominated.refl _)).add_same space_overhead)).mem_ftisp

/-- Compare the structural growth with the scale functions at the model boundary. -/
theorem mem_ftisp_of_dominated (hf : HasProgram f program t p)
    (ht : Dominated (fun x => t x + 4) (fun x => T ⌜x⌝ₜ.size))
    (hp : Dominated (fun x => max ⌜x⌝ₜ.size (p x) + 2) (fun x => S ⌜x⌝ₜ.size)) :
    f ∈ FTISP .tree T S :=
  (hf.computableWithGrowth_of_dominated ht hp).mem_ftisp

/-- Exact-size envelopes are used only where an eventual scale comparison is required.
This permits finite input types to inhabit a zero eventual class without weakening their
all-input program or machine specifications. -/
theorem mem_ftisp_of_sizeEnvelope (hf : HasProgram f program t p)
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
    (hf : HasProgram f program (fun x => ⌜x⌝ₜ.size ^ t) (fun x => ⌜x⌝ₜ.size ^ s))
    (hs : 0 < s) : f ∈ FTISP .tree (fun n => n ^ t) (fun n => n ^ s) := by
  apply hf.mem_ftisp
  · exact (Dominated.of_le fun x => Nat.le_self_pow (by omega) _)
  · exact (Dominated.const_of_pos 4 (fun x => Nat.pow_pos (Tree.size_pos ⌜x⌝ₜ)))
  · exact (Dominated.const_of_pos 2 (fun x => Nat.pow_pos (Tree.size_pos ⌜x⌝ₜ)))

end TreeProgram.Source.HasProgram

end Complexity

end

public meta section

namespace Complexity.TreeProgram.Source

/-- Compose source-function implementations and their growth.
`using ns` activates the namespace's scoped rules for this translation and its callbacks;
`via g` translates `g` instead and leaves the equality with the source as a goal;
`using recursion (…)` and `using loop (…)` compile the source by that method from the given
callbacks, leaving the method's obligations as goals. The growth comparisons left are closed by
`dominated` when it closes them completely, or by the discharger given as `(disch := tac)`,
such as `(disch := dominated [f])`; the others remain as goals. -/
syntax (name := sourceFunProp) "source_fun_prop" (Lean.Parser.Tactic.discharger)?
  (" using " ident)? (" via " term)? : tactic

open Lean Meta in
/-- `proof` as a proof of `type`: itself when the types agree reducibly, otherwise an auxiliary
theorem stated at `type`, which the kernel checks. -/
def typedSourceProof (type proof : Lean.Expr) : MetaM Lean.Expr := do
  if ← withReducible (isDefEq type (← inferType proof)) then return proof
  mkAuxTheorem type proof

open Lean Meta in
/-- The arguments of a goal `HasProgram f program time peak`, with its implicit types and
encodings. -/
def sourceGoalArgs (goal : MVarId) : MetaM (Array Lean.Expr) := do
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOfArity ``HasProgram 8 do
    throwError "source translation: expected HasProgram, got {target}"
  return target.getAppArgs

open Lean Meta in
/-- Unfold a definition being translated; any other definition only as notation (reducible
definitions and instances), since its cost is that of its own selected implementation. -/
private def unfoldSource? (roots : NameSet) (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let some name := e.getAppFn.constName? | return none
  if roots.contains name then unfoldDefinition? e
  else withReducibleAndInstances (unfoldDefinition? e)

open Lean Meta in
/-- A program request whose program and growth are left to the selected rules. -/
def programGoal (f : Lean.Expr) : MetaM Lean.Expr := do
  let growth ← mkArrow (← whnf (← inferType f)).bindingDomain! (mkConst ``Nat)
  let program ← mkFreshExprMVar
    (← mkArrow (mkConst ``Value) (mkApp (mkConst ``Code) (mkConst ``Value)))
  mkAppM ``HasProgram #[f, program, ← mkFreshExprMVar growth, ← mkFreshExprMVar growth]

open Lean Meta in
/-- Close a program request. Growth placeholders take the produced growth; a stated growth
leaves the two `Dominated` comparisons for the same program. -/
def finishProgram (goal : MVarId) (result : Lean.Expr) : MetaM (List MVarId) :=
    goal.withContext do
  let target := (← whnfR (← instantiateMVars (← goal.getType))).consumeMData
  let actual := (← whnfR (← instantiateMVars (← inferType result))).consumeMData
  unless target.isAppOfArity ``HasProgram 8 && actual.isAppOfArity ``HasProgram 8 do
    throwError "source translation: expected a HasProgram goal, got {target} and {actual}"
  -- A named placeholder takes the produced program or growth, like an anonymous one; a hole is
  -- left to `fill_hole`.
  let placeholder? (e : Lean.Expr) : MetaM (Option MVarId) := do
    let .mvar id := e | return none
    return if (← id.isAssigned) || (← id.isReadOnly) then none else some id
  if let some id ← placeholder? target.getAppArgs[5]! then id.assign actual.getAppArgs[5]!
  let mut obligations := []
  let mut comparisons := #[]
  for i in [6, 7], tag in [`time, `peak] do
    let requested := target.getAppArgs[i]!
    -- Structural growth is shown with beta redexes and constructor projections reduced, and
    -- without encoding a tree again.
    let produced := (← dsimp actual.getAppArgs[i]! (← Simp.mkContext
      (config := { zeta := false, zetaDelta := false, iota := false })
      (simpTheorems := #[← ({} : SimpTheorems).addConst ``Tree.encode_self]))).1
    if let some id ← placeholder? requested then id.assign produced
    if ← withReducible (isDefEq requested produced) then
      comparisons := comparisons.push (← mkAppM ``Dominated.refl #[produced])
    else
      let h ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``Dominated #[produced, requested])
        (tag := tag)
      comparisons := comparisons.push h
      obligations := obligations ++ [h.mvarId!]
  let value ← if obligations.isEmpty then pure result
    else mkAppM ``HasProgram.mono #[result, comparisons[0]!, comparisons[1]!]
  unless ← isDefEq (← goal.getType) (← inferType value) do
    -- A program left as a hole is filled only by `fill_hole`.
    if let .mvar hole := (target.getArg! 5).getAppFn then
      if (Hole.infoExt.getState (← getEnv)).contains hole && !(← hole.isAssigned) then
        let name := (← hole.getDecl).userName.eraseMacroScopes
        throwError "source translation: the program is the hole `{name}`; write \
          `fill_hole {name} in` before the tactic"
    throwError "source translation: the implementation does not match the requested source"
  goal.assign value
  return obligations

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
  unless goal.isAppOfArity ``HasProgram 8 do return none
  if goal.getAppArgs[4]!.hasExprMVar then return none
  let locals := (← getLCtx).foldl (fun ds d => d :: ds) []
  for decl in locals do
    if decl.kind == .auxDecl then continue
    let type ← instantiateMVars decl.type
    unless type.isAppOfArity ``HasProgram 8 do continue
    if let some result ← Search.attempt do
        if ← withReducible (isDefEq type goal) then return some ⟨decl.toExpr⟩
        return none then
      return some result
  return none
open Lean Meta in
private def typedSourceImplementation (target implementation : Lean.Expr) : MetaM Lean.Expr := do
  unless target.isAppOfArity ``HasProgram 8 do return implementation
  let actual ← inferType implementation
  if ← withReducible (isDefEq actual target) then return implementation
  unless ← withDefault (isDefEq actual target) do
    throwError "source translation: the implementation has a different source type or encoding"
  let source := actual.getAppArgs[4]!
  let desired := (← instantiateMVars target).getAppArgs[4]!
  let equality ← typedSourceProof (← mkEq source desired) (← mkEqRefl source)
  mkAppM ``HasProgram.congr #[implementation, equality]

open Lean in
/-- Program and growth arguments are results of a query, so they do not distinguish cached
requests. -/
private def implementationKey (goal : Lean.Expr) : Lean.Expr :=
  if goal.isAppOfArity ``HasProgram 8 then mkAppN goal.getAppFn (goal.getAppArgs.extract 0 5)
  else goal

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
    let some (proof, components) ← constructorEncoding body | return none
    let (tag, fields) ← match components with
      | (first, type) :: rest@(_ :: _) =>
        -- A closed tag is written as its code, without computing it.
        if first.hasFVar || first.hasMVar then pure (none, components)
        else pure (some (first, ← encodeAs type first), rest)
      | _ => pure (none, components)
    if fields.isEmpty then return none
    let growth ← mkArrow (← inferType x) (mkConst ``Nat)
    let mut proofs := #[]
    for (field, type) in fields do
      -- A field is computed at its declared type, whose encoding is found by that name.
      let inst ← synthInstance (← mkAppM ``UniqueEncoding #[mkConst ``Tree, type])
      let fieldGoal ← mkAppOptM ``HasProgram #[none, ← mkLambdaFVars #[x] type, none,
        ← mkLambdaFVars #[x] inst, ← mkLambdaFVars #[x] field,
        ← mkFreshExprMVar (← mkArrow (mkConst ``Value) (mkApp (mkConst ``Code) (mkConst ``Value))),
        ← mkFreshExprMVar growth, ← mkFreshExprMVar growth]
      let some r ← search fieldGoal | return none
      proofs := proofs.push r.proof
    let mut chain ← mkAppM ``HasProgram.with_size #[proofs.back!]
    for h in proofs.pop.reverse do
      chain ← mkAppM ``HasProgram.field_cons #[h, chain]
    let some (first, T) := tag |
      return some ⟨← mkAppM ``HasProgram.of_fields #[← mkLambdaFVars #[x] proof, chain]⟩
    let tuple := ((← inferType chain).getArg! 4).beta #[x]
    let tagged ← mkEq code (mkApp2 (mkConst ``Tree.pair) T (← encodeTree tuple))
    let henc ← mkExpectedTypeHint
      (← mkEqTrans proof (← mkAppM ``encode_prod #[first, tuple])) tagged
    return some ⟨← mkAppM ``HasProgram.of_tagged_fields #[T, ← mkLambdaFVars #[x] henc, chain]⟩

open Lean Meta in
/-- Whether the function applied in `e` is data: a local other than the input `x`, or a field. -/
private def appliesData (x e : Lean.Expr) : MetaM Bool := do
  let fn := e.getAppFn
  if fn.isFVar || fn.isProj then return fn != x
  let some name := fn.constName? | return false
  let some info ← getProjectionFnInfo? name | return false
  -- A class method is not a stored field.
  return !info.fromClass && e.getAppNumArgs > info.numParams + 1

open Lean Meta Mathlib.Meta.FunProp in
/-- For a value `b` of a type with a `source_view` view `⌜y⌝ₜ = ⌜g y⌝ₜ`, such as an index, a
subtype or a table (`List.ofFn`), the request for the value computed instead and the equation of
their codes, which have the same program and growth. The view `g y` of a value `y` other than a
function literal is computed as `y`. Otherwise `b` is computed as `w` by a `source_view` equation
`⌜b⌝ₜ = ⌜w⌝ₜ`, or through its view `g b`: as the form of `g b` given by a `source_view` equation,
or as `g b` itself when `g` has rules. A function literal is a table built pointwise, left to the
enumeration rule; a projection of the input is stored, left to field extraction; an equation
about an applied variable, such as a table read, applies to applied data only, a definition
having its own implementation. Only reads are used if `reads`, and only the other equations
otherwise. -/
private def viewRequest? (goal : Lean.Expr) (reads : Bool) :
    MetaM (Option (Lean.Expr × Lean.Expr)) :=
  lambdaBoundedTelescope (goal.getArg! 4) 1 fun xs body => do
    let #[x] := xs | return none
    let some ext ← getSimpExtension? `source_view | return none
    let thms ← ext.getTheorems
    let code ← mkAppOptM ``encode
      #[mkConst ``Tree, (goal.getArg! 1).beta #[x], (goal.getArg! 3).beta #[x], body]
    -- The equation `code = ⌜v⌝ₜ` for the value `v` computed instead.
    let field : MetaM (Option Lean.Expr) := do
      if reads then return none
      let .app _ y := body | return none
      if y.eta.isLambda then return none
      -- A proof or a type has no code.
      let some y ← (observing? (mkAppM ``encode #[mkConst ``Tree, y]) : MetaM _) | return none
      rootEquation thms y true fun r h _ => do
        unless ← withReducible (isDefEq r.appArg! body) do return none
        return some (← mkExpectedTypeHint (← mkEqSymm h) (← mkEq code y))
    let form : MetaM (Option Lean.Expr) := do
      if ← Search.isProjectionOf x body then return none
      rootEquation thms code true fun r h applied => do
        if applied != reads then return none
        let w := r.appArg!
        unless w.isApp && w.appArg! == body do
          if applied && !(← appliesData x body) then return none
          return some h
        if let some h' ← rootEquation thms w false fun _ h' _ => return some h' then
          return some (← mkEqTrans h (← mkCongrArg r.appFn! h'))
        let some name := w.getAppFn.constName? | return none
        -- The field of a constructor; its equations have no key, being reduced in the index.
        if let some info ← getProjectionFnInfo? name then
          if let some value ← projectCore? body info.i then
            return some (← mkExpectedTypeHint h (← mkEq code (mkApp r.appFn! value)))
        if (← getTheoremsForFunction name ``HasProgram).isEmpty then return none
        return some h
    let some h ← do if let some h ← field then pure (some h) else form | return none
    let some (_, _, value) := (← inferType h).eq? | return none
    let next ← mkAppOptM ``HasProgram #[none, ← mkLambdaFVars #[x] (value.getArg! 1), none,
      ← mkLambdaFVars #[x] (value.getArg! 2), ← mkLambdaFVars #[x] value.appArg!,
      goal.getArg! 5, goal.getArg! 6, goal.getArg! 7]
    return some (next, ← mkLambdaFVars #[x] h)

open Lean Meta Mathlib.Meta.FunProp in
/-- A value with a view is computed through it (`viewRequest?`), with the same program and growth.
Reads, the equations about an applied variable, are tried after stored subtrees are extracted. -/
private def viewRule (search : Lean.Expr → FunPropM (Option Result)) (goal : Lean.Expr)
    (reads := false) : FunPropM (Option Result) := do
  let some (next, h) ← viewRequest? goal reads | return none
  let some r ← search next | return none
  return some ⟨← mkAppM ``HasProgram.of_encode #[h, r.proof]⟩

open Lean Meta in
/-- The value of codes corresponding to `e`, where `pattern` is the argument type of a fact: the
entries at a type parameter of the fact become their codes, through lists and pairs. The value
and the equation that its code is that of `e`. -/
private partial def codesView (pattern e : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
  let pattern ← instantiateMVars pattern
  if pattern.isMVar then
    let code ← mkAppM ``encode #[mkConst ``Tree, e]
    return some (code, ← mkAppM ``Tree.encode_self #[code])
  if !pattern.hasMVar then
    return some (e, ← mkEqRefl (← mkAppM ``encode #[mkConst ``Tree, e]))
  -- A fact matched by its head may be about another type with the same notation.
  let type ← whnfR (← inferType e)
  if pattern.isAppOfArity ``List 1 then
    unless type.isAppOfArity ``List 1 do return none
    let some (view, equation) ← withLocalDeclD `a type.appArg! fun a => do
        let some (v, h) ← codesView pattern.appArg! a | return none
        return some ((← mkLambdaFVars #[a] v).eta, ← mkLambdaFVars #[a] h) | return none
    return some (← mkAppM ``List.map #[view, e],
      ← mkAppM ``encode_list_map_of_encode #[view, equation, e])
  if pattern.isAppOfArity ``Prod 2 then
    unless type.isAppOfArity ``Prod 2 do return none
    let some (v₁, h₁) ← codesView pattern.appFn!.appArg! (← mkAppM ``Prod.fst #[e]) | return none
    let some (v₂, h₂) ← codesView pattern.appArg! (← mkAppM ``Prod.snd #[e]) | return none
    let v ← mkAppM ``Prod.mk #[v₁, v₂]
    -- Stated on `e` itself rather than on the pair of its fields.
    let h ← mkExpectedTypeHint (← mkAppM ``encode_prod_congr #[h₁, h₂])
      (← mkEq (← mkAppM ``encode #[mkConst ``Tree, v]) (← mkAppM ``encode #[mkConst ``Tree, e]))
    return some (v, h)
  return none

open Lean Meta in
/-- A registered `HasProgram` fact instantiated where its function applied to `argument` is
`value`, or at `Tree` for every type parameter. -/
private def instantiateFact (fact : Name) (at? : Option (Lean.Expr × Lean.Expr)) :
    MetaM Lean.Expr := do
  let proof ← mkConstWithFreshMVarLevels fact
  let (args, binders, statement) ← forallMetaTelescopeReducing (← inferType proof)
  match at? with
  | some (argument, value) =>
    unless ← isDefEq ((statement.getArg! 4).beta #[argument]) value do
      throwError "{fact} does not apply"
  | none =>
    for arg in args do
      if (← whnf (← inferType arg)).isSort then
        unless ← isDefEq arg (mkConst ``Tree) do throwError "{fact} has no instance at codes"
  for arg in args, binder in binders do
    if binder.isInstImplicit && !(← arg.mvarId!.isAssigned) then
      arg.mvarId!.assign (← synthInstance (← inferType arg))
  instantiateMVars (mkAppN proof args)

open Lean Meta Mathlib.Meta.FunProp in
/-- A fact in simple form without premises, one program at every type, applied in `body` to
arguments whose types depend on the input `x`: the tuple of the arguments, its view of codes and
their equation, and the fact at codes and at the arguments. -/
private def codesInstance (x body : Lean.Expr) (fact : FunctionTheorem) :
    MetaM (Option (Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr)) := do
  let .decl name := fact.thmOrigin | return none
  unless fact.form == .uncurried && body.getAppNumArgs == fact.appliedArgs do return none
  if ← forallTelescope (← getConstInfo name).type fun ys _ => ys.anyM fun y => do
      return !(← y.fvarId!.getBinderInfo).isInstImplicit && (← isProp (← inferType y)) then
    return none
  let arguments := fact.mainArgs.map body.getArg!
  unless ← arguments.anyM fun a => return (← inferType a).containsFVar x.fvarId! do return none
  let argument ← arguments.pop.foldrM (fun a z => mkAppM ``Prod.mk #[a, z]) arguments.back!
  let (_, _, statement) ← forallMetaTelescopeReducing
    (← inferType (← mkConstWithFreshMVarLevels name))
  let some (view, equation) ← withLocalDeclD `z (← inferType argument) fun z => do
      let some (v, h) ← codesView (statement.getArg! 0) z | return none
      return some (← mkLambdaFVars #[z] v, ← mkLambdaFVars #[z] h) | return none
  let some atType ← observing? (instantiateFact name (some (argument, body))) | return none
  let some atCodes ← observing? (instantiateFact name none) | return none
  return some (argument, view, equation, atCodes, atType)

open Lean Meta Mathlib.Meta.FunProp in
/-- A function with one program at every type applied to arguments whose types depend on the
input: the tuple of the arguments is computed and the program runs on its code
(`HasProgram.comp_codes`). The growth is stated on the arguments, not on their codes. -/
private def codesComposition (search : Lean.Expr → FunPropM (Option Result))
    (goal : Lean.Expr) : FunPropM (Option Result) := do
  let some (argument, view, equation, atCodes, atTypes, viewed) ←
      lambdaTelescope (← etaExpand (goal.getArg! 4)) fun xs body => do
        let #[x] := xs | return none
        let body := body.headBeta
        -- A projection of the input is a subtree of its code, read by the structural stage.
        if ← Search.isProjectionOf x body then return none
        let some name := body.getAppFn.constName? | return none
        for fact in ← getTheoremsForFunction name ``HasProgram do
          let some (argument, view, equation, atCodes, atType) ← codesInstance x body fact |
            continue
          return some (← mkLambdaFVars xs argument, ← mkLambdaFVars xs view,
            ← mkLambdaFVars xs equation, atCodes, ← mkLambdaFVars xs atType,
            ← mkLambdaFVars xs (equation.beta #[argument]))
        return none
    | return none
  let some hx ← search (← programGoal argument) | return none
  let result ← mkAppM ``HasProgram.comp_codes #[hx.proof, view, equation, atCodes, atTypes]
  let type ← whnfR (← inferType result)
  -- The growth at the codes is restated on the arguments.
  let lemmas ← [``encode_list_codes, ``List.length_map, ``Tree.encode_self].foldlM
    (·.addConst ·) ({} : SimpTheorems)
  let codes ← Simp.mkContext (simpTheorems := #[← lemmas.add (.other `codes) #[] viewed])
  let comparisons ← [6, 7].mapM fun i => do
    let growth := type.getArg! i
    match (← simp growth codes).1.proof? with
    | some equation => mkAppM ``dominated_of_eq #[equation]
    | none => mkAppM ``Dominated.refl #[growth]
  return some ⟨← mkAppM ``HasProgram.mono #[result, comparisons[0]!, comparisons[1]!]⟩

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
private partial def sourceSearch (session : Search.Session)
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
  if let some proof := (← session.results.get)[key]? then
    if proof.getUsedConstants.all (← getEnv).contains then
      if ← isDefEq goal (← inferType proof) then return some ⟨proof⟩
  -- Only requests with unconstrained growth are failures of the source function itself.
  let unconstrained := !goal.isAppOfArity ``HasProgram 8 ||
    (goal.getAppArgs[6]!.isMVar && goal.getAppArgs[7]!.isMVar)
  if unconstrained && (← get).failureCache.contains key then return none
  if ancestors.contains key then return none
  let ancestors := ancestors.push key
  increaseSteps
  let restore ← Search.checkpoint
  let search := sourceSearch session ancestors
  let context ← read
  -- A branch has a different local context: only fuel, path and diagnostics cross this boundary.
  let query := sourceQuery search context
  let finish (result : Option Result) : FunPropM (Option Result) := do
    if let some r := result then
      let proof ← instantiateMVars
        (← typedSourceImplementation (← instantiateMVars goal) (← instantiateMVars r.proof))
      unless key.hasFVar || key.hasMVar || proof.hasFVar || proof.hasMVar do
        session.results.modify (·.insert key proof)
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
  -- A field of a field of the input is a subtree of its code; a closed value is a constant.
  if goal.isAppOfArity ``HasProgram 8 then
    if let some r ← Search.attempt (fieldRule goal) then return ← finish (some r)
    if let some r ← Search.attempt (closedRule goal) then return ← finish (some r)
  -- Encoding an unsupported source call is not an instruction to translate its encoder.
  let encodedCall ← lambdaTelescope f fun _ body => do
    unless body.isAppOfArity ``UniqueEncoding.encode 4 do return none
    let some name := body.appArg!.getAppFn.constName? | return none
    return if ← isRecursiveDefinition name then some name else none
  -- Rules recursively use this driver, including callbacks; no preliminary scan is needed.
  let data ← getFunctionData? f defaultUnfoldPred
  let result ← match data with
    | .lam f => do
      let target := goal.setArg decl.funArgId f
      if let some r ← Search.lambdaRules search decl .pi target then return some r
      -- A function literal is a table built pointwise, through its view.
      Search.attempt (viewRule search target)
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
      let info? ← match d.fn with
        | .const name _ => pure (some (← getConstInfo name))
        | _ => pure none
      -- A constructor of values at hand, such as a pair, is assembled from subtrees of the input's
      -- code; a constructor has no implementation to select.
      if info?.any (·.isCtor) then
        if let some r ← Search.attempt (assembleRule goal (target.getArg! decl.funArgId)) then
          return some r
      if let some r ← rules false then return some r
      -- A `match` on a part of the input is eliminated by its type's elimination rule.
      if let .const name _ := d.fn then
        if (← getMatcherInfo? name).isSome || isCasesOnLike env name || isRecCore env name then
          if let some r ← Search.attempt (casesRule search target) then return some r
      -- A function with one program at every type, at an argument whose type depends on the input.
      if let .const name _ := d.fn then
        unless (← getTheoremsForFunction name ``HasProgram).isEmpty do
          if let some r ← Search.attempt (codesComposition search target) then return some r
      -- A value with a view is computed through it.
      if let some r ← Search.attempt (viewRule search target) then return some r
      if let some name := encodedCall then
        if let some r ← rules true then return some r
        session.reject ancestors (Search.recursionMessage name)
        return none
      -- So is a definition whose value is such a constructor, after its selected implementations;
      -- otherwise a constructor is built from its fields, also as the value of a definition.
      if info?.any fun info => info.isCtor || info.isDefinition then
        if info?.any (·.isDefinition) then
          if let some r ← Search.attempt (assembleRule goal (target.getArg! decl.funArgId)) then
            return some r
        if let some r ← Search.attempt (constructorRule search target) then return some r
      -- Subcall specifications need structural decomposition before their fallback rules:
      -- otherwise lookup of a composite table can recursively request rebuilding that table.
      if let some r ← rules true then return some r
      -- A table is read after stored subtrees are extracted.
      if let some r ← Search.attempt (viewRule search target (reads := true)) then return some r
      -- An encoder describes representation; unfolding it does not select an algorithm.
      if d.fn.isConstOf ``UniqueEncoding.encode then
        session.reject ancestors m!"source translation: no implementation for the encoded result; \
          select a rule scope with `using`, or register a function equality with `[source]`"
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
        return ← sourceSearch session ancestors (target.setArg decl.funArgId f)
      -- A local function is implemented only by a local certificate.
      if d.fn.isFVar && d.fn != d.mainVar then
        session.reject ancestors m!"source translation: `{d.fn}` needs an implementation (a \
          `HasProgram` hypothesis)"
        return none
      if let .const name _ := d.fn then
        if ← isRecursiveDefinition name then
          session.reject ancestors (Search.recursionMessage name)
          return none
        unless (← getMatcherInfo? name).isSome do
          if let some body ← unfoldSource? (← session.roots.get)
              (Mor.mkAppN d.fn d.args) then
            let f ← mkLambdaFVars #[d.mainVar] body
            -- A source that is another definition up to uncurrying is translated as that one.
            if (← session.roots.get).contains name then addSourceRoot session f
            return ← sourceSearch session ancestors (target.setArg decl.funArgId f)
          if (← getConstInfo name).isDefinition then
            session.reject ancestors m!"source translation: `{.ofConstName name}` needs a \
              selected implementation (register one with `[source]`, or choose replacement \
              source with `via`)"
            return none
      if let .comp outer inner := decomposition then
        if let some r ← Search.lambdaRules search decl .comp target
            (some (outer, inner)) then
          return some r
      return none
  finish result

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

open Lean Meta Elab Tactic Mathlib.Meta.FunProp in
/-- Certify a callback named in a method syntax completely, sharing the method's session.
The source rules in scope are those activated by `withSourceSpecs`. -/
def certifyCallback (session : Search.Session) (method name : Name) (callback : Lean.Expr) :
    TacticM Lean.Expr := do
  if callback.hasExprMVar then
    throwError "source {method}: provide a concrete `{name}` callback"
  addSourceRoot session callback
  session.failure.set none
  let some proof ← sourceQuery (sourceSearch session #[]) (← sourceContext)
      (← programGoal callback) |
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
/-- Translate the main `HasProgram` goal and return the remaining obligations. -/
private def proveSource (scope : Option Ident := none) (replacement : Option Term := none) :
    TacticM (List MVarId) :=
    withSourceSpecs scope <| withMainContext do
  let goal ← getMainGoal
  let saved ← saveState
  let session ← Search.Session.create
  let context ← sourceContext
  try
    let original := (← instantiateMVars (← goal.getType)).consumeMData
    unless original.isAppOfArity ``HasProgram 8 do
      throwError "source_fun_prop expects a HasProgram goal, got {original}"
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
    -- The requested program, like the growth, is compared with the produced one at the end.
    let program ← mkFreshExprMVar (← inferType original.getAppArgs[5]!)
    let target := (original.setArg 4 source).setArg 5 program
      |>.setArg 6 (← mkFreshExprMVar growth) |>.setArg 7 (← mkFreshExprMVar growth)
    let some result ← sourceQuery (sourceSearch session #[]) context target |
      session.report
    let result ← match equality with
      | none => pure result
      | some h => mkAppM ``HasProgram.congr #[result, ← mkEqSymm h]
    let obligations ← finishProgram goal result
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
  let implementation ← Term.elabTerm (← `(Recursion.hasProgram $(← Term.exprToSyntax r)
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
  let result ← mkAppM ``HasProgram.of_encode #[equality, implementation]
  let comparisons ← finishProgram goal result
  trace[source.translation] "source recursion: program combined"
  setGoals rest
  return obligations ++ comparisons
open Lean Elab Tactic in
/-- Close the growth comparisons among `goals` by the discharger, `dominated` unless one is given;
a comparison it does not close completely is left unchanged. -/
def dischargeGrowth (disch : Option (TSyntax ``Lean.Parser.Tactic.discharger))
    (goals : List MVarId) : TacticM (List MVarId) := do
  let tac ← match disch with
    | none => `(tacticSeq| dominated)
    | some d => match d with
      | `(Lean.Parser.Tactic.discharger| (discharger := $tac)) => pure tac
      | _ => throwUnsupportedSyntax
  goals.filterM fun goal => do
    unless (← instantiateMVars (← goal.getType)).consumeMData.isAppOf ``Dominated do return true
    let saved ← saveState
    try
      if (← evalTacticAt tac goal).isEmpty then return false
    catch _ => pure ()
    saved.restore
    return true

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| source_fun_prop $[$disch]? $[using $scope:ident]? $[via $replacement]?) => do
    let obligations ← dischargeGrowth disch (← proveSource scope replacement)
    setGoals (obligations ++ (← getGoals))
open Lean Meta Elab Tactic in
/-- Translate a source function and reduce its model time-space bound to arithmetic goals. -/
private def modelFunPropCore (disch : Option (TSyntax ``Lean.Parser.Tactic.discharger))
    (translate : TacticM (List Lean.MVarId)) : TacticM Unit := do
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
    evalTactic (← `(tactic| refine HasProgram.computableWithGrowth_of_dominated
      (program := ?program) (hf := ?implementation) (t := ?time_bound) (p := ?peak_bound)
      ?time ?peak))
  else if let some (t, s) := powers then
    evalTactic (← `(tactic| refine HasProgram.mem_ftisp_pow (program := ?program)
      (hf := ?implementation) (t := $(quote t)) (s := $(quote s)) (by decide)))
  else
    evalTactic (← `(tactic| refine HasProgram.mem_ftisp_of_dominated (program := ?program)
      (hf := ?implementation) (t := ?time_bound) (p := ?peak_bound) ?time ?peak))
  let pending ← getGoals
  let some implementation ← pending.findM? fun g =>
      return (← g.getType).consumeMData.isAppOf ``HasProgram |
    throwError "source model: missing implementation"
  setGoals [implementation]
  let obligations ← translate
  let remaining ← (pending.erase implementation).filterM fun g => return !(← g.isAssigned)
  setGoals ((← dischargeGrowth disch (obligations ++ remaining)) ++ originalGoals.drop 1)

open Lean Elab Tactic in
def modelFunProp (disch : Option (TSyntax ``Lean.Parser.Tactic.discharger))
    (translate : TacticM (List Lean.MVarId)) : TacticM Unit := do
  let saved ← saveState
  try modelFunPropCore disch translate
  catch ex => saved.restore; throw ex

/-- Reduce a model time-space bound of a source function to its translation and arithmetic goals;
the options and methods are those of `source_fun_prop`, and the growth comparisons left are
discharged as there. -/
syntax (name := modelFunPropStx) "model_fun_prop" (Lean.Parser.Tactic.discharger)?
  (" using " ident)? (" via " term)? : tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| model_fun_prop $[$disch]? $[using $scope:ident]? $[via $replacement]?) =>
    modelFunProp disch (proveSource scope replacement)

@[tactic_alt modelFunPropStx]
syntax "model_fun_prop" (Lean.Parser.Tactic.discharger)? " using " sourceRecursion
  (" using " ident)? : tactic
@[tactic_alt sourceFunProp]
syntax "source_fun_prop" (Lean.Parser.Tactic.discharger)? " using " sourceRecursion
  (" using " ident)? : tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| model_fun_prop $[$disch]? using $method:sourceRecursion $[using $scope:ident]?) =>
    modelFunProp disch (proveRecursion method scope)
  | `(tactic| source_fun_prop $[$disch]? using $method:sourceRecursion $[using $scope:ident]?) => do
    let obligations ← dischargeGrowth disch (← proveRecursion method scope)
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
          return type.isAppOfArity ``HasProgram 8 then
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
          let goal ← mkFreshExprSyntheticOpaqueMVar (← programGoal g)
          let action : TermElabM Unit := do
            discard <| Tactic.run goal.mvarId! do
              discard <| proveSource scope
          discard <| action.run {} {}
          let proof ← instantiateMVars goal
          if proof.hasExprMVar || proof.hasSorry then
            throwError "the selected source implementation has unfinished obligations"
          let result ← mkAppM ``HasProgram.congr
            #[proof, ← mkEqSymm (mkAppN equality parameters)]
          let certificate ← withoutExporting do
            let certificate ← mkFreshUserName (name ++ `sourceProgram)
            let closure ← Closure.mkValueTypeClosure (← inferType result) result false
            addDecl <| .thmDecl { name := certificate, type := closure.type, value := closure.value
                                  levelParams := closure.levelParams.toList }
            pure certificate
          checkUniqueSource certificate
          sourceSavedImplementationExt.add certificate kind
          addTheorem certificate kind 1001
    catch ex =>
      setEnv saved
      throw ex
}

end Complexity.TreeProgram.Source
