/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Complexity.Tactic.TreeProgram.Library

open Complexity TreeProgram
open Complexity.TreeProgram.Source (Bounds Realizes identityBounds identity_realizes unit_realizes)
namespace ComplexityTest.SourceTranslation.Search

private def one {α : Type*} : Bounds α := ⟨fun _ => 1, fun _ => 1⟩

-- Test transactional routing without the frontend's preferred zero-cost implementations.
open Lean Meta Elab Tactic Mathlib.Meta.FunProp in
private def checkRuleRouting
    (rules : IO.Ref (Array Name × Bool) → Expr → FunPropM (Option Result)) : TacticM Unit := do
  let goal ← getMainGoal
  let target ← goal.getType
  let budget := target.getAppArgs[5]!
  let rejected ← IO.mkRef false
  let context : Mathlib.Meta.FunProp.Context := { disch := fun type => do
    if type.isConstOf ``False then
      unless !(← instantiateMVars budget).isMVar &&
          (← isDefEq budget (← mkAppOptM ``identityBounds #[some (mkConst ``Bool)])) do
        throwError "the rejected rule did not first assign its budget"
      rejected.set true
    tacticToDischarge (← `(tactic| with_reducible assumption)) type }
  let env ← getEnv
  let state : Mathlib.Meta.FunProp.State :=
    { morTheorems := morTheoremsExt.getState env,
      transitionTheorems := transitionTheoremsExt.getState env }
  let unfolded ← IO.mkRef (#[], false)
  let (some result, _) ← (rules unfolded target context).run state |
    throwError "rule search failed"
  unless ← rejected.get do throwError "the failing rule was not attempted first"
  goal.assign result.proof
  replaceMainGoal []

open Lean Meta Elab Tactic Mathlib.Meta.FunProp in
private def checkLambdaRules (kind : LambdaTheoremType) : TacticM Unit :=
  checkRuleRouting fun unfolded target => do
    let some (decl, _) ← getFunProp? target | throwError "expected a function property"
    Source.Search.lambdaRules unfolded (fun _ => pure none) decl kind target

section Identity

@[local fun_prop] private theorem blocked (h : False) :
    Realizes (id : Bool → Bool) identityBounds := h.elim

@[local fun_prop] private theorem available : Realizes (id : Bool → Bool) one :=
  identity_realizes.mono fun _ => by simp [identityBounds, one]

example : ∃ b, Realizes (id : Bool → Bool) b ∧ ∀ x, b.time x = 1 := by
  refine ⟨_, by run_tac checkLambdaRules .id, ?_⟩
  intro x
  rfl

end Identity

section Constant

@[local fun_prop] private theorem blockedConstant (h : False) :
    Realizes (fun _ : Bool => ()) identityBounds := h.elim

@[local fun_prop] private theorem availableConstant : Realizes (fun _ : Bool => ()) one :=
  unit_realizes.mono fun _ => by simp [identityBounds, one]

example : ∃ b, Realizes (fun _ : Bool => ()) b ∧ ∀ x, b.time x = 1 := by
  refine ⟨_, by run_tac checkLambdaRules .const, ?_⟩
  intro x
  rfl

end Constant

section Composition

-- Selected callback implementations compose with their exact budgets.
example (f g : Bool → Bool) (hf : Source.Implementation f) (hg : Source.Implementation g) :
    ∃ b, Realizes (fun x => g (f x)) b ∧
      ∀ x, b.time x = hf.bounds.time x + hg.bounds.time (f x) := by
  refine ⟨_, by source_fun_prop, ?_⟩
  intro x
  rfl

-- Let sharing also uses the same composition rules; its exact budget is retained.
example (f : Bool → Bool) (g : Bool × Bool → Bool)
    (hf : Source.Implementation f) (hg : Source.Implementation g) :
    ∃ b, Realizes (fun x => let y := f x; g (x, y)) b ∧
      ∀ x, b.time x = hf.bounds.time x + 1 + hg.bounds.time (x, f x) := by
  refine ⟨_, by source_fun_prop, ?_⟩
  intro x
  simp only [Source.compBounds, Source.pairBounds, Nat.zero_add]

end Composition

section Transition

private def Available (f : Bool → Option Bool) : Prop := Realizes f one

@[local fun_prop] private theorem blockedTransition (f : Bool → Option Bool) (b : Bounds Bool)
    (_hb : b = identityBounds) (h : False) : Realizes f b := h.elim

@[local fun_prop] private theorem availableTransition (f : Bool → Option Bool) (b : Bounds Bool)
    (hb : b = one) (h : Available f) : Realizes f b := by
  subst b
  exact h

-- Exercise transition routing directly, independently of frontend implementation selection.
open Lean Meta Elab Tactic Mathlib.Meta.FunProp in
example (f : Bool → Option Bool) (h : Available f) : ∃ b, Realizes f b ∧ b = one := by
  have _hz : (identityBounds : Bounds Bool) = identityBounds := rfl
  have _ho : (one : Bounds Bool) = one := rfl
  refine ⟨_, by
    run_tac checkRuleRouting fun unfolded target =>
      Source.Search.transitionRules unfolded (fun _ => pure none) target
    , ?_⟩
  rfl

end Transition

section CandidateFailure

private def unsupported : List Bool → List Bool
  | [] => []
  | x :: xs => unsupported xs ++ [x]

private def chosen (xs : List Bool) := xs.reverse

private theorem availableReverse : Realizes chosen Source.reverseBounds := Source.reverse_realizes

@[source_bounds↓] private noncomputable def availableImplementation : Source.Implementation chosen :=
  availableReverse.implementation

@[source_bounds↓] private noncomputable def needsRecursive (_h : Source.Implementation unsupported) :
    Source.Implementation chosen := availableImplementation

-- Equal-key function rules visit the most recently registered candidate first.
attribute [local fun_prop] availableImplementation needsRecursive

example : Realizes chosen Source.reverseBounds := by source_fun_prop

example : ∃ b, Realizes chosen b ∧ b = Source.reverseBounds := by
  refine ⟨_, by source_fun_prop, ?_⟩
  rfl

example : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace chosen
    (fun n => 13 * n + 12) (fun n => k * (n + 3)) := by
  model_fun_prop

end CandidateFailure

private def uncertified : List Bool → List Bool
  | [] => []
  | b :: bs => b :: b :: uncertified bs

-- An encoded result still reports the source operation, not the implementation of its encoder.
/--
error: source translation: `ComplexityTest.SourceTranslation.Search.uncertified` needs a registered implementation (choose replacement source with `via`, or register a function equality with `[source]`)
source path: fun xs => encode Complexity.Tree (uncertified xs) → fun xs => uncertified xs
-/
#guard_msgs in
example : ∃ b, Realizes (fun xs => ⌜uncertified xs⌝ₜ) b := ⟨_, by source_fun_prop⟩

section LocalPriority

-- Existence proofs do not select a callback program; import the chosen certificate explicitly.
example (f : Bool → Bool) (b₁ b₂ : Bounds Bool)
    (h₁ : Realizes f b₁) (_h₂ : Realizes f b₂) : True := by
  fail_if_success have : Source.Implementation f := by source_fun_prop
  let callback := h₁.implementation
  have : Source.Implementation f := by source_fun_prop
  have : ∃ b, Realizes (fun x : ℕ × Bool => f^[x.1] x.2) b := ⟨_, by source_fun_prop⟩
  trivial

-- The local specification is an explicit choice, even when a certified default is registered.
example (b : Bounds (List Bool)) (h : Realizes (List.reverse : List Bool → List Bool) b) :
    ∃ c, Realizes (List.reverse : List Bool → List Bool) c ∧ c = b := by
  let selected := h.implementation
  refine ⟨_, by source_fun_prop, ?_⟩
  rfl

example (h : Source.Implementation (List.reverse : List Bool → List Bool)) :
    let p : Source.Implementation (List.reverse : List Bool → List Bool) := by source_fun_prop
    p = h := by
  rfl

private def legacy (xs : List Bool) := xs.reverse

@[local fun_prop] private def legacyDefault : Source.Implementation legacy :=
  Source.Implementation.reverse.congr rfl

example (b : Bounds (List Bool)) (h : Realizes legacy b) :
    ∃ c, Realizes legacy c ∧ c = b := by
  let selected := h.implementation
  refine ⟨_, by source_fun_prop, ?_⟩
  rfl

example (b : Bounds Bool) (h : Realizes (id : Bool → Bool) b) :
    ∃ c, Realizes (id : Bool → Bool) c ∧ c = b := by
  let selected := h.implementation
  refine ⟨_, by source_fun_prop, ?_⟩
  rfl

example (b : Bounds Bool) (h : Realizes (fun _ : Bool => ()) b) :
    ∃ c, Realizes (fun _ : Bool => ()) c ∧ c = b := by
  let selected := h.implementation
  refine ⟨_, by source_fun_prop, ?_⟩
  rfl

private def doubleReverse (xs : List Bool) := xs.reverse.reverse

@[local fun_prop] private def doubleReverseDefault : Source.Implementation doubleReverse :=
  Source.Implementation.reverse.comp Source.Implementation.reverse

-- A local `have` works too; its semantic proof chooses the identity implementation.
example : ∃ b, Realizes doubleReverse b ∧ b = identityBounds := by
  have fast : Realizes doubleReverse identityBounds := by
    have he : doubleReverse = (id : List Bool → List Bool) := by
      funext xs
      exact List.reverse_reverse xs
    rw [he]
    exact identity_realizes
  let selected := fast.implementation
  refine ⟨_, by source_fun_prop, ?_⟩
  rfl

end LocalPriority

section RuleStages

private def stored (x : Bool × Bool) : Bool := x.1

private def storedBounds (time : ℕ) : Bounds (Bool × Bool) :=
  { Source.projectionBounds with time := fun _ => time }

private theorem storedSpec (time : ℕ) (h : 1 ≤ time) : Realizes stored (storedBounds time) :=
  Source.fst_realizes.mono fun _ => ⟨h, le_rfl⟩

section SelectedProgram

private def storedImplementation (time : ℕ) (h : 1 ≤ time) : Source.Implementation stored :=
  Source.Implementation.fst.rebudget (storedBounds time) (fun _ => ⟨h, le_rfl⟩)

private def rebuilt : Source.Implementation stored :=
  (Source.Implementation.fst.pair Source.Implementation.snd).comp Source.Implementation.fst

@[source_bounds↓] private def preferred : Source.Implementation stored :=
  rebuilt.rebudget ⟨fun _ => 7, rebuilt.bounds.peak⟩ (fun _ => ⟨by change 4 ≤ 7; decide, le_rfl⟩)
@[source_bounds↓] private def secondary := storedImplementation 9 (by decide)
@[source_bounds↓] private def fallback := storedImplementation 99 (by decide)

attribute [local source_fallback] fallback

open Lean Meta Mathlib.Meta.FunProp in
run_elab do
  addTheorem ``preferred .local 20
  addTheorem ``secondary .local 10
  addTheorem ``fallback .local 2000

-- Ordinary rules precede structural projection even below the default priority.
-- Numerical priority still chooses between ordinary rules, independently of registration order.
example : ∃ b, Realizes stored b ∧ ∀ x, b.time x = 7 := by
  refine ⟨_, by source_fun_prop, ?_⟩
  intro x
  rfl

-- Check program selection directly. The lower-priority projection is different code.
example : (show Source.Implementation stored from by source_fun_prop).program =
    preferred.program := rfl

example : (preferred.program Value.input).build 1 |>.2.1 ≠
    ((secondary.program Value.input).build 1).2.1 := by decide

-- The one-step target needs the other program; budget failure must not select it.
example : True := by
  fail_if_success have : Realizes stored Source.projectionBounds := by source_fun_prop
  trivial

-- The selected program has another valid certificate; its code is unchanged.
example : Source.Implements preferred.program stored rebuilt.bounds := rebuilt.implements

section

attribute [local source_fallback] preferred secondary

-- A high-priority fallback never displaces the one-step stored-field projection.
example : ∃ b, Realizes stored b ∧ ∀ x, b.time x = 1 := by
  refine ⟨_, by source_fun_prop, ?_⟩
  simp

end
end SelectedProgram

section Certified

private def implementation : Source.Implementation stored :=
  Source.Implementation.fst.rebudget (storedBounds 11) fun _ => ⟨by simp [storedBounds], le_rfl⟩

open Lean Meta Mathlib.Meta.FunProp in
run_elab addTheorem ``implementation .local 10

example : ∃ b, Realizes stored b ∧ ∀ x, b.time x = 11 := by
  refine ⟨_, by source_fun_prop, ?_⟩
  intro x
  rfl

section
@[source_bounds↓] private noncomputable def higherPriority : Source.Implementation stored :=
  (storedSpec 7 (by decide)).implementation

open Lean Meta Mathlib.Meta.FunProp in
run_elab addTheorem ``higherPriority .local 20

-- Priority orders the already imported implementation candidates.
example : ∃ b, Realizes stored b ∧ ∀ x, b.time x = 7 := by
  refine ⟨_, by source_fun_prop, ?_⟩
  intro x
  rfl
end

attribute [local source_fallback] implementation

-- Structural projection still precedes fallback implementation rules.
example : ∃ b, Realizes stored b ∧ ∀ x, b.time x = 1 := by
  refine ⟨_, by source_fun_prop, ?_⟩
  simp

end Certified
end RuleStages

section SharedSession

private def branches (x : Bool × List Bool) : List Bool :=
  if x.1 then x.2.reverse else x.2

-- Each leaf fits separately, but branch callbacks must share the outer request's fuel.
set_option source.maxSteps 5 in
example : Source.Implementation (fun xs => branches (false, xs)) := by source_fun_prop

set_option source.maxSteps 5 in
example : Source.Implementation (fun xs => branches (true, xs)) := by source_fun_prop

/-- error: source translation: maximum number (5) of search steps exceeded -/
#guard_msgs in
set_option source.maxSteps 5 in
example : Source.Implementation branches := by source_calls

example : Source.Implementation branches := by source_calls

private opaque unavailable : Bool → Bool
private def twice (x : Bool) := unavailable (unavailable x)

@[local fun_prop] private def localScope
    (_h : ∀ _ : Source.Implementation unavailable,
      Source.Implementation (fun x => unavailable (unavailable x)))
    (g : Source.Implementation (fun x => unavailable (unavailable x))) :
    Source.Implementation twice := g

-- A successful premise under a temporary local certificate cannot populate the sibling's cache.
example : True := by
  fail_if_success have : Source.Implementation twice := by source_fun_prop
  trivial

open Lean Meta Elab Tactic in
example : True := by
  run_tac
    let session ← Source.Search.Session.create
    let rejected ← try
      let _ ← session.discharge #[] (throwError "fatal marker") (mkConst ``True)
      pure false
    catch ex => pure ((← ex.toMessageData.toString) == "fatal marker")
    unless rejected do throwError "an unexpected elaboration error was swallowed"
    evalTactic (← `(tactic| trivial))

end SharedSession

end ComplexityTest.SourceTranslation.Search
