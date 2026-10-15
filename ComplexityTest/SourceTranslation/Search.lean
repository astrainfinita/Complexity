/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Complexity.Tactic.TreeProgram.Library

noncomputable section

open Complexity TreeProgram Complexity.TreeProgram.Source
namespace ComplexityTest.SourceTranslation.Search

section Composition

-- Selected callbacks compose their structural costs without choosing new programs.
example (f g : Bool → Bool) (hf : Implementation f) (hg : Implementation g) :
    ∃ impl : Implementation (fun x => g (f x)),
      ∀ x, impl.bounds.time x = hf.bounds.time x + hg.bounds.time (f x) := by
  refine ⟨by source_fun_prop, ?_⟩
  intro x
  simp [source_bounds]

-- Let sharing keeps the input and pays for the callback once.
example (f : Bool → Bool) (g : Bool × Bool → Bool)
    (hf : Implementation f) (hg : Implementation g) :
    ∃ impl : Implementation (fun x => let y := f x; g (x, y)),
      ∀ x, impl.bounds.time x = hf.bounds.time x + 1 + hg.bounds.time (x, f x) := by
  refine ⟨by source_fun_prop, ?_⟩
  intro x
  simp [source_bounds]

end Composition

section CandidateFailure

private def unsupported : List Bool → List Bool
  | [] => []
  | x :: xs => unsupported xs ++ [x]

private def chosen (xs : List Bool) := xs.reverse

private def availableImplementation : Implementation chosen := Implementation.reverse

private def needsRecursive (_h : Implementation unsupported) : Implementation chosen :=
  availableImplementation

-- A failed implementation premise is rolled back before another implementation rule is tried.
attribute [local fun_prop] availableImplementation needsRecursive

example : (show Implementation chosen from by source_fun_prop).program =
    availableImplementation.program := rfl

end CandidateFailure

private def uncertified : List Bool → List Bool
  | [] => []
  | b :: bs => b :: b :: uncertified bs

-- Encoded results report the unsupported source operation, not its encoder.
/--
error: source translation: `ComplexityTest.SourceTranslation.Search.uncertified` needs a registered implementation (choose replacement source with `via`, or register a function equality with `[source]`)
source path: fun xs => encode Complexity.Tree (uncertified xs) → fun xs => uncertified xs
-/
#guard_msgs in
example : Implementation (fun xs => ⌜uncertified xs⌝ₜ) := by source_fun_prop

section LocalPriority

-- A uniform chosen implementation is reusable at each runtime iteration.
example (f : Bool → Bool) (callback : Implementation f) :
    Implementation (fun x : ℕ × Bool => f^[x.1] x.2) := by source_fun_prop

-- Local selection takes precedence over a registered default.
example (h : Implementation (List.reverse : List Bool → List Bool)) :
    (show Implementation (List.reverse : List Bool → List Bool) from by source_fun_prop) = h := rfl

private def alternative (xs : List Bool) := xs.reverse

@[local fun_prop] private def defaultImplementation : Implementation alternative :=
  Implementation.reverse.congr rfl

example (selected : Implementation alternative) :
    (show Implementation alternative from by source_fun_prop) = selected := rfl

example (selected : Implementation (id : Bool → Bool)) :
    (show Implementation (id : Bool → Bool) from by source_fun_prop) = selected := rfl

example (selected : Implementation (fun _ : Bool => ())) :
    (show Implementation (fun _ : Bool => ()) from by source_fun_prop) = selected := rfl

private def doubleReverse (xs : List Bool) := xs.reverse.reverse

@[local fun_prop] private def doubleReverseDefault : Implementation doubleReverse :=
  Implementation.reverse.comp Implementation.reverse

-- A semantic equality can expressly select a faster program; growth search never does so.
example : (show Implementation doubleReverse from by
    let selected : Implementation doubleReverse := Implementation.identity.congr (by
      funext xs
      exact (List.reverse_reverse xs).symm)
    source_fun_prop).bounds.time [] = 0 := rfl

end LocalPriority

section RuleStages

private def stored (x : Bool × Bool) : Bool := x.1

private def rebuilt : Implementation stored :=
  (Implementation.fst.pair Implementation.snd).comp Implementation.fst

private def preferred : Implementation stored := rebuilt
private def secondary : Implementation stored := Implementation.fst
private def fallback : Implementation stored := Implementation.fst

attribute [local source_fallback] fallback

open Lean Meta Mathlib.Meta.FunProp in
run_elab do
  addTheorem ``preferred .local 20
  addTheorem ``secondary .local 10
  addTheorem ``fallback .local 2000

-- Ordinary registered rules precede structural projection, independent of their numeric cost.
example : (show Implementation stored from by source_fun_prop).program = preferred.program := rfl

example : (preferred.program Value.input).build 1 |>.2.1 ≠
    ((secondary.program Value.input).build 1).2.1 := by decide

example : (show Implementation stored from by source_fun_prop).bounds.time (false, false) = 4 := rfl

-- The selected implementation's semantic certificate stays attached to its own program.
example : Implements preferred.program stored rebuilt.bounds := rebuilt.implements

section
attribute [local source_fallback] preferred secondary

-- Fallback rules do not displace a structural projection.
example : (show Implementation stored from by source_fun_prop).bounds.time (false, false) = 1 := rfl
end

end RuleStages

section SharedSession

private def branches (x : Bool × List Bool) : List Bool :=
  if x.1 then x.2.reverse else x.2

-- Branch callbacks share the outer translation's search budget.
set_option source.maxSteps 5 in
example : Implementation (fun xs => branches (false, xs)) := by source_fun_prop

set_option source.maxSteps 5 in
example : Implementation (fun xs => branches (true, xs)) := by source_fun_prop

/-- error: source translation: maximum number (5) of search steps exceeded -/
#guard_msgs in
set_option source.maxSteps 5 in
example : Implementation branches := by source_calls

example : Implementation branches := by source_calls

private opaque unavailable : Bool → Bool
private def twice (x : Bool) := unavailable (unavailable x)

@[local fun_prop] private def localScope
    (_h : ∀ _ : Implementation unavailable,
      Implementation (fun x => unavailable (unavailable x)))
    (g : Implementation (fun x => unavailable (unavailable x))) : Implementation twice := g

-- A temporary local callback cannot populate a sibling premise's cache.
example : True := by
  fail_if_success have : Implementation twice := by source_fun_prop
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
