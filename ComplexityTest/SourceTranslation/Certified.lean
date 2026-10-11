/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Complexity.Tactic.TreeProgram.Library

open Complexity TreeProgram Complexity.TreeProgram.Source

namespace ComplexityTest.SourceTranslation.Certified

attribute [local fun_prop] Implementation.identity Implementation.comp
  Implementation.reverse Implementation.map Implementation.ite Implementation.fst Implementation.snd
  Implementation.pair Implementation.append

def reverse : Implementation (List.reverse : List Bool → List Bool) := by fun_prop

def twice : Implementation (fun xs : List Bool => xs.reverse.reverse) := by fun_prop

def mapReverse : Implementation (List.map (List.reverse : List Bool → List Bool)) := by fun_prop

example : reverse.program = (Implementation.reverse (α := Bool)).program := rfl

example : twice.program =
    ((Implementation.reverse (α := Bool)).comp Implementation.reverse).program := rfl

example : twice.evaluate =
    ((Implementation.reverse (α := Bool)).comp Implementation.reverse).evaluate := rfl

example : mapReverse.program = (Implementation.reverse (α := Bool)).map.program := rfl

-- These evaluate the selected programs, not an existential certificate's chosen witness.
/-- info: 9 -/
#guard_msgs in
#eval (reverse.program Value.input).build 1 |>.2.1

/-- info: 17 -/
#guard_msgs in
#eval (twice.program Value.input).build 1 |>.2.1

/-- info: 25 -/
#guard_msgs in
#eval (mapReverse.program Value.input).build 1 |>.2.1

universe u v w

section

variable {α : Type u} {β : Type v} {γ : Type w}
  [UniqueEncoding Tree α] [UniqueEncoding Tree β] [UniqueEncoding Tree γ]
  {f : α → β} {g : β → γ}

def localComp (hf : Implementation f) (hg : Implementation g) :
    Implementation (fun x => g (f x)) := by fun_prop

example (hf : Implementation f) (hg : Implementation g) :
    (localComp hf hg).evaluate = (hf.comp hg).evaluate := rfl

def localMap (hf : Implementation f) : Implementation (List.map f) := by fun_prop

example (hf : Implementation f) : (localMap hf).program = hf.map.program := rfl

end

-- Repeated calls exercise reuse of a Type-valued result in the search cache.
def threeReverses : Implementation (fun xs : List Bool => xs.reverse.reverse.reverse) := by
  fun_prop

example : threeReverses.evaluate =
    (((Implementation.reverse (α := Bool)).comp Implementation.reverse).comp
      Implementation.reverse).evaluate := rfl

-- The public resource proposition remains an immediate consequence of the same object.
example : Realizes (fun xs : List Bool => xs.reverse.reverse)
    (compBounds List.reverse reverseBounds reverseBounds) := twice.realizes

-- One program for each runtime index does not provide one program for the whole input.
example (f : ℕ → Bool → Bool) (_h : ∀ n, Implementation (f n)) : True := by
  fail_if_success have : Implementation (fun x : ℕ × Bool => f x.1 x.2) := by fun_prop
  trivial

def negateBool : Bool → Bool
  | true => false
  | false => true

def negateBoolImpl : Implementation negateBool := by source_cases

/-- info: 2 -/
#guard_msgs in
#eval (negateBoolImpl.program Value.input).build 1 |>.2.1

example : ∃ b, Realizes negateBool b := ⟨_, by source_cases⟩

private def unequalBranches (x : Bool × List Bool) : List Bool :=
  if x.1 then x.2 else true :: x.2

-- Structural correctness is checked before the supplied, input-sensitive budget.
example : Realizes unequalBranches
    ⟨fun x => if x.1 then 3 else 5,
      fun x => max ⌜x⌝ₜ.size ⌜unequalBranches x⌝ₜ.size⟩ := by
  source_cases

example : True := by
  fail_if_success
    have : Realizes unequalBranches ⟨fun _ => 0, fun _ => 0⟩ := by source_cases
  trivial

private def nonemptyTailReverse (x : {xs : List Bool // xs ≠ []}) : List Bool :=
  match h : x.1 with
  | [] => False.elim (x.2 h)
  | _ :: tail => tail.reverse

-- Impossible branches are replayed, and proof fields are erased from runtime environments.
example : ∃ b, Realizes nonemptyTailReverse b := ⟨_, by source_fun_prop⟩

def optionalReverse : Option (List Bool) → List Bool
  | none => []
  | some xs => xs.reverse

def optionalReverseImpl : Implementation optionalReverse := by source_calls

/-- info: 11 -/
#guard_msgs in
#eval (optionalReverseImpl.program Value.input).build 1 |>.2.1

def singletonIndexed (x : Σ n, List (Fin n)) : Σ n, List (List (Fin n)) := ⟨x.1, [x.2]⟩

def singletonIndexedImpl : Implementation singletonIndexed := by
  source_dependent
  source_cases

/-- info: 2 -/
#guard_msgs in
#eval (singletonIndexedImpl.program Value.input).build 1 |>.2.1

opaque legacy (xs : List Bool) : List Bool := xs

def mixedCalls (x : Bool × List Bool) : List Bool :=
  if x.1 then x.2.reverse else legacy x.2

-- Only the opaque compatibility leaf requires choosing an existential witness.
noncomputable def mixedCallsImpl (b : Bounds (List Bool)) (_h : Realizes legacy b) :
    Implementation mixedCalls := by source_calls

def conditionalReverse : Implementation
    (fun x : Bool × List Bool => if x.1 then x.2.reverse else x.2) := by source_fun_prop

/-- info: 39 -/
#guard_msgs in
#eval (conditionalReverse.evaluate (true, [true, false])).cost.time

/-- info: 5 -/
#guard_msgs in
#eval (conditionalReverse.evaluate (false, [true, false])).cost.time

example : conditionalReverse.bounds =
    iteBounds Prod.fst projectionBounds
      (compBounds Prod.snd projectionBounds reverseBounds) projectionBounds := by
  simp [conditionalReverse]

def reverseAlias (xs : List Bool) := xs.reverse

def reverseAliasImpl : Implementation reverseAlias := by source_fun_prop

example : reverseAliasImpl.evaluate = (Implementation.reverse (α := Bool)).evaluate := rfl

example : reverseAliasImpl.program = (Implementation.reverse (α := Bool)).program := rfl

def aliasInLet (xs : List Bool) :=
  let ys := reverseAlias xs
  reverseAlias ys ++ xs

example : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace aliasInLet
    (fun n => 52 * n + 39) (fun n => k * (2 * n + 3)) := by
  model_fun_prop

-- Encoding proofs retain their source type even when both encodings reduce to `Tree.nil`.
example {α : Type*} [UniqueEncoding Tree α] :
    ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace
      (fun x : Option (List α) => match x with | none => [] | some xs => xs.reverse)
      (fun n => 13 * n + 20) (fun n => k * (n + 3)) := by
  model_fun_prop

end ComplexityTest.SourceTranslation.Certified
