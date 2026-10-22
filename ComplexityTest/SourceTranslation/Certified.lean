/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Complexity.Tactic.TreeProgram.Translation

open Complexity TreeProgram Complexity.TreeProgram.Source

namespace ComplexityTest.SourceTranslation.Certified

attribute [local fun_prop] Implementation.identity Implementation.comp
  Implementation.reverse Implementation.map Implementation.ite Implementation.fst Implementation.snd
  Implementation.pair Implementation.append

def reverse : Implementation (List.reverse : List Bool → List Bool)
    (fun xs => ⌜xs⌝ₜ.size) (fun xs => ⌜xs⌝ₜ.size) := by fun_prop

-- Ordinary `fun_prop` produces the structural growth of each call.
def twice := (by fun_prop : Implementation (fun xs : List Bool => xs.reverse.reverse) _ _)

example : Implementation (fun xs : List Bool => xs.reverse.reverse)
    (fun xs => ⌜xs⌝ₜ.size + ⌜xs.reverse⌝ₜ.size) (fun xs => max ⌜xs⌝ₜ.size ⌜xs.reverse⌝ₜ.size) :=
  twice

def mapReverse := (by fun_prop :
  Implementation (List.map (List.reverse : List Bool → List Bool)) _ _)

example : reverse.program = (Implementation.reverse (α := Bool)).program := rfl

example : twice.program =
    ((Implementation.reverse (α := Bool)).comp Implementation.reverse).program := rfl

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
  {f : α → β} {g : β → γ} {t p : α → ℕ} {u q : β → ℕ}

def localComp (hf : Implementation f t p) (hg : Implementation g u q) :
    Implementation (fun x => g (f x)) (fun x => t x + u (f x)) (fun x => max (p x) (q (f x))) := by
  fun_prop

example (hf : Implementation f t p) (hg : Implementation g u q) :
    (localComp hf hg).program = (hf.comp hg).program := rfl

example (hf : Implementation f t p) :
    (by fun_prop : Implementation (List.map f) _ _).program = hf.map.program := rfl

end

-- Repeated calls exercise reuse of a Type-valued result in the search cache.
def threeReverses := (by fun_prop :
  Implementation (fun xs : List Bool => xs.reverse.reverse.reverse) _ _)

example : threeReverses.program =
    (((Implementation.reverse (α := Bool)).comp Implementation.reverse).comp
      Implementation.reverse).program := rfl

-- The machine-level proposition is an immediate consequence of the same object.
example : ∃ b : Bounds (List Bool),
    Implements twice.program (fun xs : List Bool => xs.reverse.reverse) b :=
  let ⟨b, h, _⟩ := twice.sound; ⟨b, h⟩

-- One program for each runtime index does not provide one program for the whole input.
example (f : ℕ → Bool → Bool) (_h : ∀ n, Implementation (f n) (fun _ => 1) (fun _ => 1)) :
    True := by
  fail_if_success
    have := (by fun_prop : Implementation (fun x : ℕ × Bool => f x.1 x.2) _ _)
  trivial

def negateBool : Bool → Bool
  | true => false
  | false => true

def negateBoolImpl : Implementation negateBool (fun _ => 1)
    (fun x => max ⌜x⌝ₜ.size ⌜negateBool x⌝ₜ.size) := by source_cases

/-- info: 2 -/
#guard_msgs in
#eval (negateBoolImpl.program Value.input).build 1 |>.2.1

private def unequalBranches (x : Bool × List Bool) : List Bool :=
  if x.1 then x.2 else true :: x.2

-- Each case table entry is charged once; the unused branch is not added to the growth.
example : Implementation unequalBranches (fun _ => 1)
    (fun x => max ⌜x⌝ₜ.size ⌜unequalBranches x⌝ₜ.size) := by source_cases

private def nonemptyTailReverse (x : {xs : List Bool // xs ≠ []}) : List Bool :=
  match h : x.1 with
  | [] => False.elim (x.2 h)
  | _ :: tail => tail.reverse

-- Impossible branches are replayed, and proof fields are erased from runtime environments.
example := (by source_fun_prop : Implementation nonemptyTailReverse _ _)

def optionalReverse : Option (List Bool) → List Bool
  | none => []
  | some xs => xs.reverse

def optionalReverseImpl := (by source_calls : Implementation optionalReverse _ _)

/-- info: 11 -/
#guard_msgs in
#eval (optionalReverseImpl.program Value.input).build 1 |>.2.1

def singletonIndexed (x : Σ n, List (Fin n)) : Σ n, List (List (Fin n)) := ⟨x.1, [x.2]⟩

def singletonIndexedImpl := (by
  source_dependent
  source_cases : Implementation singletonIndexed _ _)

/-- info: 2 -/
#guard_msgs in
#eval (singletonIndexedImpl.program Value.input).build 1 |>.2.1

opaque legacy (xs : List Bool) : List Bool := xs

def mixedCalls (x : Bool × List Bool) : List Bool :=
  if x.1 then x.2.reverse else legacy x.2

-- An opaque call is supplied by one explicit implementation for every input.
example {t p : List Bool → ℕ} (legacyImplementation : Implementation legacy t p) :=
  (by source_calls : Implementation mixedCalls _ _)

-- Only the selected branch is charged, at its own structural cost.
def conditionalReverse : Implementation
    (fun x : Bool × List Bool => if x.1 then x.2.reverse else x.2)
    (fun x => (1 + if x.1 = true then 1 + ⌜x.2⌝ₜ.size else 1) + 1)
    (fun x => max ⌜x⌝ₜ.size (max ⌜x⌝ₜ.size
      (if x.1 = true then max ⌜x⌝ₜ.size ⌜x.2⌝ₜ.size else ⌜x⌝ₜ.size))) := by source_fun_prop

def reverseAlias (xs : List Bool) := xs.reverse

def reverseAliasImpl := (by source_fun_prop : Implementation reverseAlias _ _)

example : reverseAliasImpl.program = (Implementation.reverse (α := Bool)).program := rfl

def aliasInLet (xs : List Bool) :=
  let ys := reverseAlias xs
  reverseAlias ys ++ xs

-- Only the translated definition is unfolded; a called alias needs its own implementation.
/-- error: source translation: `reverseAlias` needs a selected implementation -/
#guard_msgs (substring := true) in
example := (by source_fun_prop : Implementation aliasInLet _ _)

section
attribute [local source] reverseAliasImpl

example := (by source_fun_prop : Implementation aliasInLet _ _)
end

-- Encoding proofs retain their source type even when both encodings reduce to `Tree.nil`.
example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop : Implementation
  (fun x : Option (List α) => match x with | none => [] | some xs => xs.reverse) _ _)

end ComplexityTest.SourceTranslation.Certified
