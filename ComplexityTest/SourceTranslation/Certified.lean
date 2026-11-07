/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Complexity.Tactic.TreeProgram.Primitives

open Complexity TreeProgram Complexity.TreeProgram.Source
open Complexity.TreeProgram.Source.Internal (HasProgramInO)

namespace ComplexityTest.SourceTranslation.Certified

-- The rules and the implementations the library selects with `program` (`List.reverse`,
-- `List.append`, the projections) are registered for `fun_prop` in the scope opened above.

theorem hasProgramIn_reverse : HasProgramIn (List.reverse : List Bool → List Bool) hole(⊢ program)
    IsO(fun xs => ⌜xs⌝ₜ.size) IsO(fun xs => ⌜xs⌝ₜ.size) := by
  abstract_hole program using programReverse
  refine HasProgramInO.toHasProgramIn ?_
  fill_hole program in fun_prop

-- Ordinary `fun_prop` produces the structural growth of each call.
def hasProgramInO_twice := (by
  abstract_hole program using programTwice
  fill_hole program in fun_prop :
    HasProgramInO (fun xs : List Bool => xs.reverse.reverse) hole(⊢ program) _ _)

example : HasProgramInO (fun xs : List Bool => xs.reverse.reverse) programTwice
    (fun xs => ⌜xs⌝ₜ.size + ⌜xs.reverse⌝ₜ.size) (fun xs => max ⌜xs⌝ₜ.size ⌜xs.reverse⌝ₜ.size) :=
  hasProgramInO_twice

example := (by fun_prop :
  HasProgramInO (List.map (List.reverse : List Bool → List Bool)) (List.Code.map List.Code.reverse) _ _)

example : programReverse = List.Code.reverse := rfl

example : programTwice = fun v => List.Code.reverse v >>= List.Code.reverse := rfl

-- These evaluate the selected programs.
/-- info: 9 -/
#guard_msgs in
#eval (programReverse Value.input).build 1 |>.2.1

/-- info: 17 -/
#guard_msgs in
#eval (programTwice Value.input).build 1 |>.2.1

/-- info: 25 -/
#guard_msgs in
#eval (List.Code.map List.Code.reverse Value.input).build 1 |>.2.1

universe u v w

section

variable {α : Type u} {β : Type v} {γ : Type w}
  [UniqueEncoding Tree α] [UniqueEncoding Tree β] [UniqueEncoding Tree γ]
  {f : α → β} {g : β → γ} {pf pg : Value → Code Value} {t p : α → ℕ} {u q : β → ℕ}

example (hf : HasProgramInO f pf t p) (hg : HasProgramInO g pg u q) :
    HasProgramInO (fun x => g (f x)) (fun v => pf v >>= pg) (fun x => t x + u (f x))
      (fun x => max (p x) (q (f x))) := by
  fun_prop

example (hf : HasProgramInO f pf t p) :=
    (by fun_prop : HasProgramInO (List.map f) (List.Code.map pf) _ _)

end

-- Repeated calls exercise reuse of a result in the search cache.
example := (by fun_prop : HasProgramInO (fun xs : List Bool => xs.reverse.reverse.reverse)
  (fun v => List.Code.reverse v >>= List.Code.reverse >>= List.Code.reverse) _ _)

-- The machine-level proposition is an immediate consequence of the certificate.
example : ∃ b : Bounds (List Bool),
    Implements programTwice (fun xs : List Bool => xs.reverse.reverse) b :=
  let ⟨b, h, _⟩ := hasProgramInO_twice.sound; ⟨b, h⟩

-- One program for each runtime index does not provide one program for the whole input.
example (f : ℕ → Bool → Bool) (program : ℕ → Value → Code Value)
    (_h : ∀ n, HasProgramInO (f n) (program n) (fun _ => 1) (fun _ => 1)) : True := by
  fail_if_success
    have := (by fun_prop : HasProgramInO (fun x : ℕ × Bool => f x.1 x.2) _ _ _)
  trivial

def negateBool : Bool → Bool
  | true => false
  | false => true

theorem hasProgramIn_negateBool : HasProgramIn negateBool hole(⊢ program) IsO(fun _ => 1)
    IsO(fun x => max ⌜x⌝ₜ.size ⌜negateBool x⌝ₜ.size) := by
  abstract_hole program using programNegateBool
  fill_hole program in source_fun_prop

/-- info: 5 -/
#guard_msgs in
#eval (programNegateBool Value.input).build 1 |>.2.1

private def unequalBranches (x : Bool × List Bool) : List Bool :=
  if x.1 then x.2 else true :: x.2

-- Each case table entry is charged once; the unused branch is not added to the growth.
example : HasProgramInO unequalBranches hole(⊢ program) (fun _ => 1)
    (fun x => max ⌜x⌝ₜ.size ⌜unequalBranches x⌝ₜ.size) := by
  fill_hole program in source_fun_prop

private def selectConstant : Bool → ℕ
  | false => 2
  | true => 5

-- Closed values become constant trees of the case table.
example : HasProgramInO selectConstant hole(⊢ program) (fun _ => 1)
    (fun x => max ⌜x⌝ₜ.size ⌜selectConstant x⌝ₜ.size) := by
  fill_hole program in source_fun_prop

private def nonemptyTailReverse (x : {xs : List Bool // xs ≠ []}) : List Bool :=
  match h : x.1 with
  | [] => False.elim (x.2 h)
  | _ :: tail => tail.reverse

-- Impossible branches are replayed, and proof fields are erased from runtime environments.
example := (by source_fun_prop : HasProgramInO nonemptyTailReverse _ _ _)

def optionalReverse : Option (List Bool) → List Bool
  | none => []
  | some xs => xs.reverse

-- The growth is the produced one.
def hasProgramInO_optionalReverse := (by
  abstract_hole program using programOptionalReverse
  fill_hole program in source_fun_prop : HasProgramInO optionalReverse hole(⊢ program) _ _)

/-- info: 13 -/
#guard_msgs in
#eval (programOptionalReverse Value.input).build 1 |>.2.1

def singletonIndexed (x : Σ n, List (Fin n)) : Σ n, List (List (Fin n)) := ⟨x.1, [x.2]⟩

theorem hasProgramIn_singletonIndexed :
    HasProgramIn singletonIndexed hole(⊢ program) IsO(fun _ => 1)
    IsO(fun x => max ⌜x⌝ₜ.size ⌜singletonIndexed x⌝ₜ.size) := by
  abstract_hole program using programSingletonIndexed
  fill_hole program in source_fun_prop

/-- info: 2 -/
#guard_msgs in
#eval (programSingletonIndexed Value.input).build 1 |>.2.1

opaque legacy (xs : List Bool) : List Bool := xs

def mixedCalls (x : Bool × List Bool) : List Bool :=
  if x.1 then x.2.reverse else legacy x.2

-- An opaque call is supplied by one explicit implementation for every input.
example {program : Value → Code Value} {t p : List Bool → ℕ}
    (legacyImplementation : HasProgramInO legacy program t p) :=
  (by source_fun_prop : HasProgramInO mixedCalls _ _ _)

-- Only the selected branch is charged, at its own structural cost.
theorem hasProgramIn_conditionalReverse : HasProgramIn
    (fun x : Bool × List Bool => if x.1 then x.2.reverse else x.2) hole(⊢ program)
    IsO(fun x => (1 + if x.1 = true then 1 + ⌜x.2⌝ₜ.size else 1) + 1)
    IsO(fun x => max ⌜x⌝ₜ.size (max ⌜x⌝ₜ.size
      (if x.1 = true then max ⌜x⌝ₜ.size ⌜x.2⌝ₜ.size else ⌜x⌝ₜ.size))) := by
  abstract_hole program using programConditionalReverse
  fill_hole program in source_fun_prop

def reverseAlias (xs : List Bool) := xs.reverse

theorem hasProgramIn_reverseAlias : HasProgramIn reverseAlias List.Code.reverse
    IsO(fun xs => ⌜xs⌝ₜ.size) IsO(fun xs => ⌜xs⌝ₜ.size) := by
  refine HasProgramInO.toHasProgramIn ?_
  source_fun_prop

def aliasInLet (xs : List Bool) :=
  let ys := reverseAlias xs
  reverseAlias ys ++ xs

-- Only the translated definition is unfolded; a called alias needs its own implementation.
/-- error: source translation: `reverseAlias` needs a selected implementation -/
#guard_msgs (substring := true) in
example := (by source_fun_prop : HasProgramInO aliasInLet _ _ _)

section
attribute [local program] hasProgramIn_reverseAlias

example := (by source_fun_prop : HasProgramInO aliasInLet _ _ _)
end

-- Encoding proofs retain their source type even when both encodings reduce to `Tree.nil`.
example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop : HasProgramInO
  (fun x : Option (List α) => match x with | none => [] | some xs => xs.reverse) _ _ _)

end ComplexityTest.SourceTranslation.Certified
