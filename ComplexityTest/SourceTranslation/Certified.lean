/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Complexity.Tactic.TreeProgram.Translation

open Complexity TreeProgram Complexity.TreeProgram.Source

namespace ComplexityTest.SourceTranslation.Certified

attribute [local fun_prop] HasProgram.identity HasProgram.comp
  List.hasProgram_reverse HasProgram.map HasProgram.ite Prod.hasProgram_fst
  Prod.hasProgram_snd
  HasProgram.pair List.hasProgram_append

theorem hasProgram_reverse : HasProgram (List.reverse : List Bool → List Bool) hole(⊢ program)
    (fun xs => ⌜xs⌝ₜ.size) (fun xs => ⌜xs⌝ₜ.size) := by
  abstract_hole program using programReverse
  fill_hole program in fun_prop

-- Ordinary `fun_prop` produces the structural growth of each call.
def hasProgram_twice := (by
  abstract_hole program using programTwice
  fill_hole program in fun_prop :
    HasProgram (fun xs : List Bool => xs.reverse.reverse) hole(⊢ program) _ _)

example : HasProgram (fun xs : List Bool => xs.reverse.reverse) programTwice
    (fun xs => ⌜xs⌝ₜ.size + ⌜xs.reverse⌝ₜ.size) (fun xs => max ⌜xs⌝ₜ.size ⌜xs.reverse⌝ₜ.size) :=
  hasProgram_twice

example := (by fun_prop :
  HasProgram (List.map (List.reverse : List Bool → List Bool)) (List.Code.map List.Code.reverse) _ _)

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

example (hf : HasProgram f pf t p) (hg : HasProgram g pg u q) :
    HasProgram (fun x => g (f x)) (fun v => pf v >>= pg) (fun x => t x + u (f x))
      (fun x => max (p x) (q (f x))) := by
  fun_prop

example (hf : HasProgram f pf t p) := (by fun_prop : HasProgram (List.map f) (List.Code.map pf) _ _)

end

-- Repeated calls exercise reuse of a result in the search cache.
example := (by fun_prop : HasProgram (fun xs : List Bool => xs.reverse.reverse.reverse)
  (fun v => List.Code.reverse v >>= List.Code.reverse >>= List.Code.reverse) _ _)

-- The machine-level proposition is an immediate consequence of the certificate.
example : ∃ b : Bounds (List Bool),
    Implements programTwice (fun xs : List Bool => xs.reverse.reverse) b :=
  let ⟨b, h, _⟩ := hasProgram_twice.sound; ⟨b, h⟩

-- One program for each runtime index does not provide one program for the whole input.
example (f : ℕ → Bool → Bool) (program : ℕ → Value → Code Value)
    (_h : ∀ n, HasProgram (f n) (program n) (fun _ => 1) (fun _ => 1)) : True := by
  fail_if_success
    have := (by fun_prop : HasProgram (fun x : ℕ × Bool => f x.1 x.2) _ _ _)
  trivial

def negateBool : Bool → Bool
  | true => false
  | false => true

theorem hasProgram_negateBool : HasProgram negateBool hole(⊢ program) (fun _ => 1)
    (fun x => max ⌜x⌝ₜ.size ⌜negateBool x⌝ₜ.size) := by
  abstract_hole program using programNegateBool
  fill_hole program in source_fun_prop

/-- info: 5 -/
#guard_msgs in
#eval (programNegateBool Value.input).build 1 |>.2.1

private def unequalBranches (x : Bool × List Bool) : List Bool :=
  if x.1 then x.2 else true :: x.2

-- Each case table entry is charged once; the unused branch is not added to the growth.
example : HasProgram unequalBranches hole(⊢ program) (fun _ => 1)
    (fun x => max ⌜x⌝ₜ.size ⌜unequalBranches x⌝ₜ.size) := by
  fill_hole program in source_fun_prop

private def selectConstant : Bool → ℕ
  | false => 2
  | true => 5

-- Closed values become constant trees of the case table.
example : HasProgram selectConstant hole(⊢ program) (fun _ => 1)
    (fun x => max ⌜x⌝ₜ.size ⌜selectConstant x⌝ₜ.size) := by
  fill_hole program in source_fun_prop

private def nonemptyTailReverse (x : {xs : List Bool // xs ≠ []}) : List Bool :=
  match h : x.1 with
  | [] => False.elim (x.2 h)
  | _ :: tail => tail.reverse

-- Impossible branches are replayed, and proof fields are erased from runtime environments.
example := (by source_fun_prop : HasProgram nonemptyTailReverse _ _ _)

def optionalReverse : Option (List Bool) → List Bool
  | none => []
  | some xs => xs.reverse

-- The growth is the produced one.
def hasProgram_optionalReverse := (by
  abstract_hole program using programOptionalReverse
  fill_hole program in source_fun_prop : HasProgram optionalReverse hole(⊢ program) _ _)

/-- info: 13 -/
#guard_msgs in
#eval (programOptionalReverse Value.input).build 1 |>.2.1

def singletonIndexed (x : Σ n, List (Fin n)) : Σ n, List (List (Fin n)) := ⟨x.1, [x.2]⟩

theorem hasProgram_singletonIndexed : HasProgram singletonIndexed hole(⊢ program) (fun _ => 1)
    (fun x => max ⌜x⌝ₜ.size ⌜singletonIndexed x⌝ₜ.size) := by
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
    (legacyImplementation : HasProgram legacy program t p) :=
  (by source_fun_prop : HasProgram mixedCalls _ _ _)

-- Only the selected branch is charged, at its own structural cost.
theorem hasProgram_conditionalReverse : HasProgram
    (fun x : Bool × List Bool => if x.1 then x.2.reverse else x.2) hole(⊢ program)
    (fun x => (1 + if x.1 = true then 1 + ⌜x.2⌝ₜ.size else 1) + 1)
    (fun x => max ⌜x⌝ₜ.size (max ⌜x⌝ₜ.size
      (if x.1 = true then max ⌜x⌝ₜ.size ⌜x.2⌝ₜ.size else ⌜x⌝ₜ.size))) := by
  abstract_hole program using programConditionalReverse
  fill_hole program in source_fun_prop

def reverseAlias (xs : List Bool) := xs.reverse

theorem hasProgram_reverseAlias : HasProgram reverseAlias List.Code.reverse
    (fun xs => ⌜xs⌝ₜ.size) (fun xs => ⌜xs⌝ₜ.size) := by
  source_fun_prop

def aliasInLet (xs : List Bool) :=
  let ys := reverseAlias xs
  reverseAlias ys ++ xs

-- Only the translated definition is unfolded; a called alias needs its own implementation.
/-- error: source translation: `reverseAlias` needs a selected implementation -/
#guard_msgs (substring := true) in
example := (by source_fun_prop : HasProgram aliasInLet _ _ _)

section
attribute [local source] hasProgram_reverseAlias

example := (by source_fun_prop : HasProgram aliasInLet _ _ _)
end

-- Encoding proofs retain their source type even when both encodings reduce to `Tree.nil`.
example {α : Type*} [UniqueEncoding Tree α] := (by source_fun_prop : HasProgram
  (fun x : Option (List α) => match x with | none => [] | some xs => xs.reverse) _ _ _)

end ComplexityTest.SourceTranslation.Certified
