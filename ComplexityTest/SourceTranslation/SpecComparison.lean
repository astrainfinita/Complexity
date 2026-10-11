/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Complexity.Tactic.TreeProgram.Library
import Std.WP
import Std.Tactic.Do

/-! # Comparing native WP specifications with source-function specifications -/

set_option experimental.vcgen true
open Complexity TreeProgram Complexity.TreeProgram.Source Std.WP Lean.Order

namespace ComplexityTest.SourceTranslation.SpecComparison

def duplicate {α : Type*} (xs : List α) := xs ++ xs

@[simps] def duplicateBounds {α : Type*} [UniqueEncoding Tree α] : Bounds (List α) :=
  ⟨fun xs => 26 * xs.length + 16, fun xs => 2 * (encode Tree xs).size⟩

theorem duplicate_realizes {α : Type*} [UniqueEncoding Tree α] :
    Realizes (duplicate : List α → List α) duplicateBounds := by
  change Realizes (fun xs => id xs ++ id xs) duplicateBounds
  simpa only [id_eq, appendBounds, identityBounds, duplicateBounds,
    Nat.zero_add, Nat.zero_max, two_mul] using identity_realizes.append identity_realizes

section SpecComparison

structure Source where
  fn : List Bool → List Bool

def source (f : List Bool → List Bool) : Source := ⟨f⟩

instance sourceWP : WP Source (Bounds (List Bool)) Prop Unit where
  wpTrans f := ⟨fun Q _ => ∃ b, Realizes f.fn b ∧ Q b⟩
  wp_trans_monotone _ := by
    intro Q R _ _ _ h ⟨b, hb, hQ⟩
    exact ⟨b, hb, h _ hQ⟩

@[spec] theorem spec_reverse (Q : Bounds (List Bool) → Prop) :
    Triple (source List.reverse) (Q reverseBounds) Q () :=
  ⟨fun h => ⟨_, reverse_realizes, h⟩⟩

@[spec] theorem spec_duplicate (Q : Bounds (List Bool) → Prop) :
    Triple (source duplicate) (Q duplicateBounds) Q () :=
  ⟨fun h => ⟨_, duplicate_realizes, h⟩⟩

@[spec 1100] theorem spec_duplicate_lambda (Q : Bounds (List Bool) → Prop) :
    Triple (source (fun xs : List Bool => xs ++ xs)) (Q duplicateBounds) Q () :=
  spec_duplicate Q

@[spec] theorem spec_comp (f g : List Bool → List Bool) (Q : Bounds (List Bool) → Prop) :
    Triple (source (g ∘ f))
      (wp (source f) (fun b => wp (source g) (fun c => Q (compBounds f b c)) ()) ()) Q () := by
  constructor
  rintro ⟨b, hf, c, hg, hQ⟩
  exact ⟨_, hf.comp hg, hQ⟩

def twiceExplicit : List Bool → List Bool := List.reverse ∘ List.reverse
def twiceLet (xs : List Bool) := let ys := xs.reverse; ys.reverse
def share (xs : List Bool) := let ys := xs.reverse; duplicate ys
def sharePlain (xs : List Bool) := let ys := xs.reverse; ys ++ ys
def unshared (xs : List Bool) := xs.reverse ++ xs.reverse
def helper (xs : List Bool) := xs.reverse
def throughHelper (xs : List Bool) := (helper xs).reverse

example : Triple (source List.reverse) True
    (fun b => ∀ xs, b.time xs ≤ 13 * xs.length + 8) () := by
  vcgen
  simp [reverseBounds]

example : Triple (source twiceExplicit) True
    (fun b => ∀ xs, b.time xs ≤ 26 * xs.length + 16) () := by
  unfold twiceExplicit
  vcgen
  simp [compBounds, reverseBounds]
  omega

example : Triple (source (fun xs : List Bool => xs ++ xs)) True
    (fun b => ∀ xs, b.time xs ≤ 26 * xs.length + 16) () := by
  vcgen
  simp [duplicateBounds]

def retainsInput (xs : List Bool) := let ys := xs.reverse; ys ++ xs
def branch (xs : List Bool) := if xs.isEmpty then xs else xs.reverse
def recursive : List Bool → List Bool
  | [] => []
  | x :: xs => recursive xs ++ [x]

section BareLambda

local instance : WP (List Bool → List Bool) (Bounds (List Bool)) Prop Unit where
  wpTrans f := sourceWP.wpTrans (source f)
  wp_trans_monotone f := sourceWP.wp_trans_monotone (source f)

@[local spec] theorem bare_lambda_spec (Q : Bounds (List Bool) → Prop) :
    Triple (fun xs : List Bool => xs.reverse.reverse)
      (Q (compBounds List.reverse reverseBounds reverseBounds)) Q () :=
  ⟨fun h => ⟨_, reverse_realizes.comp reverse_realizes, h⟩⟩

/-- error: No spec found for program fun xs => xs.reverse.reverse. -/
#guard_msgs in
example : Triple (fun xs : List Bool => xs.reverse.reverse) True
    (fun b => ∀ xs, b.time xs ≤ 26 * xs.length + 16) () := by
  vcgen

end BareLambda
end SpecComparison

end ComplexityTest.SourceTranslation.SpecComparison
