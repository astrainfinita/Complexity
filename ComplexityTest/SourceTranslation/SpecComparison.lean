/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Complexity.Tactic.TreeProgram.Translation
import Std.WP
import Std.Tactic.Do

/-! # Comparing native WP specifications with source-function specifications -/

set_option experimental.vcgen true
open Complexity TreeProgram Complexity.TreeProgram.Source Std.WP Lean.Order

namespace ComplexityTest.SourceTranslation.SpecComparison

def duplicate {α : Type*} (xs : List α) := xs ++ xs

@[simps] def duplicateBounds {α : Type*} [UniqueEncoding Tree α] : Bounds (List α) :=
  ⟨fun xs => 26 * xs.length + 16, fun xs => 2 * (encode Tree xs).size⟩

def duplicateImplementation {α : Type*} [UniqueEncoding Tree α] :
    Implementation (duplicate : List α → List α) :=
  Implementation.identity.append Implementation.identity

@[simp] theorem bounds_duplicateImplementation {α : Type*} [UniqueEncoding Tree α] :
    (duplicateImplementation (α := α)).bounds = duplicateBounds := by
  change appendBounds (id : List α → List α) id identityBounds identityBounds = duplicateBounds
  simp [appendBounds, identityBounds, duplicateBounds, two_mul]

section SpecComparison

structure Source where
  fn : List Bool → List Bool

def source (f : List Bool → List Bool) : Source := ⟨f⟩

instance sourceWP : WP Source (Bounds (List Bool)) Prop Unit where
  wpTrans f := ⟨fun Q _ => ∃ impl : Implementation f.fn, Q impl.bounds⟩
  wp_trans_monotone _ := by
    intro Q R _ _ _ h ⟨impl, hQ⟩
    exact ⟨impl, h _ hQ⟩

@[spec] theorem spec_reverse (Q : Bounds (List Bool) → Prop) :
    Triple (source List.reverse) (Q reverseBounds) Q () :=
  ⟨fun h => ⟨Implementation.reverse, h⟩⟩

@[spec] theorem spec_duplicate (Q : Bounds (List Bool) → Prop) :
    Triple (source duplicate) (Q duplicateBounds) Q () :=
  ⟨fun h => ⟨duplicateImplementation, by
    change Q (duplicateImplementation (α := Bool)).bounds
    rw [bounds_duplicateImplementation]
    exact h⟩⟩

@[spec 1100] theorem spec_duplicate_lambda (Q : Bounds (List Bool) → Prop) :
    Triple (source (fun xs : List Bool => xs ++ xs)) (Q duplicateBounds) Q () :=
  spec_duplicate Q

@[spec] theorem spec_comp (f g : List Bool → List Bool) (Q : Bounds (List Bool) → Prop) :
    Triple (source (g ∘ f))
      (wp (source f) (fun b => wp (source g) (fun c => Q (compBounds f b c)) ()) ()) Q () := by
  constructor
  change (∃ hf : Implementation f, ∃ hg : Implementation g,
    Q (compBounds f hf.bounds hg.bounds)) →
      ∃ impl : Implementation (g ∘ f), Q impl.bounds
  rintro ⟨hf, hg, hQ⟩
  exact ⟨hf.comp hg, by rw [Implementation.bounds_comp]; exact hQ⟩

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
  ⟨fun h => ⟨Implementation.reverse.comp Implementation.reverse, h⟩⟩

/-- error: No spec found for program fun xs => xs.reverse.reverse. -/
#guard_msgs in
example : Triple (fun xs : List Bool => xs.reverse.reverse) True
    (fun b => ∀ xs, b.time xs ≤ 26 * xs.length + 16) () := by
  vcgen

end BareLambda
end SpecComparison

end ComplexityTest.SourceTranslation.SpecComparison
