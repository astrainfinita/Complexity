/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Complexity.Tactic.TreeProgram.Primitives
import Std.WP
import Std.Tactic.Do

/-! # Comparing native WP specifications with source-function specifications -/

set_option experimental.vcgen true
open Complexity TreeProgram Complexity.TreeProgram.Source
open Complexity.TreeProgram.Source.Internal (HasProgram)
open Std.WP Lean.Order

namespace ComplexityTest.SourceTranslation.SpecComparison

def duplicate {α : Type*} (xs : List α) := xs ++ xs

theorem hasProgramIn_duplicate {α : Type*} [UniqueEncoding Tree α] :
    HasProgramIn (duplicate : List α → List α) hole(⊢ program) IsO(fun xs => xs.length + 1)
      IsO(fun xs => ⌜xs⌝ₜ.size + ⌜xs⌝ₜ.size) := by
  abstract_hole program using programDuplicate
  refine HasProgram.toHasProgramIn ?_
  fill_hole program in
    refine ((HasProgram.identity.pair HasProgram.identity).comp
      List.hasProgramIn_append.toHasProgram).mono
      ?_ ?_ <;> dominated

section SpecComparison

structure Source where
  fn : List Bool → List Bool

def source (f : List Bool → List Bool) : Source := ⟨f⟩

/-- Time and peak growth of a source function. -/
abbrev Growth := (List Bool → ℕ) × (List Bool → ℕ)

instance sourceWP : WP Source Growth Prop Unit where
  wpTrans f := ⟨fun Q _ => ∃ b : Growth, (∃ program, HasProgram f.fn program b.1 b.2) ∧ Q b⟩
  wp_trans_monotone _ := by
    intro Q R _ _ _ h ⟨b, hf, hQ⟩
    exact ⟨b, hf, h _ hQ⟩

@[spec] theorem spec_reverse (Q : Growth → Prop) :
    Triple (source List.reverse) (Q (fun xs => ⌜xs⌝ₜ.size, fun xs => ⌜xs⌝ₜ.size)) Q () :=
  ⟨fun h => ⟨(_, _), ⟨_, List.hasProgramIn_reverse.toHasProgram⟩, h⟩⟩

@[spec] theorem spec_duplicate (Q : Growth → Prop) :
    Triple (source duplicate) (Q (fun xs => xs.length + 1, fun xs => ⌜xs⌝ₜ.size + ⌜xs⌝ₜ.size))
      Q () :=
  ⟨fun h => ⟨(_, _), ⟨_, hasProgramIn_duplicate.toHasProgram⟩, h⟩⟩

@[spec 1100] theorem spec_duplicate_lambda (Q : Growth → Prop) :
    Triple (source (fun xs : List Bool => xs ++ xs))
      (Q (fun xs => xs.length + 1, fun xs => ⌜xs⌝ₜ.size + ⌜xs⌝ₜ.size)) Q () :=
  spec_duplicate Q

@[spec] theorem spec_comp (f g : List Bool → List Bool) (Q : Growth → Prop) :
    Triple (source (g ∘ f))
      (wp (source f) (fun b => wp (source g) (fun c =>
        Q (fun x => b.1 x + c.1 (f x), fun x => max (b.2 x) (c.2 (f x)))) ()) ()) Q () := by
  constructor
  change (∃ b : Growth, (∃ program, HasProgram f program b.1 b.2) ∧
    ∃ c : Growth, (∃ program, HasProgram g program c.1 c.2) ∧
      Q (fun x => b.1 x + c.1 (f x), fun x => max (b.2 x) (c.2 (f x)))) →
      ∃ d : Growth, (∃ program, HasProgram (g ∘ f) program d.1 d.2) ∧ Q d
  rintro ⟨b, ⟨_, hf⟩, c, ⟨_, hg⟩, hQ⟩
  exact ⟨(_, _), ⟨_, hf.comp hg⟩, hQ⟩

def twiceExplicit : List Bool → List Bool := List.reverse ∘ List.reverse
def twiceLet (xs : List Bool) := let ys := xs.reverse; ys.reverse
def share (xs : List Bool) := let ys := xs.reverse; duplicate ys
def sharePlain (xs : List Bool) := let ys := xs.reverse; ys ++ ys
def unshared (xs : List Bool) := xs.reverse ++ xs.reverse
def helper (xs : List Bool) := xs.reverse
def throughHelper (xs : List Bool) := (helper xs).reverse

example : Triple (source List.reverse) True
    (fun b => Dominated b.1 (fun xs => ⌜xs⌝ₜ.size)) () := by
  vcgen
  exact Dominated.refl _

example : Triple (source twiceExplicit) True
    (fun b => Dominated b.1 (fun xs => ⌜xs⌝ₜ.size)) () := by
  unfold twiceExplicit
  vcgen
  simpa only [size_encode_reverse] using (Dominated.refl _).add_same (Dominated.refl _)

example : Triple (source (fun xs : List Bool => xs ++ xs)) True
    (fun b => Dominated b.1 (fun xs => ⌜xs⌝ₜ.size)) () := by
  vcgen
  exact Dominated.of_le fun xs =>
    show xs.length + 1 ≤ ⌜xs⌝ₜ.size by have := size_encode_list xs; omega

def retainsInput (xs : List Bool) := let ys := xs.reverse; ys ++ xs
def branch (xs : List Bool) := if xs.isEmpty then xs else xs.reverse
def recursive : List Bool → List Bool
  | [] => []
  | x :: xs => recursive xs ++ [x]

section BareLambda

local instance : WP (List Bool → List Bool) Growth Prop Unit where
  wpTrans f := sourceWP.wpTrans (source f)
  wp_trans_monotone f := sourceWP.wp_trans_monotone (source f)

@[local spec] theorem bare_lambda_spec (Q : Growth → Prop) :
    Triple (fun xs : List Bool => xs.reverse.reverse)
      (Q (fun xs => ⌜xs⌝ₜ.size + ⌜xs.reverse⌝ₜ.size,
        fun xs => max ⌜xs⌝ₜ.size ⌜xs.reverse⌝ₜ.size)) Q () :=
  ⟨fun h => ⟨(_, _),
    ⟨_, List.hasProgramIn_reverse.toHasProgram.comp List.hasProgramIn_reverse.toHasProgram⟩, h⟩⟩

/-- error: No spec found for program fun xs => xs.reverse.reverse. -/
#guard_msgs in
example : Triple (fun xs : List Bool => xs.reverse.reverse) True
    (fun b => Dominated b.1 (fun xs => ⌜xs⌝ₜ.size)) () := by
  vcgen

end BareLambda
end SpecComparison

end ComplexityTest.SourceTranslation.SpecComparison
