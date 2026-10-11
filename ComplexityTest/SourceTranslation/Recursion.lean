/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Complexity.Tactic.TreeProgram.Library

open Complexity

namespace ComplexityTest.SourceTranslation.Recursion

open Lean Meta Elab Tactic in
elab (name := guardPublicGoals) "guard_public_goals" : tactic => do
  for goal in ← getGoals do
    goal.withContext do
      let type ← instantiateMVars (← goal.getType)
      let displayed := (← ppExpr type).pretty
      if (displayed.splitOn "TreeProgram.Source").length > 1 then
        throwError "recursion exposed an internal certificate or budget in a user goal"

#allow_unused_tactic! guardPublicGoals

def invert : List Bool → List Bool
  | [] => []
  | x :: xs => (!x) :: invert xs

def invertResume (x : {xs : List Bool // (!xs.isEmpty) = true}) (result : List Bool) :=
  match h : x.val with
  | [] => False.elim (by simpa [h] using x.property)
  | a :: _ => (!a) :: result

theorem size_invert (xs : List Bool) : ⌜invert xs⌝ₜ.size ≤ 2 * ⌜xs⌝ₜ.size := by
  induction xs with
  | nil => simp [invert]
  | cons a xs ih => cases a <;> simp [invert] at * <;> omega

theorem invert_model : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace invert
    (fun n => 1000 * n + 1000) (fun n => k * (1000 * (n + 1)^2)) := by
  model_fun_prop using recursion
    (test := fun xs : List Bool => !xs.isEmpty)
    (next := List.tail)
    (finish := fun _ => [])
    (resume := invertResume)
    (time := fun xs => 100 * xs.length + 100)
    (space := fun xs => 100 * (⌜xs⌝ₜ.size + 1)^2)
  guard_public_goals
  case finish_eq => rfl
  case resume_eq =>
    intro xs h
    cases xs with
    | nil => exact (h rfl).elim
    | cons a xs => rfl
  case input_size => nlinarith
  case check_space =>
    rename_i xs
    have hp : 0 < (⌜xs⌝ₜ.size + 1)^2 := by positivity
    split_ifs <;> (repeat' apply And.intro) <;> nlinarith
  case step_bounds.cons =>
    rename_i a xs h
    have hs := size_invert xs
    cases a <;> simp_all <;> (repeat' apply And.intro) <;> nlinarith

def endPosition (xs : List Bool) : Fin (xs.length + 1) := Fin.last xs.length

def positionResume : (x : {xs : List Bool // (!xs.isEmpty) = true}) →
    Fin (x.val.tail.length + 1) → Fin (x.val.length + 1)
  | ⟨[], h⟩, _ => False.elim (by simp at h)
  | ⟨_ :: _, _⟩, result => result.succ

-- The dependent result uses the existing public encoding view at the model boundary.
-- Its callbacks still return ordinary Fin values; their encoding is automatic.
theorem endPosition_model : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace
    (fun xs => ⌜endPosition xs⌝ₜ)
    (fun n => 100000 * (n + 1)^2) (fun n => k * (100000 * (n + 1)^2)) := by
  model_fun_prop using recursion
    (test := fun xs : List Bool => !xs.isEmpty)
    (next := List.tail)
    (finish := fun _ => 0)
    (resume := positionResume)
    (time := fun xs => 10000 * (xs.length + 1)^2)
    (space := fun xs => 10000 * (⌜xs⌝ₜ.size + 1)^2)
  guard_public_goals
  case finish_eq => rintro a rfl; rfl
  case resume_eq =>
    intro xs h
    cases xs with
    | nil => exact (h rfl).elim
    | cons a xs => rfl
  case input_size => nlinarith
  case check_space =>
    rename_i xs
    have hp : 0 < (⌜xs⌝ₜ.size + 1)^2 := by positivity
    split_ifs <;> (repeat' apply And.intro) <;> nlinarith
  case step_bounds.cons =>
    rename_i a xs h
    have hn := size_encode_nat_le xs.length
    have hb : xs.length.bits.length ≤ ⌜xs.length⌝ₜ.size := by
      simp only [encode_nat_tree, size_encode_list]; omega
    have hl : xs.length ≤ ⌜xs⌝ₜ.size := by simp only [size_encode_list]; omega
    cases a <;> simp_all [endPosition] <;> (repeat' apply And.intro) <;> nlinarith
  case hb.left =>
    rename_i xs
    have hl : xs.length ≤ ⌜xs⌝ₜ.size := by simp only [size_encode_list]; omega
    nlinarith

-- An impossible credit cannot silently select the already supported identity implementation.
example : True := by
  fail_if_success
    have : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace (id : List Bool → List Bool)
        (fun _ => 4) (fun n => k * (n + 3)) := by
      model_fun_prop using recursion
        (test := fun _ => false)
        (next := id)
        (finish := fun x => x.val)
        (resume := fun x _ => x.val)
        (time := fun _ => 0)
        (space := fun _ => 0)
  trivial

-- An uncertified selected callback fails immediately and restores the original model goal.
example : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace (id : List Bool → List Bool)
    (fun _ => 4) (fun n => k * (n + 3)) := by
  fail_if_success
    model_fun_prop using recursion
      (test := fun xs => !xs.isEmpty)
      (next := invert)
      (finish := fun x => x.val)
      (resume := fun x _ => x.val)
      (time := fun _ => 100)
      (space := fun _ => 100)
  model_fun_prop

end ComplexityTest.SourceTranslation.Recursion
