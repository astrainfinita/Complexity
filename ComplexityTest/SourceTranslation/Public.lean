/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Complexity.Tactic.TreeProgram.Library

open Complexity

namespace ComplexityTest.SourceTranslation.Public

-- No internal namespace, implementation object or rule-registration list is needed.
def twice (xs : List Bool) := xs.reverse.reverse

example : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace twice
    (fun n => 26 * n + 20) (fun n => k * (n + 3)) := by
  model_fun_prop

example : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace
    (fun x : Option (List Bool) => match x with | none => [] | some xs => xs.reverse)
    (fun n => 13 * n + 20) (fun n => k * (n + 3)) := by
  model_fun_prop

-- Callback budgets add per element, even when one list is long and the others are empty.
def reverseLast (x : List Unit × List (List Unit)) : List Unit :=
  x.2.foldl (fun _ ys => ys.reverse) x.1

example : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace reverseLast
    (fun n => 22 * n + 14) (fun n => k * (n + 2)) := by
  model_fun_prop
  · rename_i x
    rcases x with ⟨a, xs⟩
    have h := List.sum_le_sum (l := xs)
      (fun ys _ => TreeProgram.Source.length_le_codeSize ys)
    rw [List.sum_map_mul_left, size_encode_prod, size_encode_list xs]
    dsimp only at h ⊢
    omega
  · rename_i x
    rcases x with ⟨a, xs⟩
    refine (TreeProgram.Source.foldlCost_peak_le _ _ ?_ ?_).trans ?_
    · intros; simp
    · intros; simp
    · simp only [size_encode_prod]; omega

end ComplexityTest.SourceTranslation.Public
