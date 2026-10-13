/- Cross-module reuse of the program and allowance saved by structural recursion. -/
import ComplexityTest.SourceTranslation.Recursion

open Complexity ComplexityTest.SourceTranslation.Recursion

example : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace
    (fun xs : List Bool => (drain xs, xs))
    (fun n => 210 * n + 210) (fun n => k * (30 * (n + 1)^2)) := by
  model_fun_prop
  all_goals
    rename_i xs
    simp only [show ∀ x : Unit, x = () from fun x => Subsingleton.elim _ _,
      size_encode_unit]
    have := Nat.le_self_pow (by decide : 2 ≠ 0) (⌜xs⌝ₜ.size + 1)
    omega
