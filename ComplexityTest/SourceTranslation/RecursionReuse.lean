/- Cross-module reuse of the program and growth specification saved by structural recursion. -/
import ComplexityTest.SourceTranslation.Recursion

open Complexity TreeProgram.Source ComplexityTest.SourceTranslation.Recursion

example : (by source_fun_prop : Implementation drain _ _).program =
    implementationDrain.program := rfl

example : Implementation drain (fun xs => ⌜xs⌝ₜ.size) (fun xs => ⌜xs⌝ₜ.size ^ 2) := by
  source_fun_prop

example : (fun xs : List Bool => (drain xs, xs)) ∈
    FTISP .tree (fun n => n ^ 1) (fun n => n ^ 2) := by
  model_fun_prop
  all_goals dominated
