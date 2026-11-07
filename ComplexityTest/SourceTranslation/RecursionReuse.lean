/- Cross-module reuse of the program and growth specification saved by structural recursion. -/
import ComplexityTest.SourceTranslation.Recursion

open Complexity TreeProgram.Source
open TreeProgram.Source.Internal (HasProgram)
open ComplexityTest.SourceTranslation.Recursion

example := (by source_fun_prop : HasProgram drain programDrain _ _)

example : HasProgram drain hole(⊢ program) (fun xs => ⌜xs⌝ₜ.size) (fun xs => ⌜xs⌝ₜ.size ^ 2) := by
  fill_hole program in source_fun_prop

example : (fun xs : List Bool => (drain xs, xs)) ∈
    FDTISP .tree (fun n => n ^ 1) (fun n => n ^ 2) := by
  model_fun_prop
