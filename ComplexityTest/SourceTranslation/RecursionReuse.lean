/- Cross-module reuse of the program and growth specification saved by structural recursion. -/
import ComplexityTest.SourceTranslation.Recursion

open Complexity TreeProgram.Source ComplexityTest.SourceTranslation.Recursion

noncomputable def recalledDrain : Implementation drain := by source_fun_prop

example : recalledDrain.program = drainImplementation.program := by
  simpa only [recalledDrain] using drain_model.program_sourceImplementation
example : recalledDrain.HasGrowth (fun xs => ⌜xs⌝ₜ.size) (fun xs => ⌜xs⌝ₜ.size ^ 2) :=
  drain_model.hasGrowth_sourceImplementation

example : (fun xs : List Bool => (drain xs, xs)) ∈
    FTISP .tree (fun n => n ^ 1) (fun n => n ^ 2) := by
  model_fun_prop
  all_goals
    simp only [pow_one, Dominated.add_iff, Dominated.max_iff,
      show ∀ x : Unit, x = () from fun x => Subsingleton.elim _ _, size_encode_prod, size_encode_unit]
    repeat' apply And.intro
  all_goals first
    | exact Dominated.refl _
    | exact (Dominated.refl _).le_pow (by decide)
    | exact Dominated.const_of_pos _ (fun _ => Tree.size_pos _)
    | exact Dominated.const_of_pos _ (fun _ => Nat.pow_pos (Tree.size_pos _))
