import Complexity.Tactic.TreeProgram.Library

open Complexity TreeProgram Complexity.TreeProgram.Source

namespace ComplexityTest.SourceTranslation.LengthKernel

-- Exercise the current translator, including length, composition, and pairing.
theorem certificate :
    Nonempty (Implementation (fun x : List Unit × Bool => (x.1.length, x.2))
      (fun x => ⌜x.1⌝ₜ.size ^ 2 + 1) (fun x => ⌜x⌝ₜ.size + ⌜(x.1.length, x.2)⌝ₜ.size)) := by
  refine ⟨?_⟩
  source_fun_prop
  all_goals
    simp only [Dominated.add_iff, Dominated.max_iff]
    repeat' apply And.intro
    all_goals first
      | exact Dominated.const_of_pos _ (fun _ => Nat.zero_lt_succ _)
      | apply Dominated.of_le
        intro x
        have := size_encode_fst_le x
        omega

-- Recheck the generated proof with a kernel-only allocation limit, independent of tactic cost
-- and machine speed. The benchmark records current raw heartbeats separately.
-- A historical version omitting structural equality proofs exceeded 26000 heartbeats.
-- The growth is carried by the type, so no budget projection is replayed here.
open Lean Elab in
run_elab do
  let .thmInfo info ← getConstInfo ``certificate | throwError "expected length certificate"
  let opts := maxHeartbeats.set (← getOptions) 100
  let checked := (← getEnv).toKernelEnv.addDecl opts
    (.thmDecl { info with name := info.name.appendAfter "_recheck" })
  match checked with
  | .error ex => throwError "length budget kernel regression: {ex.toMessageData opts}"
  | .ok _ => pure ()

end ComplexityTest.SourceTranslation.LengthKernel
