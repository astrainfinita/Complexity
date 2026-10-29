import Complexity.Tactic.TreeProgram.Library

open Complexity TreeProgram Complexity.TreeProgram.Source

namespace ComplexityTest.SourceTranslation.LengthKernel

-- Exercise the current translator, including length, composition, and pairing.
theorem certificate :
    HasProgram (fun x : List Unit × Bool => (x.1.length, x.2)) hole(⊢ program)
      (fun x => ⌜x.1⌝ₜ.size ^ 2 + 1) (fun x => ⌜x⌝ₜ.size + ⌜(x.1.length, x.2)⌝ₜ.size) := by
  fill_hole program in source_fun_prop

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
