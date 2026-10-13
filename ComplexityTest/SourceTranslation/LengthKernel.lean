import Complexity.Tactic.TreeProgram.Library

open Complexity TreeProgram Complexity.TreeProgram.Source

namespace ComplexityTest.SourceTranslation.LengthKernel

-- Exercise the current translator, including length, composition, and pair budget normalization.
theorem certificate :
    ∃ b, Realizes (fun x : List Unit × Bool => (x.1.length, x.2)) b := ⟨_, by source_fun_prop⟩

-- Recheck the generated proof with a kernel-only allocation limit, independent of tactic cost
-- and machine speed. On Lean 4.35.0-rc2 this needs about 8 heartbeats (1000 raw allocations each).
-- Omitting budget equality proofs in normalizeSourceBounds needs over 26000 and fails this limit.
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
