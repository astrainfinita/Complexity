/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TuringMachine.Program.Basic
public import Complexity.Control.Program.Enumeration

/-! # Finite enumerations for calling compiled Turing programs

The compiler itself does not import this layer. Read operations retain their external
alphabet enumeration; observation snapshots use coordinate numbering.
-/

@[expose] public section

namespace Complexity.TM.Program.Op

/-- Number observation snapshots without listing all possible snapshots. -/
@[instance_reducible] def enumResult {κ : Type} {Γ : Type} :
    (o : Op κ Γ) → FinEnum o.Result
  | .act _ => inferInstanceAs (FinEnum Unit)
  | .readInput s | .read s _ =>
    letI := s
    inferInstanceAs (FinEnum Γ)
  | .observeBits n _ => inferInstanceAs (FinEnum (Vector Bool n))

attribute [instance] enumResult

end Complexity.TM.Program.Op
