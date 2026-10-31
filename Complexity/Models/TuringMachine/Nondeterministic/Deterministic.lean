/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TuringMachine.Nondeterministic.Basic
public import Complexity.Models.TuringMachine.Deterministic
public import Complexity.Control.Controller.Binary

/-!
# Deterministic machines as nondeterministic machines

Duplicating a deterministic transition preserves its configurations and visit intervals.
Consequently the deterministic and nondeterministic time, termination, and space conventions
agree exactly. Coincident branches retain their multiplicities.
-/

@[expose] public section

namespace Complexity.TM

variable {κ : Type*} {Γ Q : Type*} [Inhabited Γ]
variable (M : TM Id κ Γ Q)

@[simp] theorem usesTime_toBinary_iff (xs : List Γ) (t : ℕ) :
    NTM.UsesTime M.toBinary xs t ↔ M.Halted (M.run xs t) := by
  simp only [NTM.UsesTime, Controller.mem_runWith_toBinary_iff, forall_eq,
    Controller.halted_toBinary_iff]

@[simp] theorem terminates_toBinary_iff (xs : List Γ) :
    NTM.Terminates M.toBinary xs ↔ M.Terminates xs := by
  simp only [NTM.Terminates, usesTime_toBinary_iff, Terminates]

@[simp] theorem usesSpace_toBinary_iff [Fintype κ] (xs : List Γ) (s : ℕ) :
    NTM.UsesSpace M.toBinary xs s ↔ M.UsesSpace xs s := by
  simp only [NTM.UsesSpace, UsesSpace, Controller.mem_runHistoryWith_toBinary_iff, forall_eq]

end Complexity.TM
