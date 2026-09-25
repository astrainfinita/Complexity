/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TuringMachine.Nondeterministic
public import Complexity.Models.TuringMachine.Deterministic
public import Complexity.Control.Transition.Trace
public import Complexity.Control.Controller.Binary

/-!
# Deterministic machines as nondeterministic machines

Duplicating a deterministic transition preserves its configurations and execution traces.
Consequently the deterministic and nondeterministic time, termination, and space conventions
agree exactly. Coincident branches retain their multiplicities.
-/

@[expose] public section

namespace Complexity.TM

variable {κ : Type*} {Γ Q : Type*} [Inhabited Γ] {xs : Array Γ}
variable (M : TM Id κ Γ Q)

@[simp] theorem usesTime_toBinary_iff (xs : List Γ) (t : ℕ) :
    NTM.UsesTime M.toBinary xs t ↔ M.Halted (M.run (Config := Cfg κ Γ Q xs.toArray) xs t) := by
  simp only [NTM.UsesTime, Controller.mem_runWith_toBinary_iff,
    forall_eq, Controller.halted_toBinary_iff]

@[simp] theorem terminates_toBinary_iff (xs : List Γ) :
    NTM.Terminates M.toBinary xs ↔ M.Terminates xs := by
  simp only [NTM.Terminates, usesTime_toBinary_iff, Terminates]

/-- Trace-based and time-indexed descriptions visit exactly the same positions. -/
theorem visitedOfTrace_runTrace (c : Cfg κ Γ Q xs) (n : ℕ) (i : κ) :
    visitedOfTrace (M.runTrace c n) i = M.visited c n i := by
  ext j
  simp only [visitedOfTrace, List.mem_toFinset, List.mem_map,
    visited, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨d, hd, hj⟩
    obtain ⟨t, ht, rfl⟩ := (Transition.mem_runTrace_id_iff M.step n c d).1 hd
    exact ⟨t, Nat.lt_succ_of_le ht, hj⟩
  · rintro ⟨t, ht, hj⟩
    refine ⟨M.runFrom c t, ?_, hj⟩
    exact (Transition.mem_runTrace_id_iff M.step n c (M.runFrom c t)).2
      ⟨t, Nat.le_of_lt_succ ht, rfl⟩

/-- Recording a deterministic trace does not change its measured work space. -/
theorem spaceUsedOfTrace_runTrace [Fintype κ] (c : Cfg κ Γ Q xs) (n : ℕ) :
    spaceUsedOfTrace (M.runTrace c n) = M.spaceUsed c n := by
  simp only [spaceUsedOfTrace, spaceUsed_eq_sum_visited, visitedOfTrace_runTrace]

@[simp] theorem usesSpace_toBinary_iff [Fintype κ] (xs : List Γ) (s : ℕ) :
    NTM.UsesSpace M.toBinary xs s ↔ M.UsesSpace xs s := by
  simp only [NTM.UsesSpace, Controller.initInput_toBinary,
    Controller.mem_runTraceWith_toBinary_iff, forall_eq, spaceUsedOfTrace_runTrace, UsesSpace]

end Complexity.TM
