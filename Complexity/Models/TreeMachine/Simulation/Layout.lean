/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Encoding

/-! # Register-bank layout

Two banks of data tapes are followed by one unary-counter tape. These definitions describe
only the representation; they are independent of the finite controller implementing it.
-/

@[expose] public section

namespace Complexity.TreeMachine.Simulation.Compiler

variable {k : ℕ}

/-- The physical tape corresponding to a register in the selected bank. -/
def data (b : Bool) (i : Fin k) : Fin (2 * k + 1) :=
  ⟨if b then k + i.val else i.val, by have := i.isLt; split <;> omega⟩

/-- The final work tape is the unary counter. -/
def counter (k : ℕ) : Fin (2 * k + 1) := ⟨2 * k, by omega⟩

theorem data_ne_counter (b : Bool) (i : Fin k) : data b i ≠ counter k := by
  intro h
  have h' := congrArg Fin.val h
  have := i.isLt
  cases b <;> simp [data, counter] at h' <;> omega

theorem data_ne_other (b : Bool) (i j : Fin k) : data b i ≠ data (!b) j := by
  intro h
  have h' := congrArg Fin.val h
  have := i.isLt
  have := j.isLt
  cases b <;> simp [data] at h' <;> omega

end Complexity.TreeMachine.Simulation.Compiler
