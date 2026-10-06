/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.Circuit.Basic
public import Complexity.ModelTheory.Algebra.BooleanAlgebra.Basic

/-! # Boolean circuit satisfiability -/

@[expose] public section

namespace Complexity

open FirstOrder

/-- A single-output Boolean circuit is satisfiable if some input makes its output true.
The Boolean interpretation is fixed to the standard operations on `Bool`. -/
def CircuitSAT (c : Σ n : ℕ, Circuit .booleanAlgebra n 1) : Prop :=
  ∃ x : Fin c.1 → Bool, c.2.eval x 0 = true

namespace CircuitSAT

open BooleanAlgebra

variable {n : ℕ}

@[simp] theorem outputs (select : Fin 1 → Fin n) :
    CircuitSAT ⟨n, Circuit.outputs select⟩ := ⟨fun _ => true, rfl⟩

@[simp] theorem ofGate_top (args : Fin 0 → Fin n) :
    CircuitSAT ⟨n, Circuit.ofGate topFunc args⟩ := by
  refine ⟨fun _ => false, ?_⟩
  simp

@[simp] theorem not_ofGate_bot (args : Fin 0 → Fin n) :
    ¬ CircuitSAT ⟨n, Circuit.ofGate botFunc args⟩ := by
  rintro ⟨x, h⟩
  simp at h

end CircuitSAT

end Complexity
