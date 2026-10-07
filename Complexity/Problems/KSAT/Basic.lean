/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Data.CNF.Basic

/-! # Satisfiability with a fixed bound on clause width -/

@[expose] public section

namespace Complexity

/-- A CNF with at most `k` literal occurrences in every clause. -/
abbrev KCNF (k : ℕ) (α : Type*) := {f : CNF α // ∀ clause ∈ f, clause.length ≤ k}

/-- A `k`-CNF over natural-number variables has a satisfying assignment. -/
def KSAT (k : ℕ) (f : KCNF k ℕ) : Prop :=
  ∃ x : ℕ → Bool, f.val.eval x = true

namespace KSAT

variable {k : ℕ} {f : KCNF k ℕ}

@[simp] theorem nil (k : ℕ) : KSAT k ⟨[], by simp⟩ := ⟨fun _ => false, rfl⟩

theorem not_of_nil_mem (h : [] ∈ f.val) : ¬ KSAT k f := by
  rintro ⟨x, hx⟩
  simpa using (CNF.eval_eq_true f.val x).mp hx [] h

end KSAT

end Complexity
