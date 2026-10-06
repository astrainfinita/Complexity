/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Data.CNF.Basic

/-! # Satisfiability with at most three literals per clause -/

@[expose] public section

namespace Complexity

/-- A CNF with at most three literal occurrences in every clause. -/
abbrev ThreeCNF (α : Type*) := {f : CNF α // ∀ clause ∈ f, clause.length ≤ 3}

/-- A three-CNF over natural-number variables has a satisfying assignment. -/
def ThreeSAT (f : ThreeCNF ℕ) : Prop :=
  ∃ x : ℕ → Bool, f.val.eval x = true

namespace ThreeSAT

variable {f : ThreeCNF ℕ}

@[simp] theorem nil : ThreeSAT ⟨[], by simp⟩ := ⟨fun _ => false, rfl⟩

theorem not_of_nil_mem (h : [] ∈ f.val) : ¬ ThreeSAT f := by
  rintro ⟨x, hx⟩
  simpa using (CNF.eval_eq_true f.val x).mp hx [] h

end ThreeSAT

end Complexity
