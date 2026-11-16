/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Problems.KSAT.Basic

/-! # A sparse-witness verifier for `k`-SAT

A witness lists the variables assigned `true`; every other variable is `false`. A satisfiable
formula has such a witness listing only variables occurring in it, a sublist of `CNF.atoms`,
however large the variable numbers are.
-/

@[expose] public section

namespace Complexity.KSAT

/-- Evaluate the formula with exactly the listed variables true. -/
def verify (k : ℕ) (x : KCNF k ℕ × List ℕ) : Bool :=
  x.1.val.eval fun v => x.2.contains v

/-- A formula is satisfiable exactly when some witness passes that lists only its variables, in
the order of their occurrences. -/
theorem exists_verify_iff {k : ℕ} (f : KCNF k ℕ) :
    KSAT k f ↔ ∃ w : List ℕ, w.Sublist f.val.atoms ∧ verify k (f, w) = true := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨f.val.atoms.filter x, List.filter_sublist, ?_⟩
    rw [verify, ← hx]
    refine CNF.eval_congr _ _ _ fun clause hc l hl => ?_
    have : l.atom ∈ f.val.atoms := CNF.mem_atoms.2 ⟨clause, hc, l, hl, rfl⟩
    cases h : x l.atom <;> simp [List.mem_filter, this, h]
  · rintro ⟨w, -, hw⟩
    exact ⟨fun v => w.contains v, hw⟩

end Complexity.KSAT
