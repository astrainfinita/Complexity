/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Problems.CircuitSAT.Basic
public import Complexity.Problems.KSAT.Verifier
public import Complexity.Models.Circuit.Tseitin

/-! # A sparse-witness verifier for circuit satisfiability

A witness lists the input wires assigned `true`; every other input is `false`. The input count
may be written in binary and most inputs may be unused, so a witness must not list every input.
A satisfiable circuit has a witness listing only wires of its Tseitin formula.
-/

@[expose] public section

namespace Complexity.CircuitSAT

/-- Evaluate the circuit with exactly the listed input wires true. -/
def verify (x : (Σ n, Circuit .booleanAlgebra n 1) × List ℕ) : Bool :=
  x.1.2.eval (fun i => x.2.contains i.val) 0

/-- A circuit is satisfiable exactly when some witness passes that lists only wires of its Tseitin
formula: the witness of that formula. -/
theorem exists_verify_iff (c : Σ n, Circuit .booleanAlgebra n 1) :
    CircuitSAT c ↔ ∃ w : List ℕ, w.Sublist c.2.tseitin.atoms ∧ verify (c, w) = true := by
  rcases c with ⟨n, c⟩
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨a, -, ha⟩ := (c.eval_eq_true_iff_tseitin x).mp hx
    obtain ⟨w, hw, hv⟩ := (KSAT.exists_verify_iff ⟨c.tseitin, c.tseitin_width⟩).mp ⟨a, ha⟩
    exact ⟨w, hw, (c.eval_eq_true_iff_tseitin _).mpr ⟨fun v => w.contains v, fun _ => rfl, hv⟩⟩
  · rintro ⟨w, -, hw⟩
    exact ⟨_, hw⟩

end Complexity.CircuitSAT
