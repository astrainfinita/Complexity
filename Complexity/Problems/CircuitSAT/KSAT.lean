/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.Circuit.Tseitin
public import Complexity.Problems.CircuitSAT.Basic
public import Complexity.Problems.KSAT.Basic
public import Complexity.Resources.Circuit.Program
public import Complexity.Classes.Functions.Encoding
public import Complexity.Classes.TreeFunctions.Composition
public import Complexity.Classes.TreeFunctions.UnitTime

/-! # From Boolean circuit satisfiability to 3-SAT

The Tseitin generator preserves satisfiability and is polynomial-time in the
size-charged tree model. The clause-width certificate requires no additional computation.
-/

@[expose] public section

namespace Complexity.CircuitSAT

/-- A circuit is satisfiable exactly when its Tseitin translation is satisfiable. -/
theorem iff_ksat {n : ℕ} (c : Circuit .booleanAlgebra n 1) :
    CircuitSAT ⟨n, c⟩ ↔ KSAT 3 ⟨c.tseitin, c.tseitin_width⟩ := by
  simp only [CircuitSAT, Circuit.eval_eq_true_iff_tseitin, KSAT]
  constructor
  · rintro ⟨_, a, _, ha⟩
    exact ⟨a, ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨fun i => a i.val, a, fun _ => rfl, ha⟩

/-- The width certificate uses the formula's existing encoding. -/
def toKSAT (input : Σ n, Circuit .booleanAlgebra n 1) : KCNF 3 ℕ :=
  ⟨input.2.tseitin, input.2.tseitin_width⟩

theorem toKSAT_correct (input : Σ n, Circuit .booleanAlgebra n 1) :
    CircuitSAT input ↔ KSAT 3 (toKSAT input) := iff_ksat input.2

/-- The reduction has the code of the Tseitin formula. -/
theorem toKSAT_fp : toKSAT ∈ FP .sizeCostTree := by
  obtain ⟨d, t, ⟨s, h⟩, ht⟩ := FP.mem_iff_exists_fdtime.mp Circuit.tseitin_fp
  exact FP.mem_iff_exists_fdtime.mpr ⟨d, t, ⟨s, h.of_encode fun _ => rfl⟩, ht⟩

theorem polytimeManyOneReducible_ksat :
    PolytimeManyOneReducible .sizeCostTree CircuitSAT (KSAT 3) :=
  ⟨toKSAT, toKSAT_fp, toKSAT_correct⟩

end Complexity.CircuitSAT
