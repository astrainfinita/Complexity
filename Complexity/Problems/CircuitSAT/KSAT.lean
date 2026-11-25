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

open TreeProgram.Source

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

/-- The reduction has the code of the Tseitin formula, quadratic in the code of the circuit. -/
@[dominated] theorem size_encode_toKSAT_le (input : Σ n, Circuit .booleanAlgebra n 1) :
    ⌜toKSAT input⌝ₜ.size ≤ 8 * ⌜input⌝ₜ.size ^ 2 :=
  input.2.size_encode_tseitin_le

/-- The reduction is the Tseitin transformation: quadratic time and peak. -/
@[program] theorem hasProgramIn_toKSAT : HasProgramIn toKSAT hole(⊢ program)
    IsO(fun x => ⌜x⌝ₜ.size ^ 2) IsO(fun x => ⌜x⌝ₜ.size ^ 2) := by
  abstract_hole program using programToKSAT
  fill_hole program in source_fun_prop

theorem toKSAT_fp : toKSAT ∈ FP .sizeCostTree := by
  model_fun_prop

theorem polytimeManyOneReducible_ksat :
    PolytimeManyOneReducible .sizeCostTree CircuitSAT (KSAT 3) :=
  ⟨toKSAT, toKSAT_fp, toKSAT_correct⟩

end Complexity.CircuitSAT
