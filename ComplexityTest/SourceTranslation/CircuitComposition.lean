/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Complexity.Resources.Circuit.Unroll
import Complexity.Resources.Circuit.Composition
import Complexity.Classes.Functions.Basic
open Complexity TreeProgram Complexity.TreeProgram.Source
open Complexity.TreeProgram.Source.Internal (HasProgramInO)

namespace ComplexityTest.SourceTranslation.CircuitComposition

-- The structural recursion entry keeps the previously selected callback programs.
example : programCompFn =
    Recursion.code programCompTest programCompNextFn programCompFinishFn programCompResume := rfl

-- Recursive certification keeps the explicitly selected terminal callback.
example : programRelabelFn = Recursion.code programRelabelTest programRelabelNextFn
    programRelabelFinishFn programRelabelResume := rfl
example : HasProgramInO relabelFinishFn programRelabelFinishFn
    (fun x => ⌜x⌝ₜ.size ^ 3) (fun x => ⌜x⌝ₜ.size ^ 2) :=
      hasProgramIn_relabelFinishFn.toHasProgramInO

def rewire (x : RelabelInput) : Σ n, Σ m, Circuit .booleanAlgebra n m :=
  ⟨x.k, x.m, x.circuit.relabel x.wires⟩
example := (by source_fun_prop : HasProgramInO rewire _ _ _)

def pipeline (x : CompInput) : Σ n, Σ m, Circuit .booleanAlgebra n m :=
  ⟨x.n, x.k, x.first.comp x.second⟩
example := (by source_fun_prop : HasProgramInO pipeline _ _ _)

def preserve (x : Σ n, Σ m, Circuit .booleanAlgebra n m) :
    Σ n, Σ m, Circuit .booleanAlgebra n m := ⟨x.1, x.1 + x.2.1, x.2.2.keepInputs⟩
example := (by source_fun_prop : HasProgramInO preserve _ _ _)

def layers (x : Σ n, Circuit .booleanAlgebra (n + 1) n × ℕ) :
    Σ n, Σ m, Circuit .booleanAlgebra n m :=
  ⟨x.1 + x.2.2, x.1, x.2.1.unroll x.2.2⟩
example := (by source_fun_prop : HasProgramInO layers _ _ _)

/-- Rewiring an already represented set of inputs, retaining the same input count. -/
def rewireStored (x : Σ n, Σ m, Circuit .booleanAlgebra n m × (Fin n → Fin n)) :
    Σ n, Σ m, Circuit .booleanAlgebra n m := ⟨x.1, x.2.1, x.2.2.1.relabel x.2.2.2⟩

abbrev StoredRelabelInput := Σ n, Σ m, Circuit .booleanAlgebra n m × (Fin n → Fin n)

-- The stored table bounds the wire count by code size, so the relabelling scale is linear in it
-- and the growths polynomial; only the size relations of the circuit are named.
/-- Compose the selected implementation; the translated growths are polynomial in code size. -/
@[program] theorem hasProgramIn_rewireStored : HasProgramIn rewireStored hole(⊢ program)
    (IsPoly fun x => ⌜x⌝ₜ.size) (IsPoly fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programRewireStored
  fill_hole program in source_fun_prop (disch := dominated [relabelScale, Circuit.size_relabel,
    Circuit.outputs_le_size_encode, Circuit.size_le_size_encode])

theorem rewireStored_fp : rewireStored ∈ FP .tree := hasProgramIn_rewireStored.mem_fp

/-- Unary storage makes the number of generated layers bounded by input size. -/
def layersStored (x : Σ n, Circuit .booleanAlgebra (n + 1) n × List Unit) :
    Σ n, Σ m, Circuit .booleanAlgebra n m :=
  ⟨x.1 + x.2.2.length, x.1, x.2.1.unroll x.2.2.length⟩

-- The layer count is the length of a stored list; the unrolling scale is then polynomial in code
-- size, with the step's gate count times the layer count.
theorem layersStored_fp : layersStored ∈ FP .tree := by
  model_fun_prop (disch := dominated [unrollScale, Circuit.outputs_le_size_encode,
    Circuit.size_le_size_encode, length_le_codeSize])

end ComplexityTest.SourceTranslation.CircuitComposition
