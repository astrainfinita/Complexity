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
  ⟨x.k, x.m, x.circuit.relabel x.wires.get⟩
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

/-- Rewiring an already represented set of inputs, retaining the same input count. The table is
stored as a `FinVector`. -/
def rewireStored (x : Σ n, Σ m, Circuit .booleanAlgebra n m × FinVector (Fin n) n) :
    Σ n, Σ m, Circuit .booleanAlgebra n m := ⟨x.1, x.2.1, x.2.2.1.relabel x.2.2.2.get⟩

abbrev StoredRelabelInput := Σ n, Σ m, Circuit .booleanAlgebra n m × FinVector (Fin n) n

-- The stored table bounds the wire count by code size, so the relabelling scale is linear in it
-- and the growths polynomial; only the size relations of the circuit are named.
/-- Compose the selected implementation; the translated growths are polynomial in code size. -/
@[program] theorem hasProgramIn_rewireStored : HasProgramIn rewireStored hole(⊢ program)
    (IsPoly fun x => ⌜x⌝ₜ.size) (IsPoly fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programRewireStored
  fill_hole program in source_fun_prop (disch := dominated [relabelScale, Circuit.size_relabel,
    Circuit.outputs_le_size_encode, Circuit.size_le_size_encode])

-- Guards the forms in which programs build and match circuits: the constructors with `v.get` for
-- a `FinVector` `v`, `Circuit.casesFinVector`, and `mapOutputs`, `keepWires` and `relabel` at
-- `v.get` (`relabel` is guarded by `rewire` and `rewireStored` above).
example := (by source_fun_prop :
  HasProgramInO (fun x : Σ n, Σ m, FinVector (Fin n) m =>
    (⟨x.1, x.2.1, Circuit.outputs x.2.2.get⟩ : Σ n, Σ m, Circuit .booleanAlgebra n m)) _ _ _)

example := (by source_fun_prop :
  HasProgramInO (fun x : Σ n, Σ m, Σ k, FirstOrder.Language.booleanAlgebra.Functions k ×
      FinVector (Fin n) k × Circuit .booleanAlgebra (n + 1) m =>
    (⟨x.1, x.2.1, Circuit.gate x.2.2.2.1 x.2.2.2.2.1.get x.2.2.2.2.2⟩ :
      Σ n, Σ m, Circuit .booleanAlgebra n m)) _ _ _)

example := (by source_fun_prop : HasProgramInO (fun x : Σ n, Circuit .booleanAlgebra n 1 =>
  x.2.casesFinVector (fun _ _ => false) fun _ _ _ _ => true) _ _ _)

example := (by source_fun_prop :
  HasProgramInO (fun x : Σ n, Σ m, Σ k, Circuit .booleanAlgebra n m × FinVector (Fin m) k =>
    (⟨x.1, x.2.2.1, x.2.2.2.1.mapOutputs x.2.2.2.2.get⟩ :
      Σ n, Σ k, Circuit .booleanAlgebra n k)) _ _ _)

example := (by source_fun_prop :
  HasProgramInO (fun x : Σ p, Σ n, Σ m, Circuit .booleanAlgebra n m × FinVector (Fin n) p =>
    (⟨x.2.1, x.1 + x.2.2.1, x.2.2.2.1.keepWires x.2.2.2.2.get⟩ :
      Σ n, Σ m, Circuit .booleanAlgebra n m)) _ _ _)

-- Guards that a program cannot see a wire table as a function `Fin k → Fin n`: a `match` on a
-- circuit, which binds the tables as functions, is not translated; neither is a circuit or a gate
-- built from a function literal, an operation on circuits (`relabel`, `keepWires`, `mapOutputs`)
-- at a function other than `v.get`, a `FinVector` built by `FinVector.ofFn`, a `FinVector`'s
-- indexing function as a result, nor a circuit built from a stored function table.
example : True := by
  fail_if_success have := (by source_fun_prop :
    HasProgramInO (fun x : Σ n, Circuit .booleanAlgebra n 1 =>
      match x.2 with | .outputs _ => false | .gate _ _ _ => true) _ _ _)
  fail_if_success have := (by source_fun_prop :
    HasProgramInO (fun n : ℕ =>
      (⟨n, n, Circuit.outputs (fun i : Fin n => i)⟩ :
        Σ n, Σ m, Circuit .booleanAlgebra n m)) _ _ _)
  fail_if_success have := (by source_fun_prop :
    HasProgramInO (fun x : Σ n, Σ m, Circuit .booleanAlgebra n m =>
      (⟨x.1 + 1, x.2.1, x.2.2.relabel Fin.castSucc⟩ :
        Σ n, Σ m, Circuit .booleanAlgebra n m)) _ _ _)
  fail_if_success have := (by source_fun_prop :
    HasProgramInO (fun x : Σ n, Fin n × Circuit .booleanAlgebra (n + 1) 1 =>
      (⟨x.1, 1, Circuit.gate FirstOrder.BooleanAlgebra.complFunc (fun _ => x.2.1) x.2.2⟩ :
        Σ n, Σ m, Circuit .booleanAlgebra n m)) _ _ _)
  fail_if_success have := (by source_fun_prop :
    HasProgramInO (fun x : Σ n, Σ m, Circuit .booleanAlgebra n m =>
      (⟨x.1, x.1 + x.2.1, x.2.2.keepWires id⟩ : Σ n, Σ m, Circuit .booleanAlgebra n m)) _ _ _)
  fail_if_success have := (by source_fun_prop :
    HasProgramInO (fun x : Σ n, Σ m, Circuit .booleanAlgebra n (m + 1) =>
      (⟨x.1, x.2.1, x.2.2.mapOutputs Fin.castSucc⟩ : Σ n, Σ m, Circuit .booleanAlgebra n m)) _ _ _)
  fail_if_success have := (by source_fun_prop :
    HasProgramInO (fun n : ℕ =>
      (⟨n, FinVector.ofFn (fun i : Fin n => i)⟩ : Σ n, FinVector (Fin n) n)) _ _ _)
  fail_if_success have := (by source_fun_prop :
    HasProgramInO (fun x : Σ n, FinVector (Fin n) n => x.2.get) _ _ _)
  fail_if_success have := (by source_fun_prop :
    HasProgramInO (fun x : Σ n, Σ m, (Fin m → Fin n) =>
      (⟨x.1, x.2.1, Circuit.outputs x.2.2⟩ : Σ n, Σ m, Circuit .booleanAlgebra n m)) _ _ _)
  trivial

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
