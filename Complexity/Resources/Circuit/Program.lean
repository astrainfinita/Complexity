/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Tactic.TreeProgram.Library
public import Complexity.Resources.Circuit.Tseitin

/-! # A certified tree-machine implementation of the Tseitin transformation -/

@[expose] public section

open Complexity TreeProgram

namespace Complexity.TreeProgram.Source

/-- The Tseitin clauses of a gate, its input wires and its output wire. -/
def gateClauses {α : Type*}
    (x : Σ k, FirstOrder.Language.booleanAlgebra.Functions k × (Fin k → α) × α) : CNF α :=
  CNF.ofGate x.2.1 x.2.2.1 x.2.2.2

theorem gateClauses_size_le {α : Type*} [UniqueEncoding Tree α]
    (x : Σ k, FirstOrder.Language.booleanAlgebra.Functions k × (Fin k → α) × α) :
    ⌜gateClauses x⌝ₜ.size ≤ 4 * ⌜x⌝ₜ.size := by
  rcases x with ⟨k, op, args, out⟩
  exact CNF.size_encode_ofGate_le op args out

@[source] theorem hasProgram_gateClauses {α : Type*} [UniqueEncoding Tree α] :
    HasProgram (gateClauses (α := α)) hole(⊢ program) (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programGateClauses
  fill_hole program in source_fun_prop

theorem gateClauses_fdtisp {α : Type*} [UniqueEncoding Tree α] :
    gateClauses (α := α) ∈ FDTISP .tree (fun n => n ^ 0) (fun n => n ^ 1) := by
  model_fun_prop

/-- Add a gate's clauses to the reversed clause accumulator. -/
def accumulateGate
    (input : CNF ℕ ×
      (Σ k, FirstOrder.Language.booleanAlgebra.Functions k × (Fin k → ℕ) × ℕ)) : CNF ℕ :=
  (gateClauses input.2).foldl (fun acc clause => clause :: acc) input.1

/-- Inputs of `accumulateGate`: the clause accumulator and one gate. -/
abbrev AccumulateInput := CNF ℕ ×
  (Σ k, FirstOrder.Language.booleanAlgebra.Functions k × (Fin k → ℕ) × ℕ)

@[source] theorem hasProgram_accumulateGate :
    HasProgram accumulateGate hole(⊢ program) (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programAccumulateGate
  have : Dominated (fun x : AccumulateInput => (gateClauses x.2).length) (fun _ => 1) :=
    Dominated.of_le_mul 3 (fun x => by
      simpa only [gateClauses, Nat.mul_one] using
        CNF.length_ofGate_le x.2.2.1 x.2.2.2.1 x.2.2.2.2)
  fill_hole program in source_fun_prop (disch := dominated [gateClauses_size_le])

theorem accumulateGate_fdtisp :
    accumulateGate ∈ FDTISP .tree (fun n => n ^ 0) (fun n => n ^ 1) := by
  model_fun_prop

/-- Output size is an ordinary property of the list fold, independent of its certification. -/
theorem accumulateGate_size (input : CNF ℕ ×
    (Σ k, FirstOrder.Language.booleanAlgebra.Functions k × (Fin k → ℕ) × ℕ)) :
    ⌜accumulateGate input⌝ₜ.size + 1 = ⌜gateClauses input.2⌝ₜ.size + ⌜input.1⌝ₜ.size := by
  simpa [accumulateGate] using size_encode_list_append (gateClauses input.2).reverse input.1

abbrev TseitinState := (Σ n, Circuit .booleanAlgebra n 1) × CNF ℕ

/-- Finish an output state with its final clause and the accumulated clauses. -/
def circuitFinish (input : TseitinState) : CNF ℕ :=
  match input.1.2 with
  | .outputs select => ([.pos (select 0).val] :: input.2).reverse
  | .gate _ _ _ => input.2

/-- Remove the current gate while accumulating its clauses. -/
def circuitStep (input : TseitinState) :
    TseitinState :=
  match input.1 with
  | ⟨_, .outputs _⟩ => input
  | ⟨n, .gate (k := k) op args next⟩ =>
      (⟨n + 1, next⟩, accumulateGate (input.2, ⟨k, op, Fin.val ∘ args, n⟩))

/-- Gate input values keep the code of the gate's wire table. -/
theorem size_encode_val_comp {n k : ℕ} (args : Fin k → Fin n) :
    ⌜Fin.val ∘ args⌝ₜ.size = ⌜args⌝ₜ.size := by
  simpa only [encode_fin_function] using congrArg Tree.size (encode_fin_values args)

@[source] theorem hasProgram_circuitStep :
    HasProgram circuitStep hole(⊢ program) (fun x => ⌜x.1⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programCircuitStep
  fill_hole program in
    source_fun_prop (disch := dominated [accumulateGate_size, gateClauses_size_le,
      size_encode_val_comp, size_encode_nat_succ_le])

theorem circuitStep_fdtisp :
    circuitStep ∈ FDTISP .tree (fun n => n ^ 1) (fun n => n ^ 1) := by
  model_fun_prop

/-- Whether the circuit still has a gate to process. -/
def circuitContinues (input : TseitinState) : Bool :=
  match input.1.2 with
  | .outputs _ => false
  | .gate _ _ _ => true

/-- Generate Tseitin clauses using a reversed accumulator. -/
def tseitinLoop : (Σ n, Circuit .booleanAlgebra n 1) → CNF ℕ → CNF ℕ
  | ⟨_, .outputs select⟩, acc => ([.pos (select 0).val] :: acc).reverse
  | ⟨n, .gate (k := k) op args next⟩, acc =>
    tseitinLoop ⟨n + 1, next⟩ (accumulateGate (acc, ⟨k, op, Fin.val ∘ args, n⟩))
termination_by input _ => input.2.size

theorem tseitinLoop_eq {n : ℕ} (c : Circuit .booleanAlgebra n 1) (acc : CNF ℕ) :
    tseitinLoop ⟨n, c⟩ acc = acc.reverse ++ c.tseitin := by
  cases c with
  | outputs select => simp [tseitinLoop, List.reverse_cons]
  | gate op args next =>
    rw [tseitinLoop, tseitinLoop_eq]
    simp [accumulateGate, gateClauses, List.reverse_append, List.append_assoc]
termination_by c.size

theorem tseitinLoop_nil (input : Σ n, Circuit .booleanAlgebra n 1) :
    tseitinLoop input [] = input.2.tseitin := by
  simpa using tseitinLoop_eq input.2 []

-- The recursive equation is checked on the source function, independently of generated code.
theorem tseitinLoop_step (x : TseitinState) :
    tseitinLoop x.1 x.2 = if circuitContinues x then
      tseitinLoop (circuitStep x).1 (circuitStep x).2 else circuitFinish x := by
  rcases x with ⟨⟨n, c⟩, acc⟩
  cases c <;> simp [circuitContinues, circuitStep, circuitFinish, tseitinLoop]

theorem tseitinLoop_state_size (x y : TseitinState)
    (hi : ⌜y.1⌝ₜ.size ≤ ⌜x.1⌝ₜ.size ∧ tseitinLoop y.1 y.2 = tseitinLoop x.1 x.2) :
    ⌜y⌝ₜ.size ≤ 10 * ⌜x⌝ₜ.size ^ 2 := by
  rcases x with ⟨⟨n, c⟩, acc⟩
  rcases y with ⟨⟨m, d⟩, bs⟩
  have hx := size_encode_list_append acc.reverse c.tseitin
  have hy := size_encode_list_append bs.reverse d.tseitin
  have he := congrArg (fun a : CNF ℕ => ⌜a⌝ₜ.size) hi.2
  simp only [tseitinLoop_eq, size_encode_reverse] at he hx hy
  have hc : ⌜(m, d)⌝ₜ.size ≤ ⌜(n, c)⌝ₜ.size := hi.1
  have hl : ⌜((m, d), bs)⌝ₜ.size ≤ ⌜((n, c), acc)⌝ₜ.size + ⌜c.tseitin⌝ₜ.size := by
    simp only [size_encode_prod] at hc ⊢
    omega
  have hp : ⌜(n, c)⌝ₜ.size ≤ ⌜((n, c), acc)⌝ₜ.size := by simp; omega
  have ho := c.size_encode_tseitin_le.trans (Nat.mul_le_mul_left 8 (pow_le_pow_left' hp 2))
  have hn := Nat.le_self_pow (by decide : 2 ≠ 0) ⌜((n, c), acc)⌝ₜ.size
  change ⌜((m, d), bs)⌝ₜ.size ≤ 10 * ⌜((n, c), acc)⌝ₜ.size ^ 2
  omega

@[source] theorem hasProgram_circuitContinues :
    HasProgram circuitContinues hole(⊢ program) (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programCircuitContinues
  fill_hole program in source_fun_prop

theorem circuitContinues_fdtisp :
    circuitContinues ∈ FDTISP .tree (fun n => n ^ 0) (fun n => n ^ 1) := by
  model_fun_prop

@[source] theorem hasProgram_circuitFinish :
    HasProgram circuitFinish hole(⊢ program) (fun x => ⌜x⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programCircuitFinish
  fill_hole program in source_fun_prop

theorem circuitFinish_fdtisp :
    circuitFinish ∈ FDTISP .tree (fun n => n ^ 1) (fun n => n ^ 1) := by
  model_fun_prop

theorem circuitStep_circuit_size_lt
    (x : TseitinState) (ht : circuitContinues x = true) :
    ⌜(circuitStep x).1⌝ₜ.size < ⌜x.1⌝ₜ.size := by
  rcases x with ⟨⟨n, c⟩, acc⟩
  cases c with
  | outputs select => cases ht
  | gate op args next =>
    have := size_encode_nat_succ_le n
    simp only [circuitStep, Sigma.encode_mk, size_encode_prod,
      Circuit.encode_gate, size_encode_unit]
    omega

theorem hasProgram_tseitinLoop :
    HasProgram (fun x : TseitinState => tseitinLoop x.1 x.2) hole(⊢ program)
      (fun x => ⌜x⌝ₜ.size ^ 2) (fun x => ⌜x⌝ₜ.size ^ 2) := by
  abstract_hole program using programTseitinLoop
  fill_hole program in
    source_fun_prop using loop
      (test := circuitContinues) (next := circuitStep) (finish := circuitFinish)
      (invariant := fun x y => ⌜y.1⌝ₜ.size ≤ ⌜x.1⌝ₜ.size ∧
        tseitinLoop y.1 y.2 = tseitinLoop x.1 x.2)
      (measure := fun x => ⌜x.1⌝ₜ.size) (step := fun x => ⌜x⌝ₜ.size)
      (stop := fun x => ⌜x⌝ₜ.size ^ 2) (space := fun x => ⌜x⌝ₜ.size ^ 2)
  case equation => exact tseitinLoop_step
  case initial => intro x; exact ⟨le_rfl, rfl⟩
  case next_state =>
    intro x y hi ht
    refine ⟨(circuitStep_circuit_size_lt y ht).le.trans hi.1, ?_⟩
    simpa only [tseitinLoop_step y, ht, ↓reduceIte] using hi.2
  case decreases => intro x y _ ht; exact circuitStep_circuit_size_lt y ht
  case step_pos => exact fun _ => Tree.size_pos _
  case stop_pos => exact fun _ => Nat.pow_pos (Tree.size_pos _)
  all_goals exact Dominated.of_le_mul _ (fun z => tseitinLoop_state_size z.1.1 z.1.2 z.2)

theorem tseitinLoop_fdtisp :
    (fun x : TseitinState => tseitinLoop x.1 x.2) ∈
      FDTISP .tree (fun n => n ^ 2) (fun n => n ^ 2) :=
  hasProgram_tseitinLoop.mem_fdtisp_pow (by decide)

attribute [source] hasProgram_tseitinLoop

@[local source] theorem tseitin_source :
    (fun input : Σ n, Circuit .booleanAlgebra n 1 => input.2.tseitin) =
      (fun input => tseitinLoop input []) := (funext tseitinLoop_nil).symm

theorem _root_.Complexity.Circuit.tseitin_fdtisp :
    (fun input : Σ n, Circuit .booleanAlgebra n 1 => input.2.tseitin) ∈
      FDTISP .tree (fun n => n ^ 2) (fun n => n ^ 2) := by
  model_fun_prop

end Complexity.TreeProgram.Source
