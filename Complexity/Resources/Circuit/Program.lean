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

-- Save the public proof's allowance for the very same compiled program.
@[scoped source] theorem gateClauses_model {α : Type*} [UniqueEncoding Tree α] :
    ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace (gateClauses (α := α))
      (fun _ => 61) (fun n => k * (4 * n + 2)) := by
  model_fun_prop

/-- Add a gate's clauses to the reversed clause accumulator. -/
def accumulateGate
    (input : CNF ℕ ×
      (Σ k, FirstOrder.Language.booleanAlgebra.Functions k × (Fin k → ℕ) × ℕ)) : CNF ℕ :=
  (gateClauses input.2).foldl (fun acc clause => clause :: acc) input.1

@[scoped source] theorem accumulateGate_model :
    ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace accumulateGate
      (fun _ => 200) (fun n => k * (8 * n + 8)) := by
  model_fun_prop
  all_goals
    rename_i input
    have hg := gateClauses_size_le input.2
    have hl : (gateClauses input.2).length ≤ 3 := CNF.length_ofGate_le _ _ _
    have ha := size_encode_list_append (gateClauses input.2).reverse input.1
    rcases input with ⟨acc, gate⟩
    simp only [size_encode_reverse, size_encode_prod] at *
    omega

/-- Output size is an ordinary property of the list fold, independent of its certification. -/
theorem accumulateGate_size (input : CNF ℕ ×
    (Σ k, FirstOrder.Language.booleanAlgebra.Functions k × (Fin k → ℕ) × ℕ)) :
    ⌜accumulateGate input⌝ₜ.size + 1 = ⌜gateClauses input.2⌝ₜ.size + ⌜input.1⌝ₜ.size := by
  simpa [accumulateGate] using size_encode_list_append (gateClauses input.2).reverse input.1

/-- Finish an output state with its final clause and the accumulated clauses. -/
def circuitFinish (input : (Σ n, Circuit .booleanAlgebra n 1) × CNF ℕ) : CNF ℕ :=
  match input.1.2 with
  | .outputs select => ([.pos (select 0).val] :: input.2).reverse
  | .gate _ _ _ => input.2

/-- Remove the current gate while accumulating its clauses. -/
def circuitStep (input : (Σ n, Circuit .booleanAlgebra n 1) × CNF ℕ) :
    (Σ n, Circuit .booleanAlgebra n 1) × CNF ℕ :=
  match input.1 with
  | ⟨_, .outputs _⟩ => input
  | ⟨n, .gate (k := k) op args next⟩ =>
      (⟨n + 1, next⟩, accumulateGate (input.2, ⟨k, op, Fin.val ∘ args, n⟩))

-- Both the loop and the compatibility bound reuse this program and its computed budget.
section
@[local source] theorem circuitStep_source : circuitStep = circuitStep := rfl

-- Estimate the already saved program once, retaining dependence on the remaining circuit.
private theorem circuitStep_bounds (x : (Σ n, Circuit .booleanAlgebra n 1) × CNF ℕ) :
    let implementation : Implementation circuitStep := by source_fun_prop
    implementation.bounds.time x ≤ 28 * ⌜x.1⌝ₜ.size + 300 ∧
      implementation.bounds.peak x ≤ 12 * ⌜x⌝ₜ.size + 20 := by
  dsimp only
  rcases x with ⟨⟨n, c⟩, acc⟩
  cases c with
  | outputs select =>
    simp -implicitDefEqProofs only [source_bounds]
    simp
    omega
  | @gate _ _ k op args next =>
    simp -implicitDefEqProofs only [source_bounds]
    have hn := length_le_codeSize n.bits
    have hs := size_encode_nat_succ_le n
    have ha := accumulateGate_size (acc, ⟨k, op, Fin.val ∘ args, n⟩)
    have hg := gateClauses_size_le (⟨k, op, Fin.val ∘ args, n⟩ :
      Σ k, FirstOrder.Language.booleanAlgebra.Functions k × (Fin k → ℕ) × ℕ)
    simp at *
    omega

theorem circuitStep_realizes :
    Realizes circuitStep ⟨fun x => 28 * ⌜x.1⌝ₜ.size + 300, fun x => 12 * ⌜x⌝ₜ.size + 20⟩ := by
  refine Realizes.mono (by source_fun_prop) ?_
  intro x
  simpa -implicitDefEqProofs only [source_bounds] using circuitStep_bounds x

/-- Whether the circuit still has a gate to process. -/
def circuitContinues (input : (Σ n, Circuit .booleanAlgebra n 1) × CNF ℕ) : Bool :=
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
theorem tseitinLoop_step (x : (Σ n, Circuit .booleanAlgebra n 1) × CNF ℕ) :
    tseitinLoop x.1 x.2 = if circuitContinues x then
      tseitinLoop (circuitStep x).1 (circuitStep x).2 else circuitFinish x := by
  rcases x with ⟨⟨n, c⟩, acc⟩
  cases c <;> simp [circuitContinues, circuitStep, circuitFinish, tseitinLoop]

private theorem tseitinLoop_state_size (x y : (Σ n, Circuit .booleanAlgebra n 1) × CNF ℕ)
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

@[local source] theorem tseitinLoop_model : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace
    (fun x : (Σ n, Circuit .booleanAlgebra n 1) × CNF ℕ => tseitinLoop x.1 x.2)
    (fun n => 2000 * n ^ 2 + 4) (fun n => k * (140 * n ^ 2 + 2)) := by
  model_fun_prop using loop
    (test := circuitContinues) (next := circuitStep) (finish := circuitFinish)
    (invariant := fun x y => ⌜y.1⌝ₜ.size ≤ ⌜x.1⌝ₜ.size)
    (time := fun x y => 500 * (⌜x⌝ₜ.size * ⌜y.1⌝ₜ.size + ⌜x⌝ₜ.size ^ 2))
    (space := fun x => 140 * ⌜x⌝ₜ.size ^ 2)
    (next_bound := circuitStep_bounds)
  case equation => exact tseitinLoop_step
  case initial => intro x; exact le_rfl
  case input_size =>
    intro x y hi he
    have hs := tseitinLoop_state_size x y ⟨hi, he⟩
    omega
  case check_space =>
    rintro x ⟨⟨n, c⟩, acc⟩ hi he
    have hs := tseitinLoop_state_size x (⟨n, c⟩, acc) ⟨hi, he⟩
    rcases x with ⟨⟨m, d⟩, bs⟩
    cases c <;> simp at hs ⊢ <;> omega
  case stop_bounds =>
    rintro x ⟨⟨n, c⟩, acc⟩ hi he ht
    have hs := tseitinLoop_state_size x (⟨n, c⟩, acc) ⟨hi, he⟩
    have hl := length_le_codeSize acc
    rcases x with ⟨⟨m, d⟩, bs⟩
    cases c with
    | outputs select =>
      simp at hs ⊢
      omega
    | gate op args next => simp [circuitContinues] at ht
  case step_bounds =>
    rintro x ⟨⟨n, c⟩, acc⟩ hi he ht
    have hstate := tseitinLoop_state_size x (⟨n, c⟩, acc) ⟨hi, he⟩
    refine ⟨?_, ?_⟩
    · have := Tree.size_pos ⌜x⌝ₜ
      have := Nat.le_self_pow (by decide : 2 ≠ 0) ⌜x⌝ₜ.size
      simp only [Sigma.encode_mk, size_encode_prod] at hstate ⊢
      omega
    cases c with
    | outputs select => simp [circuitContinues] at ht
    | @gate _ _ k op args next =>
      have hn := size_encode_nat_succ_le n
      have hm : ⌜(⟨n + 1, next⟩ : Σ n, Circuit .booleanAlgebra n 1)⌝ₜ.size <
          ⌜(⟨n, .gate op args next⟩ : Σ n, Circuit .booleanAlgebra n 1)⌝ₜ.size := by
        simp only [Sigma.encode_mk, size_encode_prod, Circuit.encode_gate, size_encode_unit] at *
        omega
      refine ⟨hm.le.trans hi, ?_⟩
      have hmul := Nat.mul_le_mul_left (500 * ⌜x⌝ₜ.size) hm
      rcases x with ⟨⟨m, d⟩, bs⟩
      dsimp only [circuitStep]
      simp only [Sigma.encode_mk, size_encode_prod, UniqueEncoding.ofLeftInjection_encode,
        Circuit.encode_gate, size_encode_unit, Nat.succ_eq_add_one] at hi hmul ⊢
      nlinarith only [hmul, hi]
  case hb.left =>
    rename_i x
    have h : ⌜x.1⌝ₜ.size ≤ ⌜x⌝ₜ.size := by
      rcases x with ⟨a, b⟩; simp; omega
    have := Tree.size_pos ⌜x⌝ₜ
    nlinarith
  case hb.right =>
    rename_i x
    have := Nat.le_self_pow (by decide : 2 ≠ 0) ⌜x⌝ₜ.size
    omega

@[local source] theorem tseitin_source :
    (fun input : Σ n, Circuit .booleanAlgebra n 1 => input.2.tseitin) =
      (fun input => tseitinLoop input []) := (funext tseitinLoop_nil).symm

theorem _root_.Complexity.Circuit.tseitin_model :
    ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace
      (fun input : Σ n, Circuit .booleanAlgebra n 1 => input.2.tseitin)
      (fun n => 20000 * n ^ 2 + 4) (fun n => k * (2000 * n ^ 2 + 2)) := by
  model_fun_prop
  all_goals
    rename_i input
    have := Tree.size_pos ⌜input⌝ₜ
    nlinarith

theorem _root_.Complexity.Circuit.tseitin_ftisp :
    (fun input : Σ n, Circuit .booleanAlgebra n 1 => input.2.tseitin) ∈
      FTISP .tree (fun n => n ^ 2) (fun n => n ^ 2) := by
  obtain ⟨k, hk⟩ := Circuit.tseitin_model
  refine ⟨_, _, hk, IsBigO.iff_exists_nat.mpr ⟨20004, 1, ?_⟩,
    IsBigO.iff_exists_nat.mpr ⟨2002 * k, 1, ?_⟩⟩
  · intro n hn; nlinarith
  · intro n hn
    have h : 2000 * n ^ 2 + 2 ≤ 2002 * n ^ 2 := by nlinarith
    simpa only [← Nat.mul_assoc, Nat.mul_comm k 2002] using Nat.mul_le_mul_left k h
end

end Complexity.TreeProgram.Source
