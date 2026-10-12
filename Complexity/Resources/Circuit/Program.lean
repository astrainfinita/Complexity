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

-- The saved implementation below imports this certificate for source decomposition.
theorem gateClauses_realizes {α : Type*} [UniqueEncoding Tree α] :
    Realizes (gateClauses (α := α)) ⟨fun _ => 57, fun x => 4 * ⌜x⌝ₜ.size⟩ := by
  source_cases

@[local fun_prop, source_bounds↓] noncomputable def gateClausesImplementation
    {α : Type*} [UniqueEncoding Tree α] :=
  (gateClauses_realizes (α := α)).implementation

/-- Add a gate's clauses to the reversed clause accumulator. -/
def accumulateGate
    (input : CNF ℕ ×
      (Σ k, FirstOrder.Language.booleanAlgebra.Functions k × (Fin k → ℕ) × ℕ)) : CNF ℕ :=
  (gateClauses input.2).foldl (fun acc clause => clause :: acc) input.1

theorem accumulateGate_realizes :
    Realizes accumulateGate ⟨fun _ => 196, fun input => 8 * ⌜input⌝ₜ.size + 6⟩ := by
  refine Realizes.mono (by source_fun_prop) ?_
  rintro ⟨acc, gate⟩
  have hg : ⌜gateClauses gate⌝ₜ.size ≤ 4 * ⌜gate⌝ₜ.size :=
    (gateClauses_realizes.size_le gate).trans (max_le (by omega) le_rfl)
  have hl : (gateClauses gate).length ≤ 3 := CNF.length_ofGate_le _ _ _
  simp only [compBounds_time, pairBounds_time, projectionBounds_time, Nat.reduceAdd,
    foldlSumBounds_time, size_encode_prod, Function.uncurry_apply_pair, encode_list_cons,
    foldlCost_time_sum, List.map_const', List.sum_replicate, smul_eq_mul, compBounds_peak,
    pairBounds_peak, projectionBounds_peak, Nat.max_assoc, le_max_iff, Std.le_refl,
    add_le_add_iff_left, true_or, sup_of_le_right, foldlSumBounds_peak, sup_le_iff]
  refine ⟨by omega, by omega, by omega, by omega, ?_⟩
  refine (foldlCost_peak_le _ _ ?_ ?_).trans ?_
  · intros; simp only [encode_list_cons, size_encode_prod]; omega
  · intros; simp only [size_encode_prod]; omega
  · omega

@[local fun_prop, source_bounds↓] private noncomputable def accumulateGateImplementation :=
  accumulateGate_realizes.implementation

/-- Accumulate the current gate, or finish the formula with the output clause. -/
def circuitClausesStep (input : (Σ n, Circuit .booleanAlgebra n 1) × CNF ℕ) : CNF ℕ :=
  match input.1 with
  | ⟨_, .outputs select⟩ => ([.pos (select 0).val] :: input.2).reverse
  | ⟨n, .gate (k := k) op args _⟩ =>
    accumulateGate (input.2, ⟨k, op, Fin.val ∘ args, n⟩)

theorem circuitClausesStep_realizes :
    Realizes circuitClausesStep
      ⟨fun x => 13 * ⌜x⌝ₜ.size + 300, fun x => 12 * ⌜x⌝ₜ.size + 20⟩ := by
  refine Realizes.mono (by source_fun_prop) ?_
  rintro ⟨⟨n, c⟩, acc⟩
  cases c with
  | outputs select =>
    have ha := length_le_codeSize acc
    simp at *
    omega
  | gate op args next => simp; omega

/-- Remove the current gate while accumulating its clauses. -/
def circuitStep (input : (Σ n, Circuit .booleanAlgebra n 1) × CNF ℕ) :
    (Σ n, Circuit .booleanAlgebra n 1) × CNF ℕ :=
  match input.1 with
  | ⟨_, .outputs _⟩ => input
  | ⟨n, .gate (k := k) op args next⟩ =>
      (⟨n + 1, next⟩, accumulateGate (input.2, ⟨k, op, Fin.val ∘ args, n⟩))

theorem circuitStep_realizes :
    Realizes circuitStep ⟨fun x => 28 * ⌜x.1⌝ₜ.size + 300, fun x => 12 * ⌜x⌝ₜ.size + 20⟩ := by
  refine Realizes.mono (by source_fun_prop) ?_
  rintro ⟨⟨n, c⟩, acc⟩
  cases c with
  | outputs select => simp; omega
  | @gate _ _ k op args next =>
    have hn := length_le_codeSize n.bits
    have hs := size_encode_nat_succ_le n
    have ha := accumulateGate_realizes.size_le (acc, ⟨k, op, Fin.val ∘ args, n⟩)
    simp at *
    omega

/-- Whether the circuit still has a gate to process. -/
def circuitContinues (input : (Σ n, Circuit .booleanAlgebra n 1) × CNF ℕ) : Bool :=
  match input.1.2 with
  | .outputs _ => false
  | .gate _ _ _ => true

theorem circuitContinues_realizes :
    Realizes circuitContinues ⟨fun _ => 6, fun x => ⌜x⌝ₜ.size⟩ := by
  source_cases

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
      tseitinLoop (circuitStep x).1 (circuitStep x).2 else circuitClausesStep x := by
  rcases x with ⟨⟨n, c⟩, acc⟩
  cases c <;> simp [circuitContinues, circuitStep, circuitClausesStep, tseitinLoop]

theorem tseitinLoop_realizes :
    Realizes (fun x : (Σ n, Circuit .booleanAlgebra n 1) × CNF ℕ => tseitinLoop x.1 x.2)
      ⟨fun x => 2000 * ⌜x⌝ₜ.size ^ 2, fun x => 140 * ⌜x⌝ₜ.size ^ 2⟩ := by
  let I (x y : (Σ n, Circuit .booleanAlgebra n 1) × CNF ℕ) :=
    ⌜y.1⌝ₜ.size ≤ ⌜x.1⌝ₜ.size ∧ tseitinLoop y.1 y.2 = tseitinLoop x.1 x.2
  have stateSize (x y) (hi : I x y) : ⌜y⌝ₜ.size ≤ 10 * ⌜x⌝ₜ.size ^ 2 := by
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
  apply (Realizes.loop circuitContinues_realizes circuitStep_realizes circuitClausesStep_realizes
    (fun x => ⌜x.1⌝ₜ.size) I
    (fun x => 28 * ⌜x.1⌝ₜ.size + 300)
    (fun x => 130 * ⌜x⌝ₜ.size ^ 2 + 300)
    (fun x => 120 * ⌜x⌝ₜ.size ^ 2 + 20) ?_ ?_ ?_ ?_ ?_).mono
  · rintro ⟨input, acc⟩
    dsimp only
    have hn := Tree.size_pos ⌜(input, acc)⌝ₜ
    have hf : ⌜input⌝ₜ.size ≤ ⌜(input, acc)⌝ₜ.size := by simp; omega
    have hn2 := Nat.le_self_pow (by decide : 2 ≠ 0) ⌜(input, acc)⌝ₜ.size
    constructor <;> nlinarith [pow_le_pow_left' hf 2]
  · intro x; exact ⟨le_rfl, rfl⟩
  · intro x y hi; have := stateSize x y hi; omega
  · intro x y hi
    have := stateSize x y hi
    dsimp only
    constructor <;> omega
  · rintro x ⟨⟨n, c⟩, acc⟩ hi htrue
    cases c with
    | outputs select => simp [circuitContinues] at htrue
    | @gate _ _ k op args next =>
      have hn := size_encode_nat_succ_le n
      have hm : ⌜(⟨n + 1, next⟩ : Σ n, Circuit .booleanAlgebra n 1)⌝ₜ.size <
          ⌜(⟨n, .gate op args next⟩ : Σ n, Circuit .booleanAlgebra n 1)⌝ₜ.size := by
        simp only [Sigma.encode_mk, size_encode_prod, Circuit.encode_gate] at *
        simp only [size_encode_unit] at *
        omega
      have hstate := stateSize x (⟨n, .gate op args next⟩, acc) hi
      refine ⟨?_, ?_, ⟨?_, ?_⟩, hm⟩
      · exact Nat.add_le_add_right (Nat.mul_le_mul_left 28 hi.1) _
      · dsimp only; omega
      · exact (Nat.le_of_lt hm).trans hi.1
      · simpa only [htrue, ↓reduceIte] using
          (tseitinLoop_step (⟨n, .gate op args next⟩, acc)).symm.trans hi.2
  · intro x y hi hfalse
    have := stateSize x y hi
    refine ⟨by dsimp only; omega, by dsimp only; omega, ?_⟩
    simpa only [hfalse, Bool.false_eq_true, ↓reduceIte] using (tseitinLoop_step y).symm.trans hi.2

@[local fun_prop, source_bounds↓] private noncomputable def tseitinLoopImplementation :=
  tseitinLoop_realizes.implementation

@[local source] theorem tseitin_source :
    (fun input : Σ n, Circuit .booleanAlgebra n 1 => input.2.tseitin) =
      (fun input => tseitinLoop input []) := (funext tseitinLoop_nil).symm

theorem tseitin_realizes :
    Realizes (fun input : Σ n, Circuit .booleanAlgebra n 1 => input.2.tseitin)
      ⟨fun x => 20000 * ⌜x⌝ₜ.size ^ 2, fun x => 2000 * ⌜x⌝ₜ.size ^ 2⟩ := by
  refine Realizes.mono (by source_fun_prop) ?_
  intro input
  have hn := Tree.size_pos ⌜input⌝ₜ
  simp only [compBounds_time, pairBounds_time, zero_add, size_encode_prod,
    encode_list_nil, size_encode_unit, compBounds_peak, pairBounds_peak, zero_le, sup_of_le_right,
    sup_le_iff, Order.add_one_le_iff]
  (repeat' apply And.intro) <;> nlinarith

theorem _root_.Complexity.Circuit.tseitin_model :
    ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace
      (fun input : Σ n, Circuit .booleanAlgebra n 1 => input.2.tseitin)
      (fun n => 20000 * n ^ 2 + 4) (fun n => k * (2000 * n ^ 2 + 2)) := by
  apply tseitin_realizes.computableInTimeAndSpace
  intro input
  have := Nat.le_self_pow (by decide : 2 ≠ 0) ⌜input⌝ₜ.size
  simp
  omega

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


end Complexity.TreeProgram.Source
