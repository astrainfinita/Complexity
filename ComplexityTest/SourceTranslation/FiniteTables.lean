/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Complexity.Tactic.TreeProgram.Library
import Complexity.Models.Circuit.TreeEncoding
import Complexity.ModelTheory.Algebra.BooleanAlgebra.TreeEncoding
import Complexity.Classes.Functions.Basic

open Complexity TreeProgram Complexity.TreeProgram.Source

namespace ComplexityTest.SourceTranslation.FiniteTables

example : ∃ b, Realizes (fun n : ℕ => List.ofFn (fun i : Fin n => i.val + 1)) b :=
  ⟨_, by source_fun_prop⟩

-- Reading a stored tuple stays a projection; generation is only a fallback.
example {α : Type*} [UniqueEncoding Tree α] :
    ∃ b, Realizes (fun x : Σ n, Fin n → α => List.ofFn x.2) b ∧
      ∀ x, b.time x = 1 := by
  refine ⟨_, by source_fun_prop, ?_⟩
  simp

def identityWires (n : ℕ) : Σ n, Fin n → Fin n := ⟨n, id⟩

example : ∃ b, Realizes identityWires b := ⟨_, by source_fun_prop⟩

def appendEntry (x : Σ n, (Fin n → ℕ) × ℕ) : Σ n, Fin n → ℕ :=
  ⟨x.1 + 1, Fin.snoc x.2.1 x.2.2⟩

example : ∃ b, Realizes appendEntry b := ⟨_, by source_fun_prop⟩

def appendWire (x : Σ n, Σ m, (Fin n → Fin m) × Fin m) : Σ n, Σ m, Fin n → Fin m :=
  ⟨x.1 + 1, x.2.1, Fin.snoc x.2.2.1 x.2.2.2⟩

example : ∃ b, Realizes appendWire b := ⟨_, by source_fun_prop⟩

def appendTables (x : Σ n, Σ m, (Fin n → ℕ) × (Fin m → ℕ)) : Σ n, Fin n → ℕ :=
  ⟨x.1 + x.2.1, Fin.append x.2.2.1 x.2.2.2⟩

example : ∃ b, Realizes appendTables b := ⟨_, by source_fun_prop⟩

example : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace appendTables
    (fun n => 10000 * n + 20000) (fun n => k * (1000 * n + 5000)) := by
  model_fun_prop
  all_goals
    rename_i x
    rcases x with ⟨n, m, f, g⟩
    have hn := card_le_size_encode_fin_function f
    have hm := card_le_size_encode_fin_function g
    have ha := size_encode_nat_le (n + m)
    have happ := size_encode_list_append (List.ofFn f) (List.ofFn g)
    simp only [Sigma.encode_mk, encode_prod, Tree.size_pair,
      encode_fin_function, encode_nat_tree] at hn hm ha happ ⊢
    omega

def shiftWire (x : ℕ × (Σ n, Fin n)) := (Fin.natAdd x.1 x.2.2).val

example : ∃ b, Realizes shiftWire b := ⟨_, by source_fun_prop⟩

-- Only the first table is traversed; a stored second table is not regenerated.
example {α : Type*} [UniqueEncoding Tree α] :
    ∃ b, Realizes (fun x : Σ n, Σ m, (Fin n → α) × (Fin m → α) =>
      ⌜Fin.append x.2.2.1 x.2.2.2⌝ₜ) b ∧
      ∀ x, b.time x = 26 * x.1 + 22 := by
  refine ⟨_, by source_fun_prop, ?_⟩
  simp
  omega

def successorWires (n : ℕ) : Σ n, Fin n → Fin (n + 1) := ⟨n, Fin.castSucc⟩

example : ∃ b, Realizes successorWires b := ⟨_, by source_fun_prop⟩

-- A change of index bound keeps the stored table; it is not pointwise table generation.
example : ∃ b, Realizes (fun x : Σ n, Σ k, Fin n → Fin k =>
    ⌜Fin.castSucc ∘ x.2.2⌝ₜ) b ∧ ∀ x, b.time x = 2 := by
  refine ⟨_, by source_fun_prop, ?_⟩
  simp

def identityCircuit (n : ℕ) : Σ n, Circuit .booleanAlgebra n n := ⟨n, .id _ n⟩

example : ∃ b, Realizes identityCircuit b := ⟨_, by source_fun_prop⟩

def positions {α : Type*} (xs : List α) : List ℕ := List.ofFn (fun i : Fin xs.length => i.val)

theorem positions_model {α : Type*} [UniqueEncoding Tree α] :
    ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace (positions (α := α))
      (fun n => 100000 * (n + 1) ^ 2) (fun n => k * (10000 * (n + 1) ^ 2)) := by
  model_fun_prop
  all_goals
    rename_i xs
    have hl := length_le_codeSize xs
    have hp := pow_le_pow_left' (Nat.add_le_add_right hl 1) 2
    have hN := Nat.le_self_pow (by decide : 2 ≠ 0) (⌜xs⌝ₜ.size + 1)
  · omega
  · have hr := size_encode_range_le xs.length
    have hm : (List.finRange xs.length).foldr
        (fun i s => max (1 + ⌜xs⌝ₜ.size + ⌜i.val⌝ₜ.size) s) 0 ≤
          ⌜xs⌝ₜ.size + 4 * xs.length + 2 := by
      apply (foldr_max_le _ _ _).mpr
      intro i _
      have := size_encode_nat_le i.val
      have := i.isLt
      omega
    simp only [List.ofFn_eq_map, List.map_coe_finRange_eq_range, encode_nat_tree] at hm ⊢
    omega

-- Ordinary constructors retain runtime dimensions and wire types.
def complementLayer (xs : List Unit) : List (Σ n, Circuit .booleanAlgebra n 1) :=
  let n := xs.length
  List.ofFn (fun i : Fin n =>
    ⟨n, .ofGate FirstOrder.BooleanAlgebra.complFunc (fun _ => i)⟩)

theorem complementLayer_model :
    ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace complementLayer
      (fun n => 100000 * (n + 1) ^ 2) (fun n => k * (10000 * (n + 1) ^ 2)) := by
  model_fun_prop
  all_goals
    rename_i xs
    have hl := length_le_codeSize xs
    have hp := pow_le_pow_left' (Nat.add_le_add_right hl 1) 2
    have hN := Nat.le_self_pow (by decide : 2 ≠ 0) (⌜xs⌝ₜ.size + 1)
  · omega
  · have hn := size_encode_nat_le xs.length
    have hr := size_encode_range_le xs.length
    let gate (i : Fin xs.length) : Σ n, Circuit .booleanAlgebra n 1 :=
      ⟨xs.length, .ofGate FirstOrder.BooleanAlgebra.complFunc (fun _ => i)⟩
    have hc (i : Fin xs.length) : ⌜gate i⌝ₜ.size ≤ 12 * xs.length + 40 := by
      have hi := size_encode_nat_le i.val
      have := i.isLt
      simp [gate, Circuit.ofGate] at hn hi ⊢
      omega
    have hout : ⌜List.ofFn gate⌝ₜ.size ≤ 50 * (xs.length + 1) ^ 2 := by
      have h := size_encode_fin_function_le gate (12 * xs.length + 40) hc
      simp only [encode_fin_function] at h
      nlinarith
    have hm := (foldr_max_le (fun i => ⌜gate i⌝ₜ.size) (List.finRange xs.length)
      (12 * xs.length + 40)).mpr (fun i _ => hc i)
    simp [gate, Circuit.ofGate, -foldr_max_le] at hm hn
    simp only [gate, Circuit.ofGate] at hout
    simp (disch := omega) [Circuit.ofGate]
    omega

-- Two dependent table lookups compose inside a newly generated table.
def composeWires (x : Σ n, Σ k, Σ m, (Fin n → Fin k) × (Fin k → Fin m)) :
    Σ n, Σ m, Fin n → Fin m := ⟨x.1, x.2.2.1, x.2.2.2.2 ∘ x.2.2.2.1⟩

example : ∃ b, Realizes composeWires b := ⟨_, by source_fun_prop⟩

attribute [local fun_prop] Realizes.finComp in
theorem composeWires_model :
    ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace composeWires
      (fun n => 1000000 * (n + 1) ^ 3) (fun n => k * (1000000 * (n + 1) ^ 2)) := by
  model_fun_prop
  all_goals
    rename_i x
    have h₂ := Nat.le_self_pow (by decide : 2 ≠ 0) (⌜x⌝ₜ.size + 1)
    have h₃ := Nat.le_self_pow (by decide : 3 ≠ 0) (⌜x⌝ₜ.size + 1)
    rcases x with ⟨n, k, m, f, g⟩
    let N := ⌜(n, k, m, f, g)⌝ₜ.size
    have hf : ⌜f⌝ₜ.size ≤ N := by simp only [N, size_encode_prod]; omega
    have hg : ⌜g⌝ₜ.size ≤ N := by simp only [N, size_encode_prod]; omega
    have ho : ⌜g ∘ f⌝ₜ.size ≤ (N + 1) ^ 2 :=
      (size_encode_fin_comp_le f g).trans
        ((Nat.add_le_add_right (Nat.mul_le_mul hf (Nat.add_le_add_right hg 1)) 1).trans
          (by simp only [pow_two, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]; omega))
    dsimp only [N] at ho
    simp at h₂ h₃ ho ⊢
    omega

theorem composeWires_ftisp :
    composeWires ∈ FTISP .tree (fun n => n ^ 3) (fun n => n ^ 2) := by
  obtain ⟨k, hk⟩ := composeWires_model
  exact ⟨_, _, hk, IsBigO.of_le_mul_add_one_pow 1000000 3 (fun _ => le_rfl),
    IsBigO.of_le_mul_add_one_pow (k * 1000000) 2 (fun _ => by simp only [Nat.mul_assoc, le_refl])⟩

-- A represented table and a single callback implement one algorithm for every runtime index.
-- Pointwise existence must not be mistaken for such a callback.
example (f : ℕ → ℕ → Bool) (b : ℕ → Bounds ℕ)
    (_hf : ∀ n, Realizes (f n) (b n)) : True := by
  fail_if_success
    have : ∃ c, Realizes (fun n => List.ofFn (fun i : Fin n => f n i.val)) c :=
      ⟨_, by source_fun_prop⟩
  trivial

end ComplexityTest.SourceTranslation.FiniteTables
