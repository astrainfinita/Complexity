/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Tactic.TreeProgram.Library
public import Complexity.Tactic.TreeProgram.Recursion
public import Complexity.Models.Circuit.TreeEncoding
public import Complexity.ModelTheory.Algebra.BooleanAlgebra.TreeEncoding
public import Complexity.Models.Circuit.Composition

/-! # Certified circuit relabeling and composition

The descriptors retain the dependent source types. Every callback is translated by the common
source mechanism; the recursion backend supplies the stack and its resource certificate.
-/

@[expose] public section

open Complexity TreeProgram

namespace Complexity.Circuit

/-- A numeric bound on Boolean-circuit encoding size, including every stored wire. -/
theorem size_encode_numeric_le {n m : ℕ} (c : Circuit .booleanAlgebra n m) :
    ⌜c⌝ₜ.size ≤ 100 * (c.size + m + 1) * (n + c.size + 1) := by
  induction c with
  | @outputs n m select =>
    have hs := size_encode_fin_function_le select (4 * n + 1) (fun i => by
      have := size_encode_nat_le (select i).val
      have := (select i).isLt
      simpa only [encode_fin] using (by omega : ⌜(select i).val⌝ₜ.size ≤ 4 * n + 1))
    simp only [encode_outputs, size_encode_prod, size_encode_unit, size_outputs] at *
    nlinarith
  | @gate n m k op args next ih =>
    have hk : k ≤ 2 := by cases op <;> decide
    have ho : ⌜op⌝ₜ.size ≤ 11 := by cases op <;> simp [encode_unit]
    have ha := size_encode_fin_function_le args (4 * n + 1) (fun i => by
      have := size_encode_nat_le (args i).val
      have := (args i).isLt
      simpa only [encode_fin] using (by omega : ⌜(args i).val⌝ₜ.size ≤ 4 * n + 1))
    have hargs : ⌜args⌝ₜ.size ≤ 8 * n + 5 := by nlinarith
    have hk' := size_encode_nat_le k
    simp only [encode_gate, size_encode_prod, size_encode_unit, size_gate]
    nlinarith

/-- Adding the new input wire retains the old table and stores one additional index. -/
theorem size_encode_liftInputs {n k : ℕ} (wires : Fin n → Fin k) :
    ⌜liftInputs wires⌝ₜ.size = ⌜wires⌝ₜ.size + ⌜k⌝ₜ.size + 1 := by
  have ha := size_encode_list_append (List.ofFn (Fin.castSucc ∘ wires)) [Fin.last k]
  simp only [← encode_fin_function, encode_fin_castSucc, encode_list_cons, encode_list_nil,
    size_encode_prod, size_encode_unit, encode_fin, Fin.val_last] at ha
  simpa only [liftInputs, Function.comp_def, encode_fin_snoc] using (by omega :
    ⌜List.ofFn (Fin.castSucc ∘ wires) ++ [Fin.last k]⌝ₜ.size = ⌜wires⌝ₜ.size + ⌜k⌝ₜ.size + 1)

end Complexity.Circuit

namespace Complexity

theorem Dominated.size_encode_circuit {α : Type*} {n m R : α → ℕ}
    (c : (x : α) → Circuit .booleanAlgebra (n x) (m x))
    (hn : Dominated n R) (hm : Dominated m R)
    (hc : Dominated (fun x => (c x).size) R) (hR : ∀ x, 0 < R x) :
    Dominated (fun x => ⌜c x⌝ₜ.size) (fun x => R x ^ 2) := by
  have h := ((hc.add_same hm).add_same (Dominated.one hR)).mul
    ((hn.add_same hc).add_same (Dominated.one hR))
  simpa only [pow_two, Nat.mul_assoc] using (h.const_mul_left 100).mono_left
    (fun x => by simpa only [Nat.mul_assoc] using (c x).size_encode_numeric_le)

end Complexity

namespace Complexity.TreeProgram.Source

private theorem dominated_one_pow {α : Type*} (R : α → ℕ) (hR : ∀ x, 0 < R x) (d : ℕ) :
    Dominated (fun _ => 1) (fun x => R x ^ d) :=
  Dominated.one fun x => Nat.pow_pos (hR x)

private theorem dominated_pow_pow_of_le {α : Type*} (R : α → ℕ) (hR : ∀ x, 0 < R x)
    {d e : ℕ} (h : d ≤ e) : Dominated (fun x => R x ^ d) (fun x => R x ^ e) :=
  Dominated.of_le fun x => Nat.pow_le_pow_right (hR x) h

abbrev RelabelInput := Σ n, Σ m, Σ k, Circuit .booleanAlgebra n m × (Fin n → Fin k)
def relabelFn (x : RelabelInput) := x.2.2.2.1.relabel x.2.2.2.2

def relabelTest (x : RelabelInput) :=
  match x.2.2.2.1 with | .outputs _ => false | .gate _ _ _ => true

def relabelNextFn : RelabelInput → RelabelInput
  | ⟨n, m, k, .gate _ _ next, wires⟩ => ⟨n + 1, m, k + 1, next, Circuit.liftInputs wires⟩
  | x => x

def relabelFinishFn : (x : {x // relabelTest x = false}) →
    Circuit .booleanAlgebra x.1.2.2.1 x.1.2.1
  | ⟨⟨_, _, _, .outputs select, wires⟩, _⟩ => .outputs (wires ∘ select)
  | ⟨⟨_, _, _, .gate _ _ _, _⟩, h⟩ => False.elim (by cases h)

def relabelResumeFn : (x : {x // relabelTest x = true}) →
    Circuit .booleanAlgebra (relabelNextFn x.1).2.2.1 (relabelNextFn x.1).2.1 →
    Circuit .booleanAlgebra x.1.2.2.1 x.1.2.1
  | ⟨⟨_, _, _, .outputs _, _⟩, h⟩, _ => False.elim (by cases h)
  | ⟨⟨_, _, _, .gate op args _, wires⟩, _⟩, result => .gate op (wires ∘ args) result

def relabelRecursion : Recursion relabelFn where
  test := relabelTest
  next := relabelNextFn
  finish := relabelFinishFn
  resume := relabelResumeFn
  finish_eq := by
    rintro ⟨⟨n, m, k, c, wires⟩, h⟩
    cases c <;> dsimp [relabelTest] at h ⊢ <;> first | contradiction | rfl
  resume_eq := by
    rintro ⟨⟨n, m, k, c, wires⟩, h⟩
    cases c <;> dsimp [relabelTest] at h ⊢ <;> first | contradiction | rfl
  measure x := x.2.2.2.1.size
  decreases := by
    rintro ⟨n, m, k, c, wires⟩ h
    cases c <;> simp_all [relabelTest, relabelNextFn]

noncomputable def relabelCheck : Implementation relabelTest := by source_fun_prop

noncomputable def relabelNext : Implementation relabelNextFn := by source_fun_prop

attribute [local fun_prop] Implementation.finComp in
noncomputable def relabelFinish : Implementation (fun x => ⌜relabelFinishFn x⌝ₜ) := by
  source_fun_prop

abbrev RelabelGateInput := Σ n, Σ m, Σ k, Σ arity,
  FirstOrder.Language.booleanAlgebra.Functions arity × (Fin arity → Fin n) ×
    (Fin n → Fin k) × Circuit .booleanAlgebra (k + 1) m

def relabelGateFn (x : RelabelGateInput) : Tree :=
  ⌜Circuit.gate x.2.2.2.2.1 (x.2.2.2.2.2.2.1 ∘ x.2.2.2.2.2.1) x.2.2.2.2.2.2.2⌝ₜ

attribute [local fun_prop] Implementation.finComp in
noncomputable def relabelGateImplementation : Implementation relabelGateFn := by source_fun_prop

@[source_growth] theorem relabelGate_growth : relabelGateImplementation.HasGrowth
    (fun x => ⌜x⌝ₜ.size ^ 3) (fun x => ⌜x⌝ₜ.size ^ 2) := by
  let N (x : RelabelGateInput) := ⌜x⌝ₜ.size
  have hN x : 0 < N x := Tree.size_pos _
  let u (x : RelabelGateInput) : Σ a, Σ n, Σ k, (Fin a → Fin n) × (Fin n → Fin k) :=
    ⟨x.2.2.2.1, x.1, x.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1⟩
  have hu : Dominated (fun x => ⌜u x⌝ₜ.size) N := Dominated.of_le fun x => by
    rcases x with ⟨n, m, k, a, op, args, wires, result⟩
    simp only [u, N, Sigma.encode_mk, size_encode_prod]
    omega
  have ht := hu.pow 3
  have hp := hu.pow 2
  have hout := (Dominated.comp finComp_growth.size_encode u).trans
    ((hu.le_pow (by decide : 0 < 2)).max_same (hu.pow 2))
  source_fun_prop
  all_goals
    change Dominated _ (fun x => N x ^ _)
    simp only [Function.comp_apply, Dominated.add_iff, Dominated.max_iff,
      Tree.encode_self, Sigma.encode_mk, size_encode_prod]
    repeat' apply And.intro
  all_goals with_reducible first
    | simpa only [Function.comp_def, u, Sigma.encode_mk, size_encode_prod] using ht
    | simpa only [Function.comp_def, u, Sigma.encode_mk, size_encode_prod] using hp
    | simpa only [Function.comp_def, u, Tree.encode_self] using hout
    | exact Dominated.const_of_pos _ (fun x => Nat.pow_pos (hN x))
    | apply Dominated.le_pow (g := N) _ (by decide)
      apply Dominated.of_le
      rintro ⟨n, m, k, a, op, args, wires, result⟩
      simp only [N, Sigma.encode_mk, size_encode_prod]
      omega

def relabelResumeInput : relabelRecursion.Return → RelabelGateInput
  | ⟨⟨⟨_, _, _, .outputs _, _⟩, h⟩, _⟩ => False.elim (by cases h)
  | ⟨⟨⟨n, m, k, .gate (k := a) op args _, wires⟩, _⟩, result⟩ =>
      ⟨n, m, k, a, op, args, wires, result⟩

noncomputable def relabelResumeInputImplementation : Implementation relabelResumeInput := by
  source_fun_prop

@[source_growth] theorem relabelResumeInput_growth :
    relabelResumeInputImplementation.HasGrowth (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  let Input := Σ n, Σ m, Σ k, Σ a, FirstOrder.Language.booleanAlgebra.Functions a ×
    (Fin a → Fin n) × Circuit .booleanAlgebra (n + 1) m ×
      (Fin n → Fin k) × Circuit .booleanAlgebra (k + 1) m
  let input (x : Input) : relabelRecursion.Return :=
    ⟨⟨⟨x.1, x.2.1, x.2.2.1,
      .gate x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1⟩, rfl⟩,
      x.2.2.2.2.2.2.2.2⟩
  have cover : Function.Surjective input := by
    rintro ⟨⟨⟨n, m, k, c, w⟩, h⟩, result⟩
    cases c with
    | outputs _ => cases h
    | gate op args next => exact ⟨⟨n, m, k, _, op, args, next, w, result⟩, rfl⟩
  have hcode (x : relabelRecursion.Return) : ⌜x⌝ₜ.size =
      1 + ⌜x.1.1⌝ₜ.size + ⌜x.2⌝ₜ.size := by rcases x with ⟨x, result⟩; rfl
  source_fun_prop
  all_goals
    apply Dominated.of_comp_surjective input cover
    dsimp only [Function.comp_def, input]
  · exact Dominated.const _
  · apply Dominated.of_le
    intro x
    simp only [hcode]
    dsimp +instances only [id, Recursion.Return, relabelRecursion, relabelNextFn]
    simp only [ Sigma.encode_mk, UniqueEncoding.encode_subtype, Circuit.encode_gate,
      size_encode_prod, size_encode_unit, max_le_iff]
    omega

noncomputable def relabelResume : Implementation
    (fun x : relabelRecursion.Return => ⌜relabelResumeFn x.1 x.2⌝ₜ) :=
  (relabelResumeInputImplementation.comp relabelGateImplementation).congr (by
    funext ⟨⟨⟨n, m, k, c, w⟩, h⟩, result⟩
    cases c with
    | outputs _ => cases h
    | gate _ _ _ => rfl)

noncomputable def relabelImplementation : Implementation (fun x => ⌜relabelFn x⌝ₜ) :=
  relabelRecursion.implementation relabelCheck relabelNext relabelFinish relabelResume
theorem relabel_input_size_le (n m k : ℕ) (c : Circuit .booleanAlgebra n m)
    (w : Fin n → Fin k) (N : ℕ) (h : n + m + k + 2 * c.size ≤ N) :
    ⌜(⟨n, m, k, c, w⟩ : RelabelInput)⌝ₜ.size ≤ 128 * (N + 1) ^ 2 := by
  have hc := c.size_encode_numeric_le
  have hcp : (c.size + m + 1) * (n + c.size + 1) ≤ (N + 1) ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul (by omega : c.size + m + 1 ≤ N + 1)
      (by omega : n + c.size + 1 ≤ N + 1)
  have hw := size_encode_fin_function_le w (4 * k + 1) (fun i => by
    have := size_encode_nat_le (w i).val
    have := (w i).isLt
    simpa only [encode_fin] using (by omega : ⌜(w i).val⌝ₜ.size ≤ 4 * k + 1))
  have hwp := Nat.mul_le_mul (by omega : n ≤ N + 1) (by omega : 4 * k + 1 + 1 ≤ 6 * (N + 1))
  have hn := size_encode_nat_le n
  have hm := size_encode_nat_le m
  have hk := size_encode_nat_le k
  simp only [Sigma.encode_mk, size_encode_prod]
  nlinarith

def relabelScale (x : RelabelInput) : ℕ :=
  x.1 + x.2.1 + x.2.2.1 + 2 * x.2.2.2.1.size + 1

theorem relabelScale_pos (x : RelabelInput) : 0 < relabelScale x := Nat.succ_pos _

theorem relabelScale_next_le (x : RelabelInput) :
    relabelScale (relabelNextFn x) ≤ relabelScale x := by
  rcases x with ⟨n, m, k, c, w⟩
  cases c <;>
    simp -implicitDefEqProofs only [relabelNextFn, relabelScale, Circuit.size_gate] <;> omega

theorem size_encode_relabelFn_le (x : RelabelInput) :
    ⌜relabelFn x⌝ₜ.size ≤ 100 * relabelScale x ^ 2 := by
  rcases x with ⟨n, m, k, c, w⟩
  have h := (c.relabel w).size_encode_numeric_le
  simp -implicitDefEqProofs only [Circuit.size_relabel] at h
  apply h.trans
  simpa -implicitDefEqProofs only [pow_two, Nat.mul_assoc] using Nat.mul_le_mul
    (Nat.mul_le_mul_left 100
      (by dsimp [relabelScale]; omega : c.size + m + 1 ≤ relabelScale ⟨n, m, k, c, w⟩))
    (by dsimp [relabelScale]; omega : k + c.size + 1 ≤ relabelScale ⟨n, m, k, c, w⟩)

@[source_growth] theorem relabelCheck_growth : relabelCheck.HasGrowth
    (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  · exact Dominated.const_of_pos _ (fun _ => Nat.zero_lt_one)
  · apply Dominated.of_le
    rintro ⟨n, m, k, c, w⟩
    cases c <;> simp <;> omega

@[source_growth] theorem relabelNext_growth : relabelNext.HasGrowth
    (fun x => ⌜x⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) := by
  have hcast {n k : ℕ} (wires : Fin n → Fin k) :
      ⌜fun i => (wires i).castSucc⌝ₜ = ⌜wires⌝ₜ := by
    simpa only [Function.comp_def] using encode_fin_castSucc wires
  have hcodes {n k : ℕ} (wires : Fin n → Fin k) :
      ⌜List.ofFn (fun i => ⌜(wires i).val⌝ₜ)⌝ₜ = ⌜wires⌝ₜ := by
    simpa only [encode_fin] using encode_fin_function_codes wires
  let output (x : Σ n, Σ m, Σ k, (Fin m → Fin n) × (Fin n → Fin k)) : RelabelInput :=
    ⟨x.1, x.2.1, x.2.2.1, .outputs x.2.2.2.1, x.2.2.2.2⟩
  let gate (x : Σ n, Σ m, Σ k, Σ a, FirstOrder.Language.booleanAlgebra.Functions a ×
      (Fin a → Fin n) × Circuit .booleanAlgebra (n + 1) m × (Fin n → Fin k)) : RelabelInput :=
    ⟨x.1, x.2.1, x.2.2.1, .gate x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2⟩
  have cover x : (∃ y, output y = x) ∨ ∃ y, gate y = x := by
    rcases x with ⟨n, m, k, c, d⟩
    cases c with
    | outputs w => exact Or.inl ⟨⟨n, m, k, w, d⟩, rfl⟩
    | gate op args next => exact Or.inr ⟨⟨n, m, k, _, op, args, next, d⟩, rfl⟩
  source_fun_prop
  all_goals
    apply Dominated.of_cover output gate cover
    all_goals
      dsimp only [Function.comp_def, output, gate]
      try source_fun_prop
      simp only [Function.comp_apply, Dominated.add_iff, Dominated.max_iff,
        Dominated.const_mul_left_iff, Nat.ofNat_pos,
        Tree.encode_self, Sigma.encode_mk, size_encode_prod, Circuit.encode_gate,
        Circuit.encode_outputs, size_encode_unit, Circuit.size_encode_liftInputs,
        encode_fin, Fin.val_last, Fin.val_castSucc, hcast, hcodes, List.length_ofFn,
        encode_list_cons, encode_list_nil, and_self]
      repeat' apply And.intro
  all_goals with_reducible first
    | exact Dominated.const_of_pos _ (fun _ => Tree.size_pos _)
    | exact Dominated.const_of_pos _ (fun _ => by omega)
    | apply Dominated.of_le
      rintro ⟨n, m, k, w, d⟩
      omega
    | apply Dominated.of_le_mul 10
      rintro ⟨n, m, k, a, op, args, next, wires⟩
      have hn := card_le_size_encode_fin_function wires
      have hs := size_encode_nat_succ_le n
      have hs' := size_encode_nat_succ_le k
      dsimp only
      omega

@[source_growth] theorem relabelFinish_growth : relabelFinish.HasGrowth
    (fun x => ⌜x⌝ₜ.size ^ 3) (fun x => ⌜x⌝ₜ.size ^ 2) := by
  let input (x : Σ n, Σ m, Σ k, (Fin n → Fin k) × (Fin m → Fin n)) :
      {x // relabelTest x = false} :=
    ⟨⟨x.1, x.2.1, x.2.2.1, .outputs x.2.2.2.2, x.2.2.2.1⟩, rfl⟩
  have hi : Function.Surjective input := by
    rintro ⟨⟨n, m, k, c, w⟩, h⟩
    cases c with
    | outputs s => exact ⟨⟨n, m, k, w, s⟩, rfl⟩
    | gate op args next => cases h
  let N x := ⌜input x⌝ₜ.size
  let u (x : Σ n, Σ m, Σ k, (Fin n → Fin k) × (Fin m → Fin n)) :=
    (⟨x.2.1, x.1, x.2.2.1, x.2.2.2.2, x.2.2.2.1⟩ :
      Σ n, Σ k, Σ m, (Fin n → Fin k) × (Fin k → Fin m))
  have hN x : 0 < N x := Tree.size_pos _
  have hu : Dominated (fun x => ⌜u x⌝ₜ.size) N := Dominated.of_le fun x => by
    simp only [u, N, input, UniqueEncoding.encode_subtype, Sigma.encode_mk,
      Circuit.encode_outputs, size_encode_prod, size_encode_unit]
    omega
  have hout := (Dominated.comp finComp_growth.size_encode u).trans
    ((hu.le_pow (by decide : 0 < 2)).max_same (hu.pow 2))
  have ht := (Dominated.comp finComp_growth.1 u).trans (hu.pow 3)
  have hp := (Dominated.comp finComp_growth.2 u).trans (hu.pow 2)
  have hsize := (Dominated.refl N).le_pow (by decide : 0 < 2)
  source_fun_prop
  all_goals
    apply Dominated.of_comp_surjective input hi
    dsimp only [Function.comp_def, input]
    change Dominated _ (fun x => N x ^ _)
    simp only [size_encode_prod, size_encode_unit, Tree.encode_self,
      Dominated.add_iff, Dominated.max_iff,
      Dominated.const_of_pos _ (fun x => Nat.pow_pos (hN x)), true_and, and_true]
    (repeat' apply And.intro) <;> first
      | with_reducible simpa only [Function.comp_def, u] using ht
      | with_reducible simpa only [Function.comp_def, u] using hp
      | with_reducible simpa only [Tree.encode_self, Function.comp_def, u] using hout
      | with_reducible exact hsize
      | apply Dominated.le_pow (e := 2) _ (by decide)
        apply Dominated.of_le
        intro x
        simp only [N, input, UniqueEncoding.encode_subtype, Sigma.encode_mk,
          Circuit.encode_outputs, size_encode_prod, size_encode_unit]
        omega

@[source_growth] theorem relabelResume_growth : relabelResume.HasGrowth
    (fun x => ⌜x⌝ₜ.size ^ 3) (fun x => ⌜x⌝ₜ.size ^ 2) := by
  have hsize := relabelResumeInput_growth.size_encode
  simp only [max_self] at hsize
  source_fun_prop
  · simp only [Dominated.add_iff]
    exact ⟨Dominated.const_of_pos _ (fun _ => Nat.pow_pos (Tree.size_pos _)), hsize.pow 3⟩
  · simp only [Dominated.max_iff]
    exact ⟨(Dominated.refl _).le_pow (by decide), hsize.pow 2⟩

/-- Callback scales and the invariant suffice; the recursion rule handles branch accounting. -/
theorem relabel_cost_growth :
    let bc : Bounds RelabelInput := ⟨fun _ => 1, fun x => ⌜x⌝ₜ.size⟩
    let bs : Bounds RelabelInput := ⟨fun x => ⌜x⌝ₜ.size, fun x => ⌜x⌝ₜ.size⟩
    let bd : Bounds {x // relabelRecursion.test x = false} :=
      ⟨fun x => ⌜x⌝ₜ.size ^ 3, fun x => ⌜x⌝ₜ.size ^ 2⟩
    let br : Bounds relabelRecursion.Return :=
      ⟨fun x => ⌜x⌝ₜ.size ^ 3, fun x => ⌜x⌝ₜ.size ^ 2⟩
    Dominated (fun x => (relabelRecursion.cost bc bs bd br x).time)
      (fun x => x.2.2.2.1.size * relabelScale x ^ 6 + relabelScale x ^ 6) ∧
    Dominated (fun x => (relabelRecursion.cost bc bs bd br x).peak)
      (fun x => relabelScale x ^ 4 + (x.2.2.2.1.size + 1) * (relabelScale x ^ 2 + 1)) := by
  dsimp only
  let I (a x : RelabelInput) := relabelScale x ≤ relabelScale a
  let Z := {p : RelabelInput × RelabelInput // I p.1 p.2}
  let R (z : Z) := relabelScale z.1.1
  let s (z : Z) := ⌜z.1.2⌝ₜ.size
  let o (z : Z) := ⌜relabelFn (relabelNextFn z.1.2)⌝ₜ.size
  have hR (z : Z) : 0 < R z := relabelScale_pos _
  have hsize : Dominated s (fun z => R z ^ 2) := Dominated.of_le_mul 128 fun z => by
    rcases z with ⟨⟨a, ⟨n, m, k, c, w⟩⟩, hz⟩
    have h := relabel_input_size_le n m k c w (relabelScale a - 1)
      (by dsimp [I, relabelScale] at hz; dsimp [relabelScale]; omega)
    simpa -implicitDefEqProofs only [s, R, Nat.sub_add_cancel (relabelScale_pos a)] using h
  have hout : Dominated o (fun z => R z ^ 2) := Dominated.of_le_mul 100 fun z =>
    (size_encode_relabelFn_le _).trans (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_left ((relabelScale_next_le _).trans z.2) 2))
  let Step := {z : Z // relabelRecursion.test z.1.2 = true}
  let u (z : Step) : relabelRecursion.Return :=
    ⟨⟨z.1.1.2, z.2⟩, relabelFn (relabelNextFn z.1.1.2)⟩
  have hreturn : Dominated (fun z => ⌜u z⌝ₜ.size) (fun z : Step => R z.1 ^ 2) := by
    have eq : (fun z : Step => ⌜u z⌝ₜ.size) = (fun z => 1 + s z.1 + o z.1) := by
      funext z
      rfl
    rw [eq]
    exact Dominated.comp (((dominated_one_pow R hR 2).add_same hsize).add_same hout)
      Subtype.val
  have hfinishTime : Dominated (fun z => s z ^ 3) (fun z => R z ^ 6) := by
    simpa only [← pow_mul] using hsize.pow 3
  have hfinishPeak : Dominated (fun z => s z ^ 2) (fun z => R z ^ 4) := by
    simpa only [← pow_mul] using hsize.pow 2
  have hreturnTime : Dominated (fun z => ⌜u z⌝ₜ.size ^ 3) (fun z => R z.1 ^ 6) := by
    simpa only [← pow_mul] using hreturn.pow 3
  have hreturnPeak : Dominated (fun z => ⌜u z⌝ₜ.size ^ 2) (fun z => R z.1 ^ 4) := by
    simpa only [← pow_mul] using hreturn.pow 2
  refine relabelRecursion.dominated_cost_of_bounds _ _ _ _ I id
    (fun x => relabelScale x ^ 2) (fun x => relabelScale x ^ 6)
    (fun x => relabelScale x ^ 6) (fun x => relabelScale x ^ 4)
    (fun _ => le_rfl) (fun a x hx _ => (relabelScale_next_le x).trans hx) hsize
    (hsize.mono_pow (by decide) hR) (hsize.mono_pow (by decide) hR)
    (hfinishPeak.comp Subtype.val) hreturnPeak (hfinishTime.comp Subtype.val)
    (hsize.mono_pow (by decide) hR) (Dominated.const_of_pos 1 fun z => Nat.pow_pos (hR z))
    hreturnTime (fun _ => Nat.pow_pos (relabelScale_pos _))
    (fun _ => Nat.pow_pos (relabelScale_pos _))

theorem relabel_structural_growth : relabelImplementation.HasGrowth
    (fun x => 1 + (x.2.2.2.1.size * relabelScale x ^ 6 + relabelScale x ^ 6) + 1)
    (fun x => (relabelScale x ^ 4 + (x.2.2.2.1.size + 1) * (relabelScale x ^ 2 + 1)) + 1) :=
  relabelRecursion.hasGrowth_of_growth relabelCheck_growth relabelNext_growth
    relabelFinish_growth relabelResume_growth relabel_cost_growth

@[source_growth] theorem relabel_growth : relabelImplementation.HasGrowth
    (fun x => relabelScale x ^ 7) (fun x => relabelScale x ^ 4) := by
  have hg : Dominated (fun x : RelabelInput => x.2.2.2.1.size) relabelScale :=
    Dominated.of_le fun x => by dsimp [relabelScale]; omega
  have hg' := hg.add_same (Dominated.one relabelScale_pos)
  have ht : Dominated (fun x => x.2.2.2.1.size * relabelScale x ^ 6)
      (fun x => relabelScale x ^ 7) := by
    simpa -implicitDefEqProofs only [pow_succ, Nat.mul_comm] using
      hg.mul ((Dominated.refl relabelScale).pow 6)
  have hs : Dominated (fun x => (x.2.2.2.1.size + 1) * (relabelScale x ^ 2 + 1))
      (fun x => relabelScale x ^ 3) := by
    simpa -implicitDefEqProofs only [pow_one, pow_succ, Nat.mul_comm] using hg'.mul
      (((Dominated.refl relabelScale).pow 2).add_same
        (dominated_one_pow relabelScale relabelScale_pos 2))
  apply relabel_structural_growth.mono
  · simp only [Dominated.add_iff]
    exact ⟨⟨Dominated.const_of_pos 1 (fun _ => Nat.pow_pos (relabelScale_pos _)),
      ⟨ht, Dominated.pow_of_le (Dominated.refl _) (by decide) relabelScale_pos⟩⟩,
      Dominated.const_of_pos 1 (fun _ => Nat.pow_pos (relabelScale_pos _))⟩
  · simp only [Dominated.add_iff]
    exact ⟨⟨Dominated.refl _, hs.mono_pow (by decide : 3 ≤ 4) relabelScale_pos⟩,
      Dominated.const_of_pos 1 (fun _ => Nat.pow_pos (relabelScale_pos _))⟩

noncomputable def Implementation.relabel {ρ : Type} [UniqueEncoding Tree ρ]
    {n m k : ρ → ℕ}
    {c : (x : ρ) → Circuit .booleanAlgebra (n x) (m x)}
    {w : (x : ρ) → Fin (n x) → Fin (k x)}
    (h : Implementation (fun x => (⟨n x, m x, k x, c x, w x⟩ : RelabelInput))) :
    Implementation (fun x => ⌜(c x).relabel (w x)⌝ₜ) :=
  h.comp relabelImplementation

@[simp, source_bounds↓] theorem Implementation.bounds_relabel {ρ : Type} [UniqueEncoding Tree ρ]
    {n m k : ρ → ℕ} {c : (x : ρ) → Circuit .booleanAlgebra (n x) (m x)}
    {w : (x : ρ) → Fin (n x) → Fin (k x)}
    (h : Implementation (fun x => (⟨n x, m x, k x, c x, w x⟩ : RelabelInput))) :
    (Implementation.relabel h).bounds =
      compBounds (fun x => (⟨n x, m x, k x, c x, w x⟩ : RelabelInput)) h.bounds
        relabelImplementation.bounds :=
  Implementation.bounds_comp _ _

attribute [scoped fun_prop] Implementation.relabel

theorem Implementation.HasGrowth.relabel {ρ : Type} [UniqueEncoding Tree ρ]
    {n m k : ρ → ℕ}
    {c : (x : ρ) → Circuit .booleanAlgebra (n x) (m x)}
    {w : (x : ρ) → Fin (n x) → Fin (k x)}
    {hf : Implementation (fun x => (⟨n x, m x, k x, c x, w x⟩ : RelabelInput))}
    {t p : ρ → ℕ} (h : hf.HasGrowth t p) :
    hf.relabel.HasGrowth
      (fun x => t x + relabelScale ⟨n x, m x, k x, c x, w x⟩ ^ 7)
      (fun x => max (p x) (relabelScale ⟨n x, m x, k x, c x, w x⟩ ^ 4)) :=
  h.comp (u := fun x => relabelScale x ^ 7) (q := fun x => relabelScale x ^ 4)
    relabel_growth

abbrev CompInput := Σ n, Σ m, Σ k, Circuit .booleanAlgebra n m × Circuit .booleanAlgebra m k

def compFn (x : CompInput) := x.2.2.2.1.comp x.2.2.2.2

def compTest (x : CompInput) :=
  match x.2.2.2.1 with | .outputs _ => false | .gate _ _ _ => true

def compNextFn : CompInput → CompInput
  | ⟨n, m, k, .gate _ _ next, d⟩ => ⟨n + 1, m, k, next, d⟩
  | x => x

def compFinishFn : (x : {x // compTest x = false}) →
    Circuit .booleanAlgebra x.1.1 x.1.2.2.1
  | ⟨⟨n, m, k, .outputs select, d⟩, _⟩ => relabelFn ⟨m, k, n, d, select⟩
  | ⟨⟨_, _, _, .gate _ _ _, _⟩, h⟩ => False.elim (by cases h)

def compResumeFn : (x : {x // compTest x = true}) →
    Circuit .booleanAlgebra (compNextFn x.1).1 (compNextFn x.1).2.2.1 →
    Circuit .booleanAlgebra x.1.1 x.1.2.2.1
  | ⟨⟨_, _, _, .outputs _, _⟩, h⟩, _ => False.elim (by cases h)
  | ⟨⟨_, _, _, .gate op args _, _⟩, _⟩, result => .gate op args result

def compRecursion : Recursion compFn where
  test := compTest
  next := compNextFn
  finish := compFinishFn
  resume := compResumeFn
  finish_eq := by
    rintro ⟨⟨n, m, k, c, d⟩, h⟩
    cases c <;> dsimp [compTest] at h ⊢ <;> first | contradiction | rfl
  resume_eq := by
    rintro ⟨⟨n, m, k, c, d⟩, h⟩
    cases c <;> dsimp [compTest] at h ⊢ <;> first | contradiction | rfl
  measure x := x.2.2.2.1.size
  decreases := by
    rintro ⟨n, m, k, c, d⟩ h
    cases c <;> simp_all [compTest, compNextFn]


noncomputable def compCheck : Implementation compTest := by source_fun_prop


noncomputable def compNext : Implementation compNextFn := by source_fun_prop
noncomputable def compFinish : Implementation (fun x => ⌜compFinishFn x⌝ₜ) := by
  source_fun_prop
noncomputable def compResume : Implementation
    (fun x : compRecursion.Return => ⌜compResumeFn x.1 x.2⌝ₜ) := by source_fun_prop



noncomputable def compImplementation : Implementation (fun x => ⌜compFn x⌝ₜ) :=
  compRecursion.implementation compCheck compNext compFinish compResume

@[source_bounds] theorem compImplementation_bounds :
    compImplementation.bounds =
      compRecursion.bounds compCheck.bounds compNext.bounds
        compFinish.bounds compResume.bounds :=
  Recursion.bounds_implementation ..

theorem comp_input_size_le (n m k : ℕ) (c : Circuit .booleanAlgebra n m)
    (d : Circuit .booleanAlgebra m k) (N : ℕ)
    (h : n + m + k + 2 * (c.size + d.size) ≤ N) :
    ⌜(⟨n, m, k, c, d⟩ : CompInput)⌝ₜ.size ≤ 256 * (N + 1) ^ 2 := by
  have hc := c.size_encode_numeric_le
  have hd := d.size_encode_numeric_le
  have hcp : (c.size + m + 1) * (n + c.size + 1) ≤ (N + 1) ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul (by omega : c.size + m + 1 ≤ N + 1)
      (by omega : n + c.size + 1 ≤ N + 1)
  have hdp : (d.size + k + 1) * (m + d.size + 1) ≤ (N + 1) ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul (by omega : d.size + k + 1 ≤ N + 1)
      (by omega : m + d.size + 1 ≤ N + 1)
  have hn := size_encode_nat_le n
  have hm := size_encode_nat_le m
  have hk := size_encode_nat_le k
  simp only [Sigma.encode_mk, size_encode_prod]
  nlinarith

def compScale (x : CompInput) : ℕ :=
  x.1 + x.2.1 + x.2.2.1 + 2 * (x.2.2.2.1.size + x.2.2.2.2.size) + 1

theorem compScale_pos (x : CompInput) : 0 < compScale x := Nat.succ_pos _

def compRelabelInput (x : {x // compRecursion.test x = false}) : RelabelInput := by
  rcases x with ⟨⟨n, m, k, c, d⟩, h⟩
  cases c with
  | outputs w => exact ⟨m, k, n, d, w⟩
  | gate op args next => cases h

@[source_growth] theorem compFinish_growth : compFinish.HasGrowth
    (fun x => compScale x.1 ^ 7) (fun x => ⌜x⌝ₜ.size + compScale x.1 ^ 4) := by
  let input (x : Σ n, Σ m, Σ k, (Fin m → Fin n) × Circuit .booleanAlgebra m k) :
      {x // compTest x = false} :=
    ⟨⟨x.1, x.2.1, x.2.2.1, .outputs x.2.2.2.1, x.2.2.2.2⟩, rfl⟩
  have hi : Function.Surjective input := by
    rintro ⟨⟨n, m, k, c, d⟩, h⟩
    cases c with
    | outputs w => exact ⟨⟨n, m, k, w, d⟩, rfl⟩
    | gate op args next => cases h
  let u x := compRelabelInput (input x)
  let R x := compScale (input x).1
  let N x := ⌜input x⌝ₜ.size
  have hR x : 0 < R x := compScale_pos _
  have hu : Dominated (fun x => ⌜u x⌝ₜ.size) N := Dominated.of_le fun x => by
    simp only [u, compRelabelInput, N, input, UniqueEncoding.encode_subtype, Sigma.encode_mk,
      Circuit.encode_outputs, size_encode_prod, size_encode_unit]
    omega
  have hr : Dominated (relabelScale ∘ u) R := Dominated.of_le fun x => by
    dsimp [Function.comp_def, u, compRelabelInput, input, relabelScale, R, compScale]
    omega
  have ht := (Dominated.comp relabel_growth.1 u).trans (hr.pow 7)
  have hp := ((Dominated.comp relabel_growth.2 u).trans (hr.pow 4)).mono
    (g' := fun x => N x + R x ^ 4) (fun _ => Nat.le_add_left _ _)
  source_fun_prop
  all_goals
    apply Dominated.of_comp_surjective input hi
    dsimp only [Function.comp_def, input]
  · change Dominated _ (fun x => R x ^ 7)
    simp only [Dominated.add_iff,
      Dominated.const_of_pos _ (fun x => Nat.pow_pos (hR x)), true_and, and_true]
    simpa -implicitDefEqProofs only [Function.comp_def, u, compRelabelInput, input] using ht
  · change Dominated _ (fun x => N x + R x ^ 4)
    simp only [Dominated.max_iff]
    (repeat' apply And.intro) <;> first
      | with_reducible simpa only [Function.comp_def, u, compRelabelInput, input] using hp
      | apply Dominated.of_le
        intro x
        simp only [N, input, UniqueEncoding.encode_subtype, Sigma.encode_mk,
          Circuit.encode_outputs, size_encode_prod, size_encode_unit]
        omega

theorem compScale_next_le (x : CompInput) : compScale (compNextFn x) ≤ compScale x := by
  rcases x with ⟨n, m, k, c, d⟩
  cases c <;> simp -implicitDefEqProofs only [compNextFn, compScale, Circuit.size_gate] <;> omega

theorem size_encode_compFn_le (x : CompInput) : ⌜compFn x⌝ₜ.size ≤ 100 * compScale x ^ 2 := by
  rcases x with ⟨n, m, k, c, d⟩
  have h := (c.comp d).size_encode_numeric_le
  simp -implicitDefEqProofs only [Circuit.size_comp] at h
  apply h.trans
  simpa -implicitDefEqProofs only [pow_two, Nat.mul_assoc] using Nat.mul_le_mul
    (Nat.mul_le_mul_left 100 (by dsimp [compScale]; omega :
      c.size + d.size + k + 1 ≤ compScale ⟨n, m, k, c, d⟩))
    (by dsimp [compScale]; omega : n + (c.size + d.size) + 1 ≤ compScale ⟨n, m, k, c, d⟩)

@[source_growth] theorem compCheck_growth : compCheck.HasGrowth
    (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  · exact Dominated.const_of_pos _ (fun _ => Nat.zero_lt_one)
  · apply Dominated.of_le
    rintro ⟨n, m, k, c, d⟩
    cases c <;> simp <;> omega

@[source_growth] theorem compNext_growth : compNext.HasGrowth
    (fun x => ⌜x⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) := by
  let output (x : Σ n, Σ m, Σ k, (Fin m → Fin n) × Circuit .booleanAlgebra m k) :
      CompInput :=
    ⟨x.1, x.2.1, x.2.2.1, .outputs x.2.2.2.1, x.2.2.2.2⟩
  let gate (x : Σ n, Σ m, Σ k, Σ a, FirstOrder.Language.booleanAlgebra.Functions a ×
      (Fin a → Fin n) × Circuit .booleanAlgebra (n + 1) m × Circuit .booleanAlgebra m k) :
      CompInput :=
    ⟨x.1, x.2.1, x.2.2.1, .gate x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2⟩
  have cover x : (∃ y, output y = x) ∨ ∃ y, gate y = x := by
    rcases x with ⟨n, m, k, c, d⟩
    cases c with
    | outputs w => exact Or.inl ⟨⟨n, m, k, w, d⟩, rfl⟩
    | gate op args next => exact Or.inr ⟨⟨n, m, k, _, op, args, next, d⟩, rfl⟩
  source_fun_prop
  all_goals
    apply Dominated.of_cover output gate cover
    all_goals
      dsimp only [Function.comp_def, output, gate]
      try source_fun_prop
      simp only [Function.comp_apply, Dominated.add_iff, Dominated.max_iff]
      repeat' apply And.intro
  all_goals with_reducible first
    | exact Dominated.const_of_pos _ (fun _ => Tree.size_pos _)
    | apply Dominated.of_le
      rintro ⟨n, m, k, a, op, args, next, d⟩
      simp only [Sigma.encode_mk, size_encode_prod, Tree.encode_self,
        Circuit.encode_gate, size_encode_unit]
      omega
    | apply Dominated.of_le
      rintro ⟨n, m, k, w, d⟩
      simp only [Sigma.encode_mk, size_encode_prod, Circuit.encode_outputs, size_encode_unit]
      omega
    | apply Dominated.of_le_mul 6
      rintro ⟨n, m, k, a, op, args, next, d⟩
      have h := size_encode_nat_succ_le n
      simp only [Sigma.encode_mk, size_encode_prod, Tree.encode_self,
        Circuit.encode_gate, size_encode_unit]
      omega

@[source_growth] theorem compResume_growth : compResume.HasGrowth
    (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  have hcode (x : compRecursion.Return) : ⌜x⌝ₜ.size =
      1 + ⌜x.1.1⌝ₜ.size + ⌜x.2⌝ₜ.size := by
    rcases x with ⟨x, result⟩
    rfl
  source_fun_prop
  · apply Dominated.of_forall_eq
    rintro ⟨⟨⟨n, m, k, c, d⟩, h⟩, r⟩ ⟨⟨⟨n', m', k', c', d'⟩, h'⟩, r'⟩
    cases c with
    | outputs _ => cases h
    | gate op args next =>
      cases c' with
      | outputs _ => cases h'
      | gate op' args' next' => rfl
  · apply Dominated.of_le
    rintro ⟨⟨⟨n, m, k, c, d⟩, h⟩, result⟩
    cases c with
    | outputs _ => cases h
    | gate op args next =>
      simp only [hcode]
      dsimp +instances only [id, Recursion.Return, compRecursion, compNextFn]
      simp only [Sigma.encode_mk, size_encode_prod,
        Tree.encode_self, Circuit.encode_gate, size_encode_unit, max_le_iff]
      erw [size_encode_prod, Circuit.encode_gate]
      repeat' first
        | erw [size_encode_prod]
        | rw [size_encode_unit]
      omega

/-- The terminal relabel call is paid once, so the time expression has degree seven, not eight. -/
theorem comp_cost_growth :
    let bc : Bounds CompInput := ⟨fun _ => 1, fun x => ⌜x⌝ₜ.size⟩
    let bs : Bounds CompInput := ⟨fun x => ⌜x⌝ₜ.size, fun x => ⌜x⌝ₜ.size⟩
    let bd : Bounds {x // compRecursion.test x = false} :=
      ⟨fun x => compScale x.1 ^ 7, fun x => ⌜x⌝ₜ.size + compScale x.1 ^ 4⟩
    let br : Bounds compRecursion.Return := ⟨fun _ => 1, fun x => ⌜x⌝ₜ.size⟩
    Dominated (fun x => (compRecursion.cost bc bs bd br x).time)
      (fun x => x.2.2.2.1.size * compScale x ^ 2 + compScale x ^ 7) ∧
    Dominated (fun x => (compRecursion.cost bc bs bd br x).peak)
      (fun x => compScale x ^ 4 + (x.2.2.2.1.size + 1) * (compScale x ^ 2 + 1)) := by
  dsimp only
  let I (a x : CompInput) := compScale x ≤ compScale a
  let Z := {p : CompInput × CompInput // I p.1 p.2}
  let R (z : Z) := compScale z.1.1
  let s (z : Z) := ⌜z.1.2⌝ₜ.size
  let o (z : Z) := ⌜compFn (compNextFn z.1.2)⌝ₜ.size
  have hR (z : Z) : 0 < R z := compScale_pos _
  have hsize : Dominated s (fun z => R z ^ 2) := Dominated.of_le_mul 256 fun z => by
    rcases z with ⟨⟨a, ⟨n, m, k, c, d⟩⟩, hz⟩
    have h := comp_input_size_le n m k c d (compScale a - 1)
      (by dsimp [I, compScale] at hz; dsimp [compScale]; omega)
    simpa -implicitDefEqProofs only [s, R, Nat.sub_add_cancel (compScale_pos a)] using h
  have hout : Dominated o (fun z => R z ^ 2) := Dominated.of_le_mul 100 fun z =>
    (size_encode_compFn_le _).trans (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_left ((compScale_next_le _).trans z.2) 2))
  have hscale : Dominated (fun z : Z => compScale z.1.2) R :=
    Dominated.of_le fun z => z.2
  let Step := {z : Z // compRecursion.test z.1.2 = true}
  let u (z : Step) : compRecursion.Return := ⟨⟨z.1.1.2, z.2⟩, compFn (compNextFn z.1.1.2)⟩
  have hreturn : Dominated (fun z => ⌜u z⌝ₜ.size) (fun z : Step => R z.1 ^ 2) := by
    have eq : (fun z : Step => ⌜u z⌝ₜ.size) = (fun z => 1 + s z.1 + o z.1) := by
      funext z
      rfl
    rw [eq]
    exact Dominated.comp (((dominated_one_pow R hR 2).add_same hsize).add_same hout)
      Subtype.val
  have hfinishPeak := (hsize.mono_pow (by decide : 2 ≤ 4) hR).add_same (hscale.pow 4)
  refine compRecursion.dominated_cost_of_bounds _ _ _ _ I id
    (fun x => compScale x ^ 2) (fun x => compScale x ^ 7)
    (fun x => compScale x ^ 2) (fun x => compScale x ^ 4)
    (fun _ => le_rfl) (fun a x hx _ => (compScale_next_le x).trans hx) hsize
    (hsize.mono_pow (by decide) hR) (hsize.mono_pow (by decide) hR)
    (Dominated.comp hfinishPeak Subtype.val) (hreturn.mono_pow (by decide) fun z => hR z.1)
    (Dominated.comp (hscale.pow 7) Subtype.val) hsize
    (Dominated.const_of_pos 1 fun z => Nat.pow_pos (hR z))
    (Dominated.const_of_pos 1 fun z => Nat.pow_pos (hR z.1))
    (fun _ => Nat.pow_pos (compScale_pos _)) (fun _ => Nat.pow_pos (compScale_pos _))

theorem comp_structural_growth : compImplementation.HasGrowth
    (fun x => 1 + (x.2.2.2.1.size * compScale x ^ 2 + compScale x ^ 7) + 1)
    (fun x => (compScale x ^ 4 + (x.2.2.2.1.size + 1) * (compScale x ^ 2 + 1)) + 1) :=
  compRecursion.hasGrowth_of_growth compCheck_growth compNext_growth
    compFinish_growth compResume_growth comp_cost_growth

@[source_growth] theorem comp_growth : compImplementation.HasGrowth
    (fun x => compScale x ^ 7) (fun x => compScale x ^ 4) := by
  have hg : Dominated (fun x : CompInput => x.2.2.2.1.size) compScale :=
    Dominated.of_le fun x => by dsimp [compScale]; omega
  have hg' := hg.add_same (Dominated.one compScale_pos)
  have ht : Dominated (fun x => x.2.2.2.1.size * compScale x ^ 2)
      (fun x => compScale x ^ 3) := by
    simpa -implicitDefEqProofs only [pow_succ, Nat.mul_comm] using
      hg.mul ((Dominated.refl compScale).pow 2)
  have hs : Dominated (fun x => (x.2.2.2.1.size + 1) * (compScale x ^ 2 + 1))
      (fun x => compScale x ^ 3) := by
    simpa -implicitDefEqProofs only [pow_succ, Nat.mul_comm] using hg'.mul
      (((Dominated.refl compScale).pow 2).add_same
        (dominated_one_pow compScale compScale_pos 2))
  apply comp_structural_growth.mono
  · simp only [Dominated.add_iff]
    exact ⟨⟨Dominated.const_of_pos 1 (fun _ => Nat.pow_pos (compScale_pos _)),
      ⟨ht.mono_pow (by decide : 3 ≤ 7) compScale_pos, Dominated.refl _⟩⟩,
      Dominated.const_of_pos 1 (fun _ => Nat.pow_pos (compScale_pos _))⟩
  · simp only [Dominated.add_iff]
    exact ⟨⟨Dominated.refl _, hs.mono_pow (by decide : 3 ≤ 4) compScale_pos⟩,
      Dominated.const_of_pos 1 (fun _ => Nat.pow_pos (compScale_pos _))⟩

noncomputable def Implementation.circuitComp {ρ : Type} [UniqueEncoding Tree ρ]
    {n m k : ρ → ℕ}
    {c : (x : ρ) → Circuit .booleanAlgebra (n x) (m x)}
    {d : (x : ρ) → Circuit .booleanAlgebra (m x) (k x)}
    (h : Implementation (fun x => (⟨n x, m x, k x, c x, d x⟩ : CompInput))) :
    Implementation (fun x => ⌜(c x).comp (d x)⌝ₜ) :=
  h.comp compImplementation

@[simp, source_bounds↓] theorem Implementation.bounds_circuitComp {ρ : Type} [UniqueEncoding Tree ρ]
    {n m k : ρ → ℕ} {c : (x : ρ) → Circuit .booleanAlgebra (n x) (m x)}
    {d : (x : ρ) → Circuit .booleanAlgebra (m x) (k x)}
    (h : Implementation (fun x => (⟨n x, m x, k x, c x, d x⟩ : CompInput))) :
    (Implementation.circuitComp h).bounds =
      compBounds (fun x => (⟨n x, m x, k x, c x, d x⟩ : CompInput)) h.bounds
        compImplementation.bounds :=
  Implementation.bounds_comp _ _

attribute [scoped fun_prop] Implementation.circuitComp

abbrev KeepInput := Σ n, Σ m, Circuit .booleanAlgebra n m

def keepFn (x : KeepInput) := x.2.2.keepInputs

def keepTest (x : KeepInput) :=
  match x.2.2 with | .outputs _ => false | .gate _ _ _ => true

def keepNextFn : KeepInput → KeepInput
  | ⟨n, m, .gate _ _ next⟩ => ⟨n + 1, m, next⟩
  | x => x

/-- An outputs circuit gains its identity outputs without changing existing wires. -/
abbrev KeepOutputsInput := Σ n, Σ m, Fin m → Fin n

def keepOutputsFn (x : KeepOutputsInput) : Circuit .booleanAlgebra x.1 (x.1 + x.2.1) :=
  .outputs (Fin.append id x.2.2)

def keepFinishFn : (x : {x // keepTest x = false}) →
    Circuit .booleanAlgebra x.1.1 (x.1.1 + x.1.2.1)
  | ⟨⟨n, m, .outputs select⟩, _⟩ => keepOutputsFn ⟨n, m, select⟩
  | ⟨⟨_, _, .gate _ _ _⟩, h⟩ => False.elim (by cases h)

def keepResumeFn : (x : {x // keepTest x = true}) →
    Circuit .booleanAlgebra (keepNextFn x.1).1 ((keepNextFn x.1).1 + (keepNextFn x.1).2.1) →
    Circuit .booleanAlgebra x.1.1 (x.1.1 + x.1.2.1)
  | ⟨⟨_, _, .outputs _⟩, h⟩, _ => False.elim (by cases h)
  | ⟨⟨n, m, .gate op args _⟩, _⟩, result =>
      .gate op args (result.mapOutputs
        (Fin.append (fun i : Fin n => Fin.castAdd m i.castSucc) (Fin.natAdd (n + 1))))

def keepRecursion : Recursion keepFn where
  test := keepTest
  next := keepNextFn
  finish := keepFinishFn
  resume := keepResumeFn
  finish_eq := by
    rintro ⟨⟨n, m, c⟩, h⟩
    cases c <;> dsimp [keepTest] at h ⊢ <;> first | contradiction | rfl
  resume_eq := by
    rintro ⟨⟨n, m, c⟩, h⟩
    cases c <;> dsimp [keepTest] at h ⊢ <;> first | contradiction | rfl
  measure x := x.2.2.size
  decreases := by
    rintro ⟨n, m, c⟩ h
    cases c <;> simp_all [keepTest, keepNextFn]


noncomputable def keepCheck : Implementation keepTest := by source_fun_prop


noncomputable def keepNext : Implementation keepNextFn := by source_fun_prop
private theorem keepOutputs_input_growth :
    Dominated (fun x : KeepOutputsInput => ⌜x⌝ₜ.size) (fun x => (x.1 + x.2.1 + 1) ^ 2) := by
  let R (x : KeepOutputsInput) := x.1 + x.2.1 + 1
  have hR x : 0 < R x := Nat.succ_pos _
  have hn : Dominated (fun x : KeepOutputsInput => x.1) R :=
    Dominated.of_le fun x => by dsimp [R]; omega
  have hm : Dominated (fun x : KeepOutputsInput => x.2.1) R :=
    Dominated.of_le fun x => by dsimp [R]; omega
  have hcn := hn.size_encode_nat hR
  have hcm := hm.size_encode_nat hR
  have hw := Dominated.size_encode_fin_function (fun x : KeepOutputsInput => x.2.2) hm hn hR
  change Dominated (fun x : KeepOutputsInput =>
    1 + ⌜x.1⌝ₜ.size + (1 + ⌜x.2.1⌝ₜ.size + ⌜x.2.2⌝ₜ.size)) _
  simp only [Dominated.add_iff]
  have hc := Dominated.const_of_pos (g := fun x => R x ^ 2) 1 (fun x => Nat.pow_pos (hR x))
  exact ⟨⟨hc, hcn.le_pow (by decide)⟩, ⟨hc, hcm.le_pow (by decide)⟩, hw⟩

noncomputable def keepOutputs : Implementation (fun x => ⌜keepOutputsFn x⌝ₜ) := by
  source_fun_prop using tabulate

@[source_growth] theorem keepOutputs_growth : keepOutputs.HasGrowth
    (fun x => (x.1 + x.2.1 + 1) ^ 2) (fun x => (x.1 + x.2.1 + 1) ^ 2) := by
  let R (x : KeepOutputsInput) := x.1 + x.2.1 + 1
  have hR x : 0 < R x := Nat.succ_pos _
  have hn : Dominated (fun x : KeepOutputsInput => x.1) R :=
    Dominated.of_le fun x => by dsimp [R]; omega
  have hm : Dominated (fun x : KeepOutputsInput => x.2.1) R :=
    Dominated.of_le fun x => by dsimp [R]; omega
  have hcn := hn.size_encode_nat hR
  have hcm := hm.size_encode_nat hR
  have hw := Dominated.size_encode_fin_function (fun x : KeepOutputsInput => x.2.2) hm hn hR
  have hinput := keepOutputs_input_growth
  have hid := Dominated.size_encode_fin_function
    (fun x : KeepOutputsInput => (id : Fin x.1 → Fin x.1)) hn hn hR
  have ho := Dominated.size_encode_fin_function
    (fun x : KeepOutputsInput => Fin.append (id : Fin x.1 → Fin x.1) x.2.2) (hn.add_same hm) hn hR
  have hnpow := (hn.add_same (Dominated.one hR)).pow 2
  have hr := (((hn.add_same (Dominated.one hR)).pow 2).const_mul_left 3).mono_left
    (fun x : KeepOutputsInput => size_encode_range_le x.1)
  have hidCode (x : KeepOutputsInput) : ⌜List.ofFn (fun i : Fin x.1 => ⌜i⌝ₜ)⌝ₜ =
      ⌜(id : Fin x.1 → Fin x.1)⌝ₜ := encode_fin_function_codes _
  source_fun_prop
  all_goals
    change Dominated _ (fun x => R x ^ 2)
    simp only [Function.comp_apply, Sigma.encode_mk,
      size_encode_unit, size_encode_prod, Tree.encode_self, id_eq, Nat.mul_one,
      List.map_const', List.sum_replicate, List.length_finRange, List.length_ofFn,
      encode_finRange, ← List.ofFn_eq_map, encode_fin_function_codes, hidCode, smul_eq_mul,
      Dominated.add_iff, Dominated.max_iff, Dominated.const_mul_left_iff,
      Nat.ofNat_pos]
    repeat' apply And.intro
  all_goals with_reducible first
    | assumption
    | exact Dominated.const_of_pos _ (fun x => Nat.pow_pos (hR x))
    | exact Dominated.le_pow (g := R) (by assumption) (by decide)
    | skip
  · let Z := Σ x : KeepOutputsInput, Fin x.1
    have hci := Dominated.size_encode_nat
      ((Dominated.comp hn (Sigma.fst : Z → KeepOutputsInput)).mono_left (fun z => z.2.isLt.le))
      (fun z => hR z.1)
    have hs := Dominated.comp hinput (Sigma.fst : Z → KeepOutputsInput)
    simp only [Function.comp_def] at hci hs
    apply Dominated.foldr_max_le
    simp only [encode_fin, Dominated.max_iff, Dominated.add_iff]
    repeat' apply And.intro
    all_goals with_reducible first
      | assumption
      | exact Dominated.const_of_pos _ (fun z : Z => Nat.pow_pos (hR z.1))
      | exact Dominated.le_pow (g := fun z : Z => R z.1) (by assumption) (by decide)

noncomputable def keepFinish : Implementation (fun x => ⌜keepFinishFn x⌝ₜ) := by
  let input : {x // keepTest x = false} → KeepOutputsInput
    | ⟨⟨n, m, .outputs w⟩, _⟩ => ⟨n, m, w⟩
    | ⟨⟨_, _, .gate _ _ _⟩, h⟩ => False.elim (by cases h)
  have hi : Implementation input := by source_fun_prop
  exact (hi.comp keepOutputs).congr (by
    funext ⟨⟨n, m, c⟩, h⟩
    cases c with
    | outputs w => rfl
    | gate op args next => cases h)
/-- The live return value and gate fields needed by the return callback. -/
abbrev KeepGateInput := Σ n, Σ m, Σ k, FirstOrder.Language.booleanAlgebra.Functions k ×
  (Fin k → Fin n) × Circuit .booleanAlgebra (n + 1) (n + 1 + m)

def keepGateFn (x : KeepGateInput) : Tree :=
  ⌜Circuit.gate x.2.2.2.1 x.2.2.2.2.1
    (x.2.2.2.2.2.mapOutputs
      (Fin.append (fun i : Fin x.1 => Fin.castAdd x.2.1 i.castSucc)
        (Fin.natAdd (x.1 + 1))))⌝ₜ

noncomputable def keepGateImplementation : Implementation keepGateFn := by
  source_fun_prop using tabulate

def keepResumeInput : keepRecursion.Return → KeepGateInput
  | ⟨⟨⟨_, _, .outputs _⟩, h⟩, _⟩ => False.elim (by cases h)
  | ⟨⟨⟨n, m, .gate (k := k) op args _⟩, _⟩, result⟩ => ⟨n, m, k, op, args, result⟩

noncomputable def keepResumeInputImplementation : Implementation keepResumeInput := by
  source_fun_prop

noncomputable def keepResume : Implementation
    (fun x : keepRecursion.Return => ⌜keepResumeFn x.1 x.2⌝ₜ) :=
  (keepResumeInputImplementation.comp keepGateImplementation).congr (by
    funext ⟨⟨⟨n, m, c⟩, h⟩, result⟩
    cases c with
    | outputs _ => cases h
    | gate _ _ _ => rfl)

/-- The selected recursive program; its growth is certified below. -/
noncomputable def keepImplementation : Implementation (fun x => ⌜keepFn x⌝ₜ) :=
  keepRecursion.implementation keepCheck keepNext keepFinish keepResume

theorem keep_input_size_le (n m : ℕ) (c : Circuit .booleanAlgebra n m)
    (N : ℕ) (h : n + m + 2 * c.size ≤ N) :
    ⌜(⟨n, m, c⟩ : KeepInput)⌝ₜ.size ≤ 128 * (N + 1) ^ 2 := by
  have hc := c.size_encode_numeric_le
  have hcp : (c.size + m + 1) * (n + c.size + 1) ≤ (N + 1) ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul (by omega : c.size + m + 1 ≤ N + 1)
      (by omega : n + c.size + 1 ≤ N + 1)
  have hn := size_encode_nat_le n
  have hm := size_encode_nat_le m
  simp only [Sigma.encode_mk, size_encode_prod]
  nlinarith

def keepScale (x : KeepInput) : ℕ := x.1 + x.2.1 + 2 * x.2.2.size + 1

theorem keepScale_pos (x : KeepInput) : 0 < keepScale x := Nat.succ_pos _

def keepGateScale (x : KeepGateInput) := x.1 + x.2.1 + x.2.2.2.2.2.size + 1

@[source_growth] theorem keepGate_growth : keepGateImplementation.HasGrowth
    (fun x => keepGateScale x ^ 7) (fun x => keepGateScale x ^ 4) := by
  let R := keepGateScale
  have hR x : 0 < R x := Nat.succ_pos _
  have hn : Dominated (fun x : KeepGateInput => x.1) R :=
    Dominated.of_le fun x => by dsimp [R, keepGateScale]; omega
  have hm : Dominated (fun x : KeepGateInput => x.2.1) R :=
    Dominated.of_le fun x => by dsimp [R, keepGateScale]; omega
  have hk : Dominated (fun x : KeepGateInput => x.2.2.1) R :=
    (Dominated.const_of_pos 2 hR).mono_left fun x => by
      rcases x with ⟨n, m, k, op, args, result⟩
      cases op <;> dsimp <;> decide
  have hop : Dominated (fun x : KeepGateInput => ⌜x.2.2.2.1⌝ₜ.size) R :=
    (Dominated.const_of_pos 11 hR).mono_left fun x => by
      rcases x with ⟨n, m, k, op, args, result⟩
      cases op <;> simp [encode_unit]
  have hn1 := hn.add_same (Dominated.one hR)
  have hnm := hn.add_same hm
  have hn1m := hn1.add_same hm
  have hresult := Dominated.size_encode_circuit (fun x : KeepGateInput => x.2.2.2.2.2)
    hn1 hn1m (Dominated.of_le fun x => by dsimp [R, keepGateScale]; omega) hR
  have hargs := Dominated.size_encode_fin_function (fun x : KeepGateInput => x.2.2.2.2.1)
    hk hn hR
  let w₁ (x : KeepGateInput) (i : Fin x.1) := Fin.castAdd x.2.1 i.castSucc
  let w₂ (x : KeepGateInput) : Fin x.2.1 → Fin (x.1 + 1 + x.2.1) :=
    Fin.natAdd (x.1 + 1)
  let w (x : KeepGateInput) := Fin.append (w₁ x) (w₂ x)
  have hw₁ := Dominated.size_encode_fin_function w₁ hn hn1m hR
  have hw₂ := Dominated.size_encode_fin_function w₂ hm hn1m hR
  have hw := Dominated.size_encode_fin_function w hnm hn1m hR
  have hmapped := Dominated.size_encode_circuit
    (fun x : KeepGateInput => x.2.2.2.2.2.mapOutputs (w x)) hn1 hnm
    (Dominated.of_le fun x => by
      simp only [Circuit.size_mapOutputs]
      dsimp [R, keepGateScale]
      omega) hR
  have hrn : Dominated (fun x : KeepGateInput => ⌜List.range x.1⌝ₜ.size)
      (fun x => R x ^ 2) :=
    ((hn1.pow 2).const_mul_left 3).mono_left fun x => size_encode_range_le _
  have hrm : Dominated (fun x : KeepGateInput => ⌜List.range x.2.1⌝ₜ.size)
      (fun x => R x ^ 2) :=
    (((hm.add_same (Dominated.one hR)).pow 2).const_mul_left 3).mono_left
      fun x => size_encode_range_le _
  let u (x : KeepGateInput) : CompInput :=
    ⟨x.1 + 1, x.1 + 1 + x.2.1, x.1 + x.2.1, x.2.2.2.2.2, .outputs (w x)⟩
  have hu : Dominated (compScale ∘ u) R := Dominated.of_le_mul 3 fun x => by
    dsimp [Function.comp_def, compScale, u, R, keepGateScale]
    omega
  have hcn := hn.size_encode_nat hR
  have hcm := hm.size_encode_nat hR
  have hck := hk.size_encode_nat hR
  have hcn1 := Dominated.size_encode_nat hn1 hR
  have hcnm := Dominated.size_encode_nat hnm hR
  have hcn1m := Dominated.size_encode_nat hn1m hR
  have hinput : Dominated (fun x : KeepGateInput => ⌜x⌝ₜ.size) (fun x => R x ^ 2) := by
    rw [show (fun x : KeepGateInput => ⌜x⌝ₜ.size) =
      (fun x => 1 + ⌜x.1⌝ₜ.size + (1 + ⌜x.2.1⌝ₜ.size + (1 + ⌜x.2.2.1⌝ₜ.size +
        (1 + ⌜x.2.2.2.1⌝ₜ.size + (1 + ⌜x.2.2.2.2.1⌝ₜ.size + ⌜x.2.2.2.2.2⌝ₜ.size)))))
      from by funext ⟨n, m, k, op, args, result⟩; rfl]
    simp only [Dominated.add_iff]
    repeat' apply And.intro
    all_goals with_reducible first
      | with_reducible assumption
      | exact Dominated.const_of_pos _ (fun x => Nat.pow_pos (hR x))
      | exact Dominated.le_pow (g := R) (by with_reducible assumption) (by decide)
  have hcomp7 := hu.pow 7
  have hcomp4 := hu.pow 4
  simp only [Function.comp_apply, u, w, w₁, w₂] at hcomp7 hcomp4
  have hnpow := hn1.pow 2
  have hmpow := (hm.add_same (Dominated.one hR)).pow 2
  source_fun_prop
  all_goals
    simp only [Function.comp_apply, id_eq, Sigma.encode_mk, Tree.encode_self,
      size_encode_prod, size_encode_unit, Circuit.encode_outputs,
      Dominated.add_iff, Dominated.max_iff, Dominated.const_mul_left_iff,
      Nat.ofNat_pos, Dominated.zero,
      true_and, List.map_const', List.sum_replicate,
      List.length_finRange, List.length_ofFn, encode_finRange, ← List.ofFn_eq_map,
      encode_fin_function_codes, Nat.nsmul_eq_mul, Nat.mul_one]
    repeat' apply And.intro
  all_goals with_reducible first
    | with_reducible assumption
    | exact Dominated.const_of_pos _ (fun x => Nat.pow_pos (hR x))
    | exact Dominated.le_pow (g := R) (by with_reducible assumption) (by decide)
    | exact Dominated.mono_pow (g := R) (d := 2) (by with_reducible assumption) (by decide) hR
    | skip
  · simp only [List.ofFn_eq_map]
    have htotal : Dominated (fun x : KeepGateInput => x.2.1 * R x)
        (fun x => R x ^ 2) := by
      simpa only [pow_two] using hm.mul (Dominated.refl R)
    refine (Dominated.sum_finRange (b := R) ?_).trans
      (htotal.mono_pow (e := 7) (by decide) hR)
    let Z := Σ x : KeepGateInput, Fin x.2.1
    have hi : Dominated (fun z : Z => z.2.val) (fun z => R z.1) :=
      (Dominated.comp hm Sigma.fst).mono_left fun z => z.2.isLt.le
    have hci := Dominated.size_encode_nat hi (fun z => hR z.1)
    have hc := Dominated.comp hcn (Sigma.fst : Z → KeepGateInput)
    have hc1 := Dominated.comp hcn1 (Sigma.fst : Z → KeepGateInput)
    simp only [Function.comp_def] at hc hc1
    simp only [Dominated.add_iff, Dominated.zero, and_true]
    repeat' apply And.intro
    all_goals with_reducible first
      | assumption
      | exact Dominated.const_of_pos (g := fun z : Z => R z.1) _ (fun z => hR z.1)
  · have hi : Dominated (fun z : Σ x : KeepGateInput, Fin x.1 => z.2.val)
        (fun z => R z.1) := (Dominated.comp hn Sigma.fst).mono_left fun z => z.2.isLt.le
    have hci := hi.size_encode_nat (fun z => hR z.1)
    have hs := Dominated.comp hinput (Sigma.fst : (Σ x : KeepGateInput, Fin x.1) → _)
    simp only [Function.comp_def] at hs
    apply Dominated.foldr_max_le
    simp only [encode_fin, Fin.val_castAdd, Fin.val_castSucc,
      Dominated.max_iff, Dominated.add_iff]
    repeat' apply And.intro
    all_goals with_reducible first
      | exact Dominated.const_of_pos _
          (fun z : Σ x : KeepGateInput, Fin x.1 => Nat.pow_pos (hR z.1))
      | exact Dominated.le_pow (g := fun z : Σ x : KeepGateInput, Fin x.1 => R z.1)
          (by assumption) (by decide)
      | exact Dominated.mono_pow (g := fun z : Σ x : KeepGateInput, Fin x.1 => R z.1) (d := 2)
          (by assumption) (by decide) (fun z => hR z.1)
  · have hi : Dominated (fun z : Σ x : KeepGateInput, Fin x.2.1 => z.2.val)
        (fun z => R z.1) := (Dominated.comp hm Sigma.fst).mono_left fun z => z.2.isLt.le
    have hci := hi.size_encode_nat (fun z => hR z.1)
    have hs := Dominated.comp hinput (Sigma.fst : (Σ x : KeepGateInput, Fin x.2.1) → _)
    have hc := Dominated.comp hcn (Sigma.fst : (Σ x : KeepGateInput, Fin x.2.1) → _)
    have hc1 := Dominated.comp hcn1 (Sigma.fst : (Σ x : KeepGateInput, Fin x.2.1) → _)
    simp only [Function.comp_def] at hs hc hc1
    apply Dominated.foldr_max_le
    simp only [encode_fin, Dominated.max_iff, Dominated.add_iff, Dominated.zero, and_true]
    repeat' apply And.intro
    all_goals with_reducible first
      | exact Dominated.const_of_pos _
          (fun z : Σ x : KeepGateInput, Fin x.2.1 => Nat.pow_pos (hR z.1))
      | exact Dominated.le_pow (g := fun z : Σ x : KeepGateInput, Fin x.2.1 => R z.1)
          (by assumption) (by decide)
      | exact Dominated.mono_pow (g := fun z : Σ x : KeepGateInput, Fin x.2.1 => R z.1) (d := 2)
          (by assumption) (by decide) (fun z => hR z.1)

@[source_growth] theorem keepResumeInput_growth :
    keepResumeInputImplementation.HasGrowth (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  have hcode (x : keepRecursion.Return) : ⌜x⌝ₜ.size =
      1 + ⌜x.1.1⌝ₜ.size + ⌜x.2⌝ₜ.size := by
    rcases x with ⟨x, result⟩
    rfl
  source_fun_prop
  · apply Dominated.of_forall_eq
    rintro ⟨⟨⟨n, m, c⟩, h⟩, result⟩ ⟨⟨⟨n', m', c'⟩, h'⟩, result'⟩
    cases c with
    | outputs _ => cases h
    | gate op args next =>
      cases c' with
      | outputs _ => cases h'
      | gate op' args' next' => rfl
  · apply Dominated.of_le
    rintro ⟨⟨⟨n, m, c⟩, h⟩, result⟩
    cases c with
    | outputs _ => cases h
    | gate op args next =>
      change Circuit .booleanAlgebra (n + 1) (n + 1 + m) at result
      simp only [hcode]
      dsimp +instances only [id, Recursion.Return, keepRecursion, keepNextFn]
      simp only [Sigma.encode_mk, UniqueEncoding.encode_subtype,
        Circuit.encode_gate, size_encode_prod, size_encode_unit, max_le_iff]
      omega

def keepReturnScale (x : keepRecursion.Return) : ℕ := x.1.1.1 + x.1.1.2.1 + x.2.size + 1

/-- The selected return callback consumes the saved composition and traversal specifications. -/
@[source_growth] theorem keepResume_saved_growth : keepResume.HasGrowth
    (fun x => keepReturnScale x ^ 7)
    (fun x => ⌜x⌝ₜ.size + keepReturnScale x ^ 4) := by
  have hscale (x : keepRecursion.Return) :
      keepGateScale (keepResumeInput x) = keepReturnScale x := by
    rcases x with ⟨⟨⟨n, m, c⟩, h⟩, result⟩
    cases c with
    | outputs _ => cases h
    | gate _ _ _ => rfl
  source_fun_prop
  · simp only [hscale, Dominated.add_iff]
    exact ⟨Dominated.const_of_pos 1 (fun _ => Nat.pow_pos (Nat.succ_pos _)),
      Dominated.refl _⟩
  · simp only [hscale]
    exact Dominated.of_le fun _ => max_le (Nat.le_add_right ..) (Nat.le_add_left ..)

theorem keepScale_next_le (x : KeepInput) : keepScale (keepNextFn x) ≤ keepScale x := by
  rcases x with ⟨n, m, c⟩
  cases c <;> simp -implicitDefEqProofs only [keepNextFn, keepScale, Circuit.size_gate] <;> omega

theorem size_encode_keepFn_le (x : KeepInput) : ⌜keepFn x⌝ₜ.size ≤ 100 * keepScale x ^ 2 := by
  rcases x with ⟨n, m, c⟩
  have h := c.keepInputs.size_encode_numeric_le
  simp -implicitDefEqProofs only [Circuit.size_keepInputs] at h
  apply h.trans
  simpa -implicitDefEqProofs only [pow_two, Nat.mul_assoc] using Nat.mul_le_mul
    (Nat.mul_le_mul_left 100 (by dsimp [keepScale]; omega :
      c.size + (n + m) + 1 ≤ keepScale ⟨n, m, c⟩))
    (by dsimp [keepScale]; omega : n + c.size + 1 ≤ keepScale ⟨n, m, c⟩)

@[source_growth] theorem keepCheck_growth : keepCheck.HasGrowth
    (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  · exact Dominated.const_of_pos _ (fun _ => Nat.zero_lt_one)
  · apply Dominated.of_le
    rintro ⟨n, m, c⟩
    cases c <;> simp <;> omega

@[source_growth] theorem keepNext_growth : keepNext.HasGrowth
    (fun x => ⌜x⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) := by
  let output (x : Σ n, Σ m, (Fin m → Fin n)) : KeepInput :=
    ⟨x.1, x.2.1, .outputs x.2.2⟩
  let gate (x : Σ n, Σ m, Σ a, FirstOrder.Language.booleanAlgebra.Functions a ×
      (Fin a → Fin n) × Circuit .booleanAlgebra (n + 1) m) : KeepInput :=
    ⟨x.1, x.2.1, .gate x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2⟩
  have cover x : (∃ y, output y = x) ∨ ∃ y, gate y = x := by
    rcases x with ⟨n, m, c⟩
    cases c with
    | outputs w => exact Or.inl ⟨⟨n, m, w⟩, rfl⟩
    | gate op args next => exact Or.inr ⟨⟨n, m, _, op, args, next⟩, rfl⟩
  source_fun_prop
  all_goals
    apply Dominated.of_cover output gate cover
    all_goals
      dsimp only [Function.comp_def, output, gate]
      try source_fun_prop
      simp only [Function.comp_apply, Dominated.add_iff, Dominated.max_iff]
      repeat' apply And.intro
  all_goals with_reducible first
    | exact Dominated.const_of_pos _ (fun _ => Tree.size_pos _)
    | apply Dominated.of_le
      rintro ⟨n, m, a, op, args, next⟩
      simp only [Sigma.encode_mk, size_encode_prod, Tree.encode_self,
        Circuit.encode_gate, size_encode_unit]
      omega
    | apply Dominated.of_le
      rintro ⟨n, m, w⟩
      simp only [Sigma.encode_mk, size_encode_prod, Circuit.encode_outputs, size_encode_unit]
      omega
    | apply Dominated.of_le_mul 6
      rintro ⟨n, m, a, op, args, next⟩
      have h := size_encode_nat_succ_le n
      simp only [Sigma.encode_mk, size_encode_prod, Tree.encode_self,
        Circuit.encode_gate, size_encode_unit]
      omega

@[source_growth] theorem keepFinish_growth : keepFinish.HasGrowth
    (fun x => (x.1.1 + x.1.2.1 + 1) ^ 2) (fun x => (x.1.1 + x.1.2.1 + 1) ^ 2) := by
  let input (x : KeepOutputsInput) : {x // keepTest x = false} :=
    ⟨⟨x.1, x.2.1, .outputs x.2.2⟩, rfl⟩
  have hi : Function.Surjective input := by
    rintro ⟨⟨n, m, c⟩, h⟩
    cases c with
    | outputs w => exact ⟨⟨n, m, w⟩, rfl⟩
    | gate op args next => cases h
  have hinput : Dominated (fun x : KeepOutputsInput => ⌜input x⌝ₜ.size)
      (fun x => (x.1 + x.2.1 + 1) ^ 2) := by
    have hc := Dominated.const_of_pos (g := fun x : KeepOutputsInput =>
      (x.1 + x.2.1 + 1) ^ 2) 2 (fun _ => Nat.pow_pos (Nat.succ_pos _))
    apply (keepOutputs_input_growth.add_same hc).mono_left
    rintro ⟨n, m, w⟩
    simp only [input, UniqueEncoding.encode_subtype, Sigma.encode_mk,
      Circuit.encode_outputs, size_encode_unit, size_encode_prod]
    omega
  source_fun_prop
  all_goals
    apply Dominated.of_comp_surjective input hi
    dsimp only [Function.comp_def, input]
    simp only [Dominated.add_iff, Dominated.max_iff]
    repeat' apply And.intro
    all_goals first
      | exact hinput
      | exact keepOutputs_input_growth
      | exact Dominated.refl _
      | exact Dominated.const_of_pos _ (fun _ => Nat.pow_pos (Nat.succ_pos _))

theorem keep_cost_growth :
    let bc : Bounds KeepInput := ⟨fun _ => 1, fun x => ⌜x⌝ₜ.size⟩
    let bs : Bounds KeepInput :=
      ⟨fun x => ⌜x⌝ₜ.size, fun x => ⌜x⌝ₜ.size⟩
    let bd : Bounds {x // keepRecursion.test x = false} :=
      ⟨fun x => (x.1.1 + x.1.2.1 + 1) ^ 2,
       fun x => (x.1.1 + x.1.2.1 + 1) ^ 2⟩
    let br : Bounds keepRecursion.Return :=
      ⟨fun x => keepReturnScale x ^ 7, fun x => ⌜x⌝ₜ.size + keepReturnScale x ^ 4⟩
    Dominated (fun x => (keepRecursion.cost bc bs bd br x).time)
      (fun x => x.2.2.size * keepScale x ^ 7 + keepScale x ^ 2) ∧
    Dominated (fun x => (keepRecursion.cost bc bs bd br x).peak)
      (fun x => keepScale x ^ 4 + (x.2.2.size + 1) * (keepScale x ^ 2 + 1)) := by
  dsimp only
  let I (a x : KeepInput) := keepScale x ≤ keepScale a
  let Z := {p : KeepInput × KeepInput // I p.1 p.2}
  let R (z : Z) := keepScale z.1.1
  let s (z : Z) := ⌜z.1.2⌝ₜ.size
  let o (z : Z) := ⌜keepFn (keepNextFn z.1.2)⌝ₜ.size
  have hR (z : Z) : 0 < R z := keepScale_pos _
  have hsize : Dominated s (fun z => R z ^ 2) := Dominated.of_le_mul 128 fun z => by
    rcases z with ⟨⟨a, ⟨n, m, c⟩⟩, hz⟩
    have h := keep_input_size_le n m c (keepScale a - 1)
      (by dsimp [I, keepScale] at hz; dsimp [keepScale]; omega)
    simpa -implicitDefEqProofs only [s, R, Nat.sub_add_cancel (keepScale_pos a)] using h
  have hout : Dominated o (fun z => R z ^ 2) := Dominated.of_le_mul 100 fun z =>
    (size_encode_keepFn_le _).trans (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_left ((keepScale_next_le _).trans z.2) 2))
  have hdims : Dominated (fun z : Z => z.1.2.1 + z.1.2.2.1 + 1) R :=
    Dominated.of_le fun z => by
      have hz := z.2
      dsimp [I, keepScale, R] at hz ⊢
      omega
  have hfinish := hdims.pow 2
  let Step := {z : Z // keepRecursion.test z.1.2 = true}
  let u (z : Step) : keepRecursion.Return := ⟨⟨z.1.1.2, z.2⟩, keepFn (keepNextFn z.1.1.2)⟩
  have hscale : Dominated (fun z => keepReturnScale (u z)) (fun z : Step => R z.1) :=
    Dominated.of_le fun z => by
      rcases z with ⟨⟨⟨a, ⟨n, m, c⟩⟩, hi⟩, ht⟩
      cases c with
      | outputs w => cases ht
      | gate op args next =>
        change n + m + next.keepInputs.size + 1 ≤ keepScale a
        rw [Circuit.size_keepInputs]
        dsimp [I, keepScale, R] at hi ⊢
        omega
  have hreturnSize : Dominated (fun z => ⌜u z⌝ₜ.size) (fun z : Step => R z.1 ^ 2) := by
    have eq : (fun z : Step => ⌜u z⌝ₜ.size) = (fun z => 1 + s z.1 + o z.1) := by
      funext z
      change 1 + ⌜z.1.1.2⌝ₜ.size + ⌜keepFn (keepNextFn z.1.1.2)⌝ₜ.size = _
      rfl
    rw [eq]
    exact Dominated.comp (((dominated_one_pow R hR 2).add_same hsize).add_same hout)
      (Subtype.val : Step → Z)
  have hrp := (hreturnSize.mono_pow (by decide : 2 ≤ 4) (fun z => hR z.1)).add_same
    (hscale.pow 4)
  refine keepRecursion.dominated_cost_of_bounds _ _ _ _ I id
    (fun x => keepScale x ^ 2) (fun x => keepScale x ^ 2)
    (fun x => keepScale x ^ 7) (fun x => keepScale x ^ 4)
    (fun _ => le_rfl) (fun a x hx _ => (keepScale_next_le x).trans hx) hsize
    (hsize.mono_pow (by decide) hR) (hsize.mono_pow (by decide) hR)
    (Dominated.comp (Dominated.mono_pow hfinish (by decide) hR) Subtype.val)
    hrp (Dominated.comp hfinish Subtype.val) (hsize.mono_pow (by decide) hR)
    (Dominated.const_of_pos 1 fun z => Nat.pow_pos (hR z)) (hscale.pow 7)
    (fun _ => Nat.pow_pos (keepScale_pos _)) (fun _ => Nat.pow_pos (keepScale_pos _))

theorem keep_structural_growth : keepImplementation.HasGrowth
    (fun x => 1 + (x.2.2.size * keepScale x ^ 7 + keepScale x ^ 2) + 1)
    (fun x => (keepScale x ^ 4 + (x.2.2.size + 1) * (keepScale x ^ 2 + 1)) + 1) :=
  keepRecursion.hasGrowth_of_growth keepCheck_growth keepNext_growth
    keepFinish_growth keepResume_saved_growth keep_cost_growth

@[source_growth] theorem keep_growth : keepImplementation.HasGrowth
    (fun x => keepScale x ^ 8) (fun x => keepScale x ^ 4) := by
  have hg : Dominated (fun x : KeepInput => x.2.2.size) keepScale :=
    Dominated.of_le fun x => by dsimp [keepScale]; omega
  have hg' := hg.add_same (Dominated.one keepScale_pos)
  have ht : Dominated (fun x => x.2.2.size * keepScale x ^ 7)
      (fun x => keepScale x ^ 8) := by
    simpa -implicitDefEqProofs only [pow_succ, Nat.mul_comm] using
      hg.mul ((Dominated.refl keepScale).pow 7)
  have hs : Dominated (fun x => (x.2.2.size + 1) * (keepScale x ^ 2 + 1))
      (fun x => keepScale x ^ 3) := by
    simpa -implicitDefEqProofs only [pow_succ, Nat.mul_comm] using hg'.mul
      (((Dominated.refl keepScale).pow 2).add_same
        (dominated_one_pow keepScale keepScale_pos 2))
  apply keep_structural_growth.mono
  · simp only [Dominated.add_iff]
    exact ⟨⟨Dominated.const_of_pos 1 (fun _ => Nat.pow_pos (keepScale_pos _)),
      ⟨ht, Dominated.pow_of_le (Dominated.refl _) (by decide) keepScale_pos⟩⟩,
      Dominated.const_of_pos 1 (fun _ => Nat.pow_pos (keepScale_pos _))⟩
  · simp only [Dominated.add_iff]
    exact ⟨⟨Dominated.refl _,
      Dominated.mono_pow hs (by decide : 3 ≤ 4) keepScale_pos⟩,
      Dominated.const_of_pos 1 (fun _ => Nat.pow_pos (keepScale_pos _))⟩

noncomputable def Implementation.keepInputs {ρ : Type} [UniqueEncoding Tree ρ]
    {n m : ρ → ℕ} {c : (x : ρ) → Circuit .booleanAlgebra (n x) (m x)}
    (h : Implementation (fun x => (⟨n x, m x, c x⟩ : KeepInput))) :
    Implementation (fun x => ⌜(c x).keepInputs⌝ₜ) :=
  h.comp keepImplementation

@[simp, source_bounds↓] theorem Implementation.bounds_keepInputs
    {ρ : Type} [UniqueEncoding Tree ρ]
    {n m : ρ → ℕ} {c : (x : ρ) → Circuit .booleanAlgebra (n x) (m x)}
    (h : Implementation (fun x => (⟨n x, m x, c x⟩ : KeepInput))) :
    (Implementation.keepInputs h).bounds =
      compBounds (fun x => (⟨n x, m x, c x⟩ : KeepInput)) h.bounds keepImplementation.bounds :=
  Implementation.bounds_comp _ _

attribute [scoped fun_prop] Implementation.keepInputs

end Complexity.TreeProgram.Source
