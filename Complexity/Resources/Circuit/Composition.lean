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

end Complexity.Circuit

namespace Complexity.TreeProgram.Source

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

noncomputable def relabelCheck : Implementation relabelTest :=
  (show Realizes relabelTest ⟨fun _ => 10, fun x => ⌜x⌝ₜ.size⟩ from by
    source_fun_prop).implementation

theorem relabelNext_realizes : Realizes relabelNextFn
    ⟨fun x => 1000 * (⌜x⌝ₜ.size + 1), fun x => 1000 * (⌜x⌝ₜ.size + 1)⟩ := by
  refine Realizes.mono (by source_fun_prop) ?_
  rintro ⟨n, m, k, c, wires⟩
  have hn := card_le_size_encode_fin_function wires
  have hb := length_le_codeSize n.bits
  have hk := length_le_codeSize k.bits
  have hs := size_encode_nat_succ_le n
  have hs' := size_encode_nat_succ_le k
  have ha := size_encode_list_append (List.ofFn (Fin.castSucc ∘ wires)) [Fin.last k]
  simp only [← encode_fin_function, encode_fin_castSucc, encode_list_cons, encode_list_nil,
    size_encode_prod, size_encode_unit, encode_fin, Fin.val_last] at ha
  cases c <;> dsimp only <;>
    simp only [compBounds, pairBounds, Sigma.encode_mk,
      size_encode_prod, Tree.encode_self, Circuit.liftInputs, encode_fin_snoc,
      encode_fin_castSucc, Circuit.encode_outputs, Circuit.encode_gate, size_encode_unit,
      encode_fin, Fin.val_last, encode_nat_tree, max_le_iff] at * <;>
    (repeat' apply And.intro) <;> omega

noncomputable def relabelNext : Implementation relabelNextFn := relabelNext_realizes.implementation

attribute [local fun_prop] Realizes.finComp in
theorem relabelFinish_realizes : Realizes (fun x => ⌜relabelFinishFn x⌝ₜ)
    ⟨fun x => 1000000 * (⌜x⌝ₜ.size + 1) ^ 3,
     fun x => 1000000 * (⌜x⌝ₜ.size + 1) ^ 2⟩ := by
  refine Realizes.mono (by source_fun_prop) ?_
  rintro ⟨⟨n, m, k, c, wires⟩, h⟩
  cases c with
  | outputs select =>
    dsimp only
    simp only [compBounds, pairBounds]
    let N := ⌜(n, m, k, (Circuit.outputs select : Circuit .booleanAlgebra n m), wires)⌝ₜ.size
    have hn : 1 + ⌜m⌝ₜ.size + (1 + ⌜n⌝ₜ.size +
        (1 + ⌜k⌝ₜ.size + (1 + ⌜select⌝ₜ.size + ⌜wires⌝ₜ.size))) ≤ N := by
      simp only [N, Circuit.encode_outputs, size_encode_prod, size_encode_unit] at *; omega
    have h₂ := pow_le_pow_left' (Nat.add_le_add_right hn 1) 2
    have h₃ := pow_le_pow_left' (Nat.add_le_add_right hn 1) 3
    have hN₂ := Nat.le_self_pow (by decide : 2 ≠ 0) (N + 1)
    have hN₃ := Nat.le_self_pow (by decide : 3 ≠ 0) (N + 1)
    have hout := size_encode_fin_function_le (wires ∘ select) ⌜wires⌝ₜ.size
      (fun i => size_encode_fin_apply_le wires (select i))
    have hm := card_le_size_encode_fin_function select
    have hf : ⌜wires⌝ₜ.size ≤ N := by
      simp only [N, Circuit.encode_outputs, size_encode_prod, size_encode_unit] at *
      omega
    have hmN : m ≤ N := by
      simp only [N, Circuit.encode_outputs, size_encode_prod, size_encode_unit] at *
      omega
    have ho : ⌜wires ∘ select⌝ₜ.size ≤ (N + 1) ^ 2 := by
      exact hout.trans
        ((Nat.add_le_add_right (Nat.mul_le_mul hmN (Nat.add_le_add_right hf 1)) 1).trans
          (by simp only [pow_two, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]; omega))
    simp only [UniqueEncoding.encode_subtype, Sigma.encode_mk, Circuit.encode_outputs,
      size_encode_prod, size_encode_unit, Tree.encode_self, identityBounds, max_le_iff]
    simp only [N, Circuit.encode_outputs, size_encode_prod, size_encode_unit] at h₂ h₃ hN₂ hN₃ ho
    (repeat' apply And.intro) <;> omega
  | gate op args next => cases h
attribute [local fun_prop] Realizes.finComp in
theorem relabelResume_realizes :
    Realizes (fun x : relabelRecursion.Return => ⌜relabelResumeFn x.1 x.2⌝ₜ)
    ⟨fun x => 1000000 * (⌜x⌝ₜ.size + 1) ^ 3,
     fun x => 1000000 * (⌜x⌝ₜ.size + 1) ^ 2⟩ := by
  refine Realizes.mono (by source_fun_prop) ?_
  rintro ⟨⟨⟨n, m, k, c, wires⟩, h⟩, result⟩
  cases c with
  | outputs select => cases h
  | @gate _ _ arity op args next =>
    dsimp only
    simp only [compBounds, pairBounds,
      UniqueEncoding.encode_subtype, Sigma.encode_mk, size_encode_prod,
      Tree.encode_self, identityBounds]
    dsimp +instances only [id, relabelRecursion, relabelNextFn] at *
    let N := 1 + ⌜(n, m, k, Circuit.gate op args next, wires)⌝ₜ.size +
      ⌜result⌝ₜ.size
    have hn : 1 + ⌜arity⌝ₜ.size + (1 + ⌜n⌝ₜ.size +
        (1 + ⌜k⌝ₜ.size + (1 + ⌜args⌝ₜ.size + ⌜wires⌝ₜ.size))) ≤ N := by
      simp only [N, Circuit.encode_gate, size_encode_prod, size_encode_unit]; omega
    have h₂ := pow_le_pow_left' (Nat.add_le_add_right hn 1) 2
    have h₃ := pow_le_pow_left' (Nat.add_le_add_right hn 1) 3
    have hN₂ := Nat.le_self_pow (by decide : 2 ≠ 0) (N + 1)
    have hN₃ := Nat.le_self_pow (by decide : 3 ≠ 0) (N + 1)
    have hf : ⌜args⌝ₜ.size ≤ N := by
      simp only [N, Circuit.encode_gate, size_encode_prod, size_encode_unit]; omega
    have hg : ⌜wires⌝ₜ.size ≤ N := by
      simp only [N, Circuit.encode_gate, size_encode_prod, size_encode_unit]; omega
    have ho : ⌜wires ∘ args⌝ₜ.size ≤ (N + 1) ^ 2 :=
      (size_encode_fin_comp_le args wires).trans
        ((Nat.add_le_add_right (Nat.mul_le_mul hf (Nat.add_le_add_right hg 1)) 1).trans
          (by simp only [pow_two, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]; omega))
    simp only [N, Circuit.encode_gate, size_encode_prod, size_encode_unit, max_le_iff]
      at h₂ h₃ hN₂ hN₃ ho ⊢
    dsimp +instances only [id, relabelRecursion, relabelNextFn] at *
    (repeat' apply And.intro) <;> omega

noncomputable def relabelFinish : Implementation (fun x => ⌜relabelFinishFn x⌝ₜ) :=
  relabelFinish_realizes.implementation
noncomputable def relabelResume : Implementation
    (fun x : relabelRecursion.Return => ⌜relabelResumeFn x.1 x.2⌝ₜ) :=
  relabelResume_realizes.implementation
noncomputable def relabelImplementation : Implementation (fun x => ⌜relabelFn x⌝ₜ) :=
  relabelRecursion.implementation relabelCheck relabelNext relabelFinish relabelResume
private theorem relabel_input_size_le (n m k : ℕ) (c : Circuit .booleanAlgebra n m)
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

private theorem relabel_cost_numeric_le (N : ℕ) (x : RelabelInput)
    (hx : x.1 + x.2.1 + x.2.2.1 + 2 * x.2.2.2.1.size ≤ N) :
    let bc : Bounds RelabelInput := ⟨fun _ => 10, fun x => ⌜x⌝ₜ.size⟩
    let bs : Bounds RelabelInput := ⟨fun x => 1000 * (⌜x⌝ₜ.size + 1),
      fun x => 1000 * (⌜x⌝ₜ.size + 1)⟩
    let bd : Bounds {x // relabelRecursion.test x = false} :=
      ⟨fun x => 1000000 * (⌜x⌝ₜ.size + 1) ^ 3, fun x => 1000000 * (⌜x⌝ₜ.size + 1) ^ 2⟩
    let br : Bounds relabelRecursion.Return :=
      ⟨fun x => 1000000 * (⌜x⌝ₜ.size + 1) ^ 3, fun x => 1000000 * (⌜x⌝ₜ.size + 1) ^ 2⟩
    (relabelRecursion.cost bc bs bd br x).time ≤
        (x.2.2.2.1.size + 1) * (100000000000000 * (N + 1) ^ 6) ∧
      (relabelRecursion.cost bc bs bd br x).peak ≤
        1000000000000 * (N + 1) ^ 4 +
          (x.2.2.2.1.size + 1) * (128 * (N + 1) ^ 2 + 1) := by
  let R := N + 1
  have hR : 1 ≤ R := by dsimp [R]; omega
  have hp₂ : 1 ≤ R ^ 2 := Nat.one_le_pow 2 R hR
  have hp₄ : R ^ 2 ≤ R ^ 4 := Nat.pow_le_pow_right hR (by decide)
  have hp₆ : R ^ 2 ≤ R ^ 6 := Nat.pow_le_pow_right hR (by decide)
  have budget (s : ℕ) (hs : s ≤ 256 * R ^ 2) :
      1000000 * (s + 1) ^ 3 + 1000 * (128 * R ^ 2 + 1) + 26 ≤ 100000000000000 * R ^ 6 ∧
      1000000 * (s + 1) ^ 2 ≤ 1000000000000 * R ^ 4 := by
    have h : s + 1 ≤ 257 * R ^ 2 := by omega
    have h₂ := pow_le_pow_left' h 2
    have h₃ := pow_le_pow_left' h 3
    norm_num [mul_pow, ← pow_mul] at h₂ h₃
    constructor <;> omega
  apply relabelRecursion.cost_le_of_invariant _ _ _ _
    (fun y => y.1 + y.2.1 + y.2.2.1 + 2 * y.2.2.2.1.size ≤ N)
    (128 * R ^ 2) (100000000000000 * R ^ 6) (1000000000000 * R ^ 4)
    ?_ ?_ ?_ ?_ x hx
  · rintro ⟨n, m, k, c, w⟩ h
    exact relabel_input_size_le n m k c w N h
  · rintro ⟨n, m, k, c, w⟩ h
    have hs := relabel_input_size_le n m k c w N h
    dsimp only
    change _ ≤ 1000000000000 * R ^ 4
    change _ ≤ 128 * R ^ 2 at hs
    omega
  · rintro ⟨n, m, k, c, w⟩ h hy
    have hs := relabel_input_size_le n m k c w N hy
    have hb := budget ⌜(⟨n, m, k, c, w⟩ : RelabelInput)⌝ₜ.size
      (by change _ ≤ 128 * R ^ 2 at hs; omega)
    dsimp only
    simp only [UniqueEncoding.encode_subtype]
    change _ ≤ _ ∧ _ ≤ 1000000000000 * R ^ 4
    constructor <;> omega
  · rintro ⟨n, m, k, c, w⟩ h hy
    cases c with
    | outputs select => cases h
    | gate op args next =>
      have hs := relabel_input_size_le n m k (.gate op args next) w N hy
      have hi : n + 1 + m + (k + 1) + 2 * next.size ≤ N := by
        simp only [Circuit.size_gate] at hy
        omega
      have ho := (next.relabel (Circuit.liftInputs w)).size_encode_numeric_le
      simp only [Circuit.size_relabel] at ho
      have hout : ⌜next.relabel (Circuit.liftInputs w)⌝ₜ.size ≤ 100 * R ^ 2 := ho.trans (by
        simpa only [pow_two, Nat.mul_assoc] using Nat.mul_le_mul
          (Nat.mul_le_mul_left 100 (by dsimp [R]; omega : next.size + m + 1 ≤ R))
          (by dsimp [R]; omega : k + 1 + next.size + 1 ≤ R))
      have harg : 1 + ⌜(⟨n, m, k, .gate op args next, w⟩ : RelabelInput)⌝ₜ.size +
          ⌜next.relabel (Circuit.liftInputs w)⌝ₜ.size ≤ 256 * R ^ 2 := by
        change _ ≤ 128 * R ^ 2 at hs
        omega
      have hb := budget _ harg
      change _ ≤ 128 * R ^ 2 at hs
      refine ⟨hi, ?_, ?_, ?_⟩
      · change 1000 * (⌜(⟨n, m, k, .gate op args next, w⟩ : RelabelInput)⌝ₜ.size + 1) ≤ _
        omega
      · change 1000000 * (1 + ⌜(⟨n, m, k, .gate op args next, w⟩ : RelabelInput)⌝ₜ.size +
          ⌜next.relabel (Circuit.liftInputs w)⌝ₜ.size + 1) ^ 2 ≤ _
        exact hb.2
      · change 1000 * (⌜(⟨n, m, k, .gate op args next, w⟩ : RelabelInput)⌝ₜ.size + 1) + 10 +
          1000000 * (1 + ⌜(⟨n, m, k, .gate op args next, w⟩ : RelabelInput)⌝ₜ.size +
            ⌜next.relabel (Circuit.liftInputs w)⌝ₜ.size + 1) ^ 3 + 16 ≤ _
        omega

/-- Numeric allowances for the same recursive relabeling program, including its saved callers. -/
@[simps] def relabelBounds : Bounds RelabelInput :=
  let N (x : RelabelInput) := x.1 + x.2.1 + x.2.2.1 + 2 * x.2.2.2.1.size + 1
  ⟨fun x => 300000000000000 * (x.2.2.2.1.size + 1) * N x ^ 6 + 20,
   fun x => 1000000000000 * N x ^ 4 +
     (x.2.2.2.1.size + 1) * (128 * N x ^ 2 + 1) + 1⟩

theorem relabel_bounds_le (x : RelabelInput) :
    relabelImplementation.bounds.time x ≤ relabelBounds.time x ∧
      relabelImplementation.bounds.peak x ≤ relabelBounds.peak x := by
  rcases x with ⟨n, m, k, c, w⟩
  have hc := relabel_cost_numeric_le (n + m + k + 2 * c.size) ⟨n, m, k, c, w⟩ le_rfl
  dsimp only at hc
  constructor
  · calc
      _ ≤ 10 + 3 * ((c.size + 1) *
          (100000000000000 * (n + m + k + 2 * c.size + 1) ^ 6)) + 10 :=
        Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left 3 hc.1) 10) 10
      _ = _ := by
        dsimp only [relabelBounds]
        ring
  · exact Nat.add_le_add_right hc.2 1


@[scoped fun_prop] theorem relabel_realizes {ρ : Type} [UniqueEncoding Tree ρ]
    {n m k : ρ → ℕ}
    {c : (x : ρ) → Circuit .booleanAlgebra (n x) (m x)}
    {w : (x : ρ) → Fin (n x) → Fin (k x)} {b : Bounds ρ}
    (h : Realizes (fun x => (⟨n x, m x, k x, c x, w x⟩ : RelabelInput)) b) :
    Realizes (fun x => ⌜(c x).relabel (w x)⌝ₜ)
      (compBounds (fun x => (⟨n x, m x, k x, c x, w x⟩ : RelabelInput)) b
        relabelBounds) :=
  h.comp (relabelImplementation.realizes.mono relabel_bounds_le)

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


def compFinishBounds : Bounds {x // compRecursion.test x = false} :=
  let N x := x.1.1 + x.1.2.1 + x.1.2.2.1 + 2 * x.1.2.2.2.2.size + 1
  ⟨fun x => 300000000000000 * (x.1.2.2.2.2.size + 1) * N x ^ 6 + 100,
   fun x => max (2 * ⌜x⌝ₜ.size)
      (1000000000000 * N x ^ 4 +
        (x.1.2.2.2.2.size + 1) * (128 * N x ^ 2 + 1) + 1)⟩

theorem compCheck_realizes : Realizes compTest ⟨fun _ => 10, fun x => ⌜x⌝ₜ.size⟩ := by
  source_fun_prop
theorem compNext_realizes : Realizes compNextFn
    ⟨fun x => 1000 * (⌜x⌝ₜ.size + 1), fun x => 1000 * (⌜x⌝ₜ.size + 1)⟩ := by
  refine Realizes.mono (by source_fun_prop) ?_
  rintro ⟨n, m, k, c, d⟩
  have hn := length_le_codeSize n.bits
  have hs := size_encode_nat_succ_le n
  cases c <;> dsimp +instances only <;>
    simp only [compBounds, pairBounds, Sigma.encode_mk, size_encode_prod,
      Circuit.encode_outputs, Circuit.encode_gate, size_encode_unit, encode_nat_tree,
      Tree.encode_self, max_le_iff] at * <;>
    (repeat' apply And.intro) <;> omega
theorem compResume_realizes : Realizes (fun x : compRecursion.Return => ⌜compResumeFn x.1 x.2⌝ₜ)
    ⟨fun _ => 1000, fun x => 1000 * (⌜x⌝ₜ.size + 1)⟩ := by
  refine Realizes.mono (by source_fun_prop) ?_
  rintro ⟨⟨⟨n, m, k, c, d⟩, h⟩, result⟩
  cases c with
  | outputs select => cases h
  | gate op args next =>
    change _ ≤ 1000 ∧ _ ≤ 1000 *
      (1 + ⌜(n, m, k, Circuit.gate op args next, d)⌝ₜ.size + ⌜result⌝ₜ.size + 1)
    dsimp +instances only [id, compRecursion, compNextFn, Recursion.Return, compTest, compFn]
    simp only [Sigma.encode_mk, size_encode_prod,
      Circuit.encode_gate, size_encode_unit, Tree.encode_self]
    erw [Sigma.encode_mk, size_encode_prod, UniqueEncoding.encode_subtype]
    simp +instances only [Sigma.encode_mk, size_encode_prod,
      Circuit.encode_gate, size_encode_unit, max_le_iff]
    repeat' first
      | erw [Circuit.encode_gate]
      | erw [Sigma.encode_mk]
      | erw [size_encode_prod]
      | rw [size_encode_unit]
    (repeat' apply And.intro) <;> omega

theorem compFinish_realizes : Realizes (fun x => ⌜compFinishFn x⌝ₜ) compFinishBounds := by
  refine Realizes.mono (by source_fun_prop) ?_
  rintro ⟨⟨n, m, k, c, d⟩, h⟩
  cases c with
  | outputs select =>
    dsimp +instances only
    simp only [compBounds, Realizes.bounds_implementation, compFinishBounds, relabelBounds,
      UniqueEncoding.encode_subtype,
      Sigma.encode_mk, size_encode_prod, Circuit.encode_outputs, size_encode_unit,
      Realizes.bounds_implementation]
    have he : m + k + n + 2 * d.size + 1 = n + m + k + 2 * d.size + 1 := by omega
    simp only [he, max_le_iff]
    (repeat' apply And.intro) <;> omega
  | gate op args next => cases h

noncomputable def compCheck : Implementation compTest := compCheck_realizes.implementation
noncomputable def compNext : Implementation compNextFn := compNext_realizes.implementation
noncomputable def compFinish : Implementation (fun x => ⌜compFinishFn x⌝ₜ) :=
  compFinish_realizes.implementation
noncomputable def compResume : Implementation
    (fun x : compRecursion.Return => ⌜compResumeFn x.1 x.2⌝ₜ) := compResume_realizes.implementation

noncomputable def compImplementation : Implementation (fun x => ⌜compFn x⌝ₜ) :=
  compRecursion.implementation compCheck compNext compFinish compResume

private theorem comp_input_size_le (n m k : ℕ) (c : Circuit .booleanAlgebra n m)
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

private theorem comp_cost_numeric_le (N : ℕ) (x : CompInput)
    (hx : x.1 + x.2.1 + x.2.2.1 + 2 * (x.2.2.2.1.size + x.2.2.2.2.size) ≤ N) :
    let bc : Bounds CompInput := ⟨fun _ => 10, fun x => ⌜x⌝ₜ.size⟩
    let bs : Bounds CompInput :=
      ⟨fun x => 1000 * (⌜x⌝ₜ.size + 1), fun x => 1000 * (⌜x⌝ₜ.size + 1)⟩
    let br : Bounds compRecursion.Return :=
      ⟨fun _ => 1000, fun x => 1000 * (⌜x⌝ₜ.size + 1)⟩
    (compRecursion.cost bc bs compFinishBounds br x).time ≤
        (x.2.2.2.1.size + 1) * (1000000000000000 * (N + 1) ^ 7) ∧
      (compRecursion.cost bc bs compFinishBounds br x).peak ≤
        10000000000000 * (N + 1) ^ 4 +
          (x.2.2.2.1.size + 1) * (256 * (N + 1) ^ 2 + 1) := by
  let R := N + 1
  have hR : 1 ≤ R := by dsimp [R]; omega
  have h₂ : 1 ≤ R ^ 2 := Nat.one_le_pow 2 _ hR
  have h₂₄ : R ^ 2 ≤ R ^ 4 := Nat.pow_le_pow_right hR (by decide)
  have h₂₇ : R ^ 2 ≤ R ^ 7 := Nat.pow_le_pow_right hR (by decide)
  have h₃₄ : R ^ 3 ≤ R ^ 4 := Nat.pow_le_pow_right hR (by decide)
  refine compRecursion.cost_le_of_invariant _ _ _ _
    (fun y => y.1 + y.2.1 + y.2.2.1 + 2 * (y.2.2.2.1.size + y.2.2.2.2.size) ≤ N)
    (256 * R ^ 2) (1000000000000000 * R ^ 7) (10000000000000 * R ^ 4)
    ?_ ?_ ?_ ?_ x hx
  · rintro ⟨n, m, k, c, d⟩ hy
    exact comp_input_size_le n m k c d N hy
  · rintro ⟨n, m, k, c, d⟩ hy
    have hs := comp_input_size_le n m k c d N hy
    change _ ≤ 256 * R ^ 2 at hs
    change ⌜(⟨n, m, k, c, d⟩ : CompInput)⌝ₜ.size ≤ _
    omega
  · rintro ⟨n, m, k, c, d⟩ h hy
    dsimp only at hy
    have hs := comp_input_size_le n m k c d N hy
    change _ ≤ 256 * R ^ 2 at hs
    have hw : n + m + k + 2 * d.size + 1 ≤ R := by dsimp [R]; omega
    have hd : d.size + 1 ≤ R := by dsimp [R]; omega
    have h₄ := pow_le_pow_left' hw 4
    have hW₂ := pow_le_pow_left' hw 2
    have ht : (d.size + 1) * (n + m + k + 2 * d.size + 1) ^ 6 ≤ R ^ 7 := calc
      _ ≤ R * R ^ 6 := Nat.mul_le_mul hd (pow_le_pow_left' hw 6)
      _ = _ := by rw [pow_succ R 6]; ac_rfl
    have hstack : (d.size + 1) *
        (128 * (n + m + k + 2 * d.size + 1) ^ 2 + 1) ≤ 129 * R ^ 3 := calc
      _ ≤ R * (129 * R ^ 2) := Nat.mul_le_mul hd (by omega)
      _ = _ := by rw [pow_succ R 2]; ac_rfl
    constructor
    · change 300000000000000 * (d.size + 1) * (n + m + k + 2 * d.size + 1) ^ 6 + 100 + 2 ≤ _
      rw [Nat.mul_assoc]
      omega
    · change max (2 * ⌜(⟨n, m, k, c, d⟩ : CompInput)⌝ₜ.size)
        (1000000000000 * (n + m + k + 2 * d.size + 1) ^ 4 +
          (d.size + 1) * (128 * (n + m + k + 2 * d.size + 1) ^ 2 + 1) + 1) ≤ _
      exact max_le (by omega) (by omega)
  · rintro ⟨n, m, k, c, d⟩ h hy
    dsimp only at hy
    have hs := comp_input_size_le n m k c d N hy
    cases c with
    | outputs select => cases h
    | gate op args next =>
      have hi : n + 1 + m + k + 2 * (next.size + d.size) ≤ N := by
        simp only [Circuit.size_gate] at hy
        omega
      have ho := (next.comp d).size_encode_numeric_le
      simp only [Circuit.size_comp] at ho
      have hout : ⌜next.comp d⌝ₜ.size ≤ 100 * R ^ 2 := ho.trans (by
        simpa only [pow_two, Nat.mul_assoc] using Nat.mul_le_mul
          (Nat.mul_le_mul_left 100
            (by dsimp [R]; omega : next.size + d.size + k + 1 ≤ R))
          (by dsimp [R]; omega : n + 1 + (next.size + d.size) + 1 ≤ R))
      change _ ≤ 256 * R ^ 2 at hs
      refine ⟨hi, ?_, ?_, ?_⟩
      · change 1000 * (⌜(⟨n, m, k, .gate op args next, d⟩ : CompInput)⌝ₜ.size + 1) ≤ _
        omega
      · change 1000 * (1 + ⌜(⟨n, m, k, .gate op args next, d⟩ : CompInput)⌝ₜ.size +
          ⌜next.comp d⌝ₜ.size + 1) ≤ _
        omega
      · change 1000 * (⌜(⟨n, m, k, .gate op args next, d⟩ : CompInput)⌝ₜ.size + 1) +
          10 + 1000 + 16 ≤ _
        omega
@[simps] def circuitCompBounds : Bounds CompInput :=
  let N (x : CompInput) := x.1 + x.2.1 + x.2.2.1 + 2 * (x.2.2.2.1.size + x.2.2.2.2.size) + 1
  ⟨fun x => 10000000000000000 * N x ^ 8, fun x => 100000000000000 * N x ^ 4⟩

theorem comp_bounds_le (x : CompInput) :
    compImplementation.bounds.time x ≤ circuitCompBounds.time x ∧
      compImplementation.bounds.peak x ≤ circuitCompBounds.peak x := by
  rcases x with ⟨n, m, k, c, d⟩
  let R := n + m + k + 2 * (c.size + d.size) + 1
  have hc := comp_cost_numeric_le (n + m + k + 2 * (c.size + d.size)) ⟨n, m, k, c, d⟩ le_rfl
  dsimp only at hc
  have hg : c.size + 1 ≤ R := by dsimp [R]; omega
  have hR : 1 ≤ R := by dsimp [R]; omega
  have h₂ : 1 ≤ R ^ 2 := Nat.one_le_pow 2 _ hR
  have h₄ : 1 ≤ R ^ 4 := Nat.one_le_pow 4 _ hR
  have h₈ : 1 ≤ R ^ 8 := Nat.one_le_pow 8 _ hR
  have h₃₄ : R ^ 3 ≤ R ^ 4 := Nat.pow_le_pow_right hR (by decide)
  have ht : (c.size + 1) * R ^ 7 ≤ R ^ 8 := calc
    _ ≤ R * R ^ 7 := Nat.mul_le_mul_right _ hg
    _ = _ := by rw [pow_succ R 7]; ac_rfl
  have hs : (c.size + 1) * (256 * R ^ 2 + 1) ≤ 257 * R ^ 3 := calc
    _ ≤ R * (257 * R ^ 2) := Nat.mul_le_mul hg (by omega)
    _ = _ := by rw [pow_succ R 2]; ac_rfl
  constructor
  · calc
      _ ≤ 10 + 3 * ((c.size + 1) * (1000000000000000 * R ^ 7)) + 10 :=
        Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left 3 hc.1) 10) 10
      _ ≤ 10000000000000000 * R ^ 8 := by
        rw [Nat.mul_left_comm (c.size + 1) 1000000000000000]
        omega
  · calc
      _ ≤ 10000000000000 * R ^ 4 + (c.size + 1) * (256 * R ^ 2 + 1) + 1 :=
        Nat.add_le_add_right hc.2 1
      _ ≤ 100000000000000 * R ^ 4 := by omega

@[scoped fun_prop] theorem comp_realizes {ρ : Type} [UniqueEncoding Tree ρ]
    {n m k : ρ → ℕ}
    {c : (x : ρ) → Circuit .booleanAlgebra (n x) (m x)}
    {d : (x : ρ) → Circuit .booleanAlgebra (m x) (k x)} {b : Bounds ρ}
    (h : Realizes (fun x => (⟨n x, m x, k x, c x, d x⟩ : CompInput)) b) :
    Realizes (fun x => ⌜(c x).comp (d x)⌝ₜ)
      (compBounds (fun x => (⟨n x, m x, k x, c x, d x⟩ : CompInput)) b
        circuitCompBounds) :=
  h.comp (compImplementation.realizes.mono comp_bounds_le)

abbrev KeepInput := Σ n, Σ m, Circuit .booleanAlgebra n m

def keepFn (x : KeepInput) := x.2.2.keepInputs

def keepTest (x : KeepInput) :=
  match x.2.2 with | .outputs _ => false | .gate _ _ _ => true

def keepNextFn : KeepInput → KeepInput
  | ⟨n, m, .gate _ _ next⟩ => ⟨n + 1, m, next⟩
  | x => x

def keepFinishFn : (x : {x // keepTest x = false}) →
    Circuit .booleanAlgebra x.1.1 (x.1.1 + x.1.2.1)
  | ⟨⟨_, _, .outputs select⟩, _⟩ => .outputs (Fin.append id select)
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


def keepResumeBounds : Bounds keepRecursion.Return :=
  let N (x : keepRecursion.Return) := x.1.1.1 + x.1.1.2.1 + x.2.size + 1
  ⟨fun x => 1000000000000000000000 * N x ^ 8,
   fun x => 2 * ⌜x⌝ₜ.size + 1000000000000000000 * N x ^ 4⟩

theorem keepCheck_realizes : Realizes keepTest ⟨fun _ => 10, fun x => ⌜x⌝ₜ.size⟩ := by
  source_fun_prop
theorem keepNext_realizes : Realizes keepNextFn
    ⟨fun x => 1000 * (⌜x⌝ₜ.size + 1), fun x => 1000 * (⌜x⌝ₜ.size + 1)⟩ := by
  refine Realizes.mono (by source_fun_prop) ?_
  rintro ⟨n, m, c⟩
  have hn := length_le_codeSize n.bits
  have hs := size_encode_nat_succ_le n
  cases c <;> dsimp only <;>
    simp only [compBounds, pairBounds, Sigma.encode_mk, size_encode_prod,
      Circuit.encode_outputs, Circuit.encode_gate, size_encode_unit, encode_nat_tree,
      Tree.encode_self, max_le_iff] at * <;>
    (repeat' apply And.intro) <;> omega
theorem keepFinish_realizes : Realizes (fun x => ⌜keepFinishFn x⌝ₜ)
    ⟨fun x => 1000000 * (x.1.1 + x.1.2.1 + 1) ^ 2,
     fun x => 1000000 * (x.1.1 + x.1.2.1 + 1) ^ 2⟩ := by
  refine Realizes.mono (by source_fun_prop using tabulate) ?_
  rintro ⟨⟨n, m, c⟩, h⟩
  cases c with
  | outputs select =>
    dsimp only
    simp only [pairBounds, identityBounds,
      UniqueEncoding.encode_subtype, Sigma.encode_mk, size_encode_prod,
      Circuit.encode_outputs, size_encode_unit, Tree.encode_self]
    have hi (i : Fin n) : ⌜i⌝ₜ.size ≤ 4 * n + 1 := by
      have := size_encode_nat_le i.val
      have := i.isLt
      simpa only [encode_fin] using (by omega : ⌜i.val⌝ₜ.size ≤ 4 * n + 1)
    have hid := size_encode_fin_function_le (id : Fin n → Fin n) (4 * n + 1) hi
    have hselect := size_encode_fin_function_le select (4 * n + 1) (fun i => hi (select i))
    have ho := size_encode_fin_function_le (Fin.append (id : Fin n → Fin n) select)
      (4 * n + 1) (fun i => hi _)
    have hn := size_encode_nat_le n
    have hm := size_encode_nat_le m
    have hr := size_encode_range_le n
    have hN := Nat.le_self_pow (by decide : 2 ≠ 0) (n + m + 1)
    have hp := pow_le_pow_left' (by omega : n + 1 ≤ n + m + 1) 2
    have hsize : ⌜(n, m, select)⌝ₜ.size ≤ 16 * (n + m + 1) ^ 2 := by
      simp only [size_encode_prod]
      nlinarith
    have hmax := (foldr_max_le
      (fun i : Fin n => max ⌜((n, m, select), i)⌝ₜ.size ⌜i⌝ₜ.size) (List.finRange n)
      (32 * (n + m + 1) ^ 2)).mpr (fun i _ => by
        have := hi i
        simp only [max_le_iff, size_encode_prod]
        simp only [size_encode_prod] at hsize
        constructor <;> nlinarith)
    have hid' : ⌜(id : Fin n → Fin n)⌝ₜ.size ≤ 8 * (n + m + 1) ^ 2 := by nlinarith
    have ho' : ⌜Fin.append (id : Fin n → Fin n) select⌝ₜ.size ≤
        8 * (n + m + 1) ^ 2 := by nlinarith
    have hr' : ⌜List.range n⌝ₜ.size ≤ 8 * (n + m + 1) ^ 2 := by nlinarith
    simp only [tabulateBounds, compBounds, pairBounds, identityBounds,
      Sigma.encode_mk, size_encode_prod, List.map_const', List.sum_replicate,
      List.length_finRange, smul_eq_mul, id_eq]
    simp only [size_encode_prod] at hsize hmax
    simp only [← max_assoc, max_le_iff]
    (repeat' apply And.intro) <;> omega
  | gate op args next => cases h

noncomputable def keepCheck : Implementation keepTest := keepCheck_realizes.implementation
noncomputable def keepNext : Implementation keepNextFn := keepNext_realizes.implementation
noncomputable def keepFinish : Implementation (fun x => ⌜keepFinishFn x⌝ₜ) :=
  keepFinish_realizes.implementation
noncomputable def keepResume : Implementation
    (fun x : keepRecursion.Return => ⌜keepResumeFn x.1 x.2⌝ₜ) := by
  source_fun_prop using tabulate

theorem keepResume_realizes :
    Realizes (fun x : keepRecursion.Return => ⌜keepResumeFn x.1 x.2⌝ₜ) keepResumeBounds := by
  refine keepResume.realizes.mono ?_
  rintro ⟨⟨⟨n, m, c⟩, h⟩, result⟩
  cases c with
  | outputs select => cases h
  | @gate _ _ arity op args next =>
    change Circuit .booleanAlgebra (n + 1) (n + 1 + m) at result
    simp only [keepResume, source_bounds]
    simp only [compBounds, pairBounds, Realizes.bounds_implementation, circuitCompBounds,
      keepResumeBounds, identityBounds, Sigma.encode_mk,
      size_encode_prod, Circuit.encode_outputs, Circuit.size_outputs,
      size_encode_unit, Tree.encode_self]
    dsimp +instances only [id, keepRecursion, keepNextFn] at *
    let N := n + m + result.size + 1
    change _ ≤ 1000000000000000000000 * N ^ 8 ∧ _ ≤
      2 * (1 + ⌜(n, m, Circuit.gate op args next)⌝ₜ.size + ⌜result⌝ₜ.size) +
        1000000000000000000 * N ^ 4
    have hN : 1 ≤ N := by dsimp [N]; omega
    have hN₂ := Nat.le_self_pow (by decide : 2 ≠ 0) N
    have h₁₂ : 1 ≤ N ^ 2 := Nat.one_le_pow 2 _ hN
    have h₂₄ : N ^ 2 ≤ N ^ 4 := Nat.pow_le_pow_right hN (by decide)
    have h₂₈ : N ^ 2 ≤ N ^ 8 := Nat.pow_le_pow_right hN (by decide)
    have hnN : n ≤ N := by dsimp [N]; omega
    have hmN : m ≤ N := by dsimp [N]; omega
    have hn := size_encode_nat_le n
    have hm := size_encode_nat_le m
    have hn' := size_encode_nat_le (n + 1)
    have hnm := size_encode_nat_le (n + m)
    have hnm' := size_encode_nat_le (n + 1 + m)
    have hb := (length_le_codeSize n.bits).trans hn
    have hk : arity ≤ 2 := by cases op <;> decide
    have hk' := size_encode_nat_le arity
    have hop : ⌜op⌝ₜ.size ≤ 11 := by cases op <;> simp [encode_unit]
    have wireSize {q k : ℕ} (hq : q ≤ 2 * N) (hk : k ≤ 2 * N) (w : Fin q → Fin k) :
        ⌜w⌝ₜ.size ≤ 32 * N ^ 2 := by
      have hw := size_encode_fin_function_le w (4 * k + 1) (fun i => by
        have := size_encode_nat_le (w i).val
        have := (w i).isLt
        simpa only [encode_fin] using (by omega : ⌜(w i).val⌝ₜ.size ≤ 4 * k + 1))
      have hp := Nat.mul_le_mul hq (by omega : 4 * k + 1 + 1 ≤ 10 * N)
      nlinarith only [hw, hp, hN₂, h₁₂]
    have ha := wireSize (by omega) (by omega) args
    have hw₁ := wireSize (by omega) (by dsimp [N]; omega)
      (fun i : Fin n => Fin.castAdd m i.castSucc)
    have hw₂ := wireSize (by omega) (by dsimp [N]; omega) (Fin.natAdd (n + 1) :
      Fin m → Fin (n + 1 + m))
    have hw₃ := wireSize (by dsimp [N]; omega) (by dsimp [N]; omega)
      (Fin.append (fun i : Fin n => Fin.castAdd m i.castSucc) (Fin.natAdd (n + 1)))
    have hr := result.size_encode_numeric_le
    have hresult : ⌜result⌝ₜ.size ≤ 400 * N ^ 2 := hr.trans (by
      have hp := Nat.mul_le_mul
        (Nat.mul_le_mul_left 100 (by dsimp [N]; omega : result.size + (n + 1 + m) + 1 ≤ 2 * N))
        (by dsimp [N]; omega : n + 1 + result.size + 1 ≤ 2 * N)
      calc
        _ ≤ 100 * (2 * N) * (2 * N) := hp
        _ = 400 * N ^ 2 := by ring)
    have hmap := (result.mapOutputs
      (Fin.append (fun i : Fin n => Fin.castAdd m i.castSucc)
        (Fin.natAdd (n + 1)))).size_encode_numeric_le
    simp only [Circuit.size_mapOutputs] at hmap
    have hmapped : ⌜result.mapOutputs
        (Fin.append (fun i : Fin n => Fin.castAdd m i.castSucc) (Fin.natAdd (n + 1)))⌝ₜ.size ≤
          400 * N ^ 2 := hmap.trans (by
      have hp := Nat.mul_le_mul
        (Nat.mul_le_mul_left 100 (by dsimp [N]; omega : result.size + (n + m) + 1 ≤ 2 * N))
        (by dsimp [N]; omega : n + 1 + result.size + 1 ≤ 2 * N)
      calc
        _ ≤ 100 * (2 * N) * (2 * N) := hp
        _ = 400 * N ^ 2 := by ring)
    have hrn := size_encode_range_le n
    have hrm := size_encode_range_le m
    have hpn := pow_le_pow_left' (by dsimp [N]; omega : n + 1 ≤ N) 2
    have hpm := pow_le_pow_left' (by dsimp [N]; omega : m + 1 ≤ N) 2
    have hrn' : ⌜List.range n⌝ₜ.size ≤ 32 * N ^ 2 := by nlinarith only [hrn, hpn]
    have hrm' : ⌜List.range m⌝ₜ.size ≤ 32 * N ^ 2 := by nlinarith only [hrm, hpm]
    have hW : n + 1 + (n + 1 + m) + (n + m) + 2 * (result.size + 0) + 1 ≤ 3 * N := by
      dsimp [N]; omega
    have hW₄ := pow_le_pow_left' hW 4
    have hW₈ := pow_le_pow_left' hW 8
    norm_num only [mul_pow, Nat.reducePow] at hW₄ hW₈
    have hsum : ((List.finRange m).map (fun i =>
        2 + (28 * n.bits.length + 25) + (1 + 1) +
          (2000 * (1 + ⌜n + 1⌝ₜ.size + ⌜i.val⌝ₜ.size) + 10020) + 0)).sum ≤
            100000 * N ^ 2 := by
      have hs := List.sum_le_sum (l := List.finRange m) (g := fun _ => 100000 * N)
        (fun i _ => show 2 + (28 * n.bits.length + 25) + (1 + 1) +
            (2000 * (1 + ⌜n + 1⌝ₜ.size + ⌜i.val⌝ₜ.size) + 10020) + 0 ≤ 100000 * N from by
          have := size_encode_nat_le i.val
          have := i.isLt
          omega)
      simp only [List.map_const', List.sum_replicate, List.length_finRange, smul_eq_mul] at hs
      apply hs.trans
      calc
        _ = 100000 * (m * N) := by ring
        _ ≤ 100000 * (N * N) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right N hmN)
        _ = 100000 * N ^ 2 := by ring
    simp only [tabulateBounds, compBounds, pairBounds, identityBounds, Sigma.encode_mk,
      size_encode_prod, encode_fin, Fin.val_castAdd, Fin.val_castSucc,
      List.map_const', List.sum_replicate, List.length_finRange, smul_eq_mul,
      ← max_assoc, max_le_iff, foldr_max_le]
    dsimp +instances only [id, keepRecursion, keepNextFn] at *
    (repeat' apply And.intro) <;> first
    | omega
    | (change 1 + (1 + ⌜n⌝ₜ.size + (1 + ⌜m⌝ₜ.size +
         ⌜Circuit.gate op args next⌝ₜ.size)) + ⌜result⌝ₜ.size ≤ _
       omega)
    | (change 1 + (1 + ⌜n⌝ₜ.size + (1 + ⌜m⌝ₜ.size + (1 + ⌜arity⌝ₜ.size +
         (1 + ⌜op⌝ₜ.size + (1 + ⌜args⌝ₜ.size + ⌜result⌝ₜ.size))))) + _ ≤ _
       omega)
    | (intro i hi
       have hcode := size_encode_nat_le i.val
       have hlt := i.isLt
       have hsumcode := size_encode_nat_le (n + 1 + i.val)
       (repeat' apply And.intro) <;> omega)

noncomputable def keepImplementation : Implementation (fun x => ⌜keepFn x⌝ₜ) :=
  keepRecursion.implementation keepCheck keepNext keepFinish keepResume_realizes.implementation

private theorem keep_input_size_le (n m : ℕ) (c : Circuit .booleanAlgebra n m)
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

private theorem keep_cost_numeric_le (N : ℕ) (x : KeepInput)
    (hx : x.1 + x.2.1 + 2 * x.2.2.size ≤ N) :
    let bc : Bounds KeepInput := ⟨fun _ => 10, fun x => ⌜x⌝ₜ.size⟩
    let bs : Bounds KeepInput :=
      ⟨fun x => 1000 * (⌜x⌝ₜ.size + 1), fun x => 1000 * (⌜x⌝ₜ.size + 1)⟩
    let bd : Bounds {x // keepRecursion.test x = false} :=
      ⟨fun x => 1000000 * (x.1.1 + x.1.2.1 + 1) ^ 2,
       fun x => 1000000 * (x.1.1 + x.1.2.1 + 1) ^ 2⟩
    (keepRecursion.cost bc bs bd keepResumeBounds x).time ≤
        (x.2.2.size + 1) * (10000000000000000000000 * (N + 1) ^ 8) ∧
      (keepRecursion.cost bc bs bd keepResumeBounds x).peak ≤
        10000000000000000000 * (N + 1) ^ 4 +
          (x.2.2.size + 1) * (128 * (N + 1) ^ 2 + 1) := by
  let R := N + 1
  have hR : 1 ≤ R := by dsimp [R]; omega
  have h₂ : 1 ≤ R ^ 2 := Nat.one_le_pow 2 _ hR
  have h₂₄ : R ^ 2 ≤ R ^ 4 := Nat.pow_le_pow_right hR (by decide)
  have h₂₈ : R ^ 2 ≤ R ^ 8 := Nat.pow_le_pow_right hR (by decide)
  refine keepRecursion.cost_le_of_invariant _ _ _ _
    (fun y => y.1 + y.2.1 + 2 * y.2.2.size ≤ N)
    (128 * R ^ 2) (10000000000000000000000 * R ^ 8) (10000000000000000000 * R ^ 4)
    ?_ ?_ ?_ ?_ x hx
  · rintro ⟨n, m, c⟩ hy
    exact keep_input_size_le n m c N hy
  · rintro ⟨n, m, c⟩ hy
    have hs := keep_input_size_le n m c N hy
    change _ ≤ 128 * R ^ 2 at hs
    change ⌜(⟨n, m, c⟩ : KeepInput)⌝ₜ.size ≤ _
    omega
  · rintro ⟨n, m, c⟩ h hy
    dsimp only at hy
    have hw : n + m + 1 ≤ R := by dsimp [R]; omega
    have hW₂ := pow_le_pow_left' hw 2
    change 1000000 * (n + m + 1) ^ 2 + 2 ≤ _ ∧ 1000000 * (n + m + 1) ^ 2 ≤ _
    omega
  · rintro ⟨n, m, c⟩ h hy
    dsimp only at hy
    have hs := keep_input_size_le n m c N hy
    cases c with
    | outputs select => cases h
    | gate op args next =>
      have hi : n + 1 + m + 2 * next.size ≤ N := by
        simp only [Circuit.size_gate] at hy
        omega
      have ho := next.keepInputs.size_encode_numeric_le
      simp only [Circuit.size_keepInputs] at ho
      have hout : ⌜next.keepInputs⌝ₜ.size ≤ 100 * R ^ 2 := ho.trans (by
        simpa only [pow_two, Nat.mul_assoc] using Nat.mul_le_mul
          (Nat.mul_le_mul_left 100
            (by dsimp [R]; omega : next.size + (n + 1 + m) + 1 ≤ R))
          (by dsimp [R]; omega : n + 1 + next.size + 1 ≤ R))
      have hw : n + m + next.size + 1 ≤ R := by dsimp [R]; omega
      have h₄ := pow_le_pow_left' hw 4
      have h₈ := pow_le_pow_left' hw 8
      change _ ≤ 128 * R ^ 2 at hs
      refine ⟨hi, ?_, ?_, ?_⟩
      · change 1000 * (⌜(⟨n, m, .gate op args next⟩ : KeepInput)⌝ₜ.size + 1) ≤ _
        omega
      · change 2 * (1 + ⌜(⟨n, m, .gate op args next⟩ : KeepInput)⌝ₜ.size +
          ⌜next.keepInputs⌝ₜ.size) +
            1000000000000000000 * (n + m + next.keepInputs.size + 1) ^ 4 ≤ _
        rw [Circuit.size_keepInputs]
        omega
      · change 1000 * (⌜(⟨n, m, .gate op args next⟩ : KeepInput)⌝ₜ.size + 1) + 10 +
          1000000000000000000000 * (n + m + next.keepInputs.size + 1) ^ 8 + 16 ≤ _
        rw [Circuit.size_keepInputs]
        omega

@[simps] def keepBounds : Bounds KeepInput :=
  let N (x : KeepInput) := x.1 + x.2.1 + 2 * x.2.2.size + 1
  ⟨fun x => 100000000000000000000000 * N x ^ 9,
   fun x => 100000000000000000000 * N x ^ 4⟩

theorem keep_bounds_le (x : KeepInput) :
    keepImplementation.bounds.time x ≤ keepBounds.time x ∧
      keepImplementation.bounds.peak x ≤ keepBounds.peak x := by
  rcases x with ⟨n, m, c⟩
  let R := n + m + 2 * c.size + 1
  have hc := keep_cost_numeric_le (n + m + 2 * c.size) ⟨n, m, c⟩ le_rfl
  dsimp only at hc
  have hg : c.size + 1 ≤ R := by dsimp [R]; omega
  have hR : 1 ≤ R := by dsimp [R]; omega
  have h₂ : 1 ≤ R ^ 2 := Nat.one_le_pow 2 _ hR
  have h₄ : 1 ≤ R ^ 4 := Nat.one_le_pow 4 _ hR
  have h₉ : 1 ≤ R ^ 9 := Nat.one_le_pow 9 _ hR
  have h₃₄ : R ^ 3 ≤ R ^ 4 := Nat.pow_le_pow_right hR (by decide)
  have ht : (c.size + 1) * R ^ 8 ≤ R ^ 9 := calc
    _ ≤ R * R ^ 8 := Nat.mul_le_mul_right _ hg
    _ = _ := by rw [pow_succ R 8]; ac_rfl
  have hs : (c.size + 1) * (128 * R ^ 2 + 1) ≤ 129 * R ^ 3 := calc
    _ ≤ R * (129 * R ^ 2) := Nat.mul_le_mul hg (by omega)
    _ = _ := by rw [pow_succ R 2]; ac_rfl
  constructor
  · calc
      _ ≤ 10 + 3 * ((c.size + 1) * (10000000000000000000000 * R ^ 8)) + 10 :=
        Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left 3 hc.1) 10) 10
      _ ≤ 100000000000000000000000 * R ^ 9 := by
        rw [Nat.mul_left_comm (c.size + 1) 10000000000000000000000]
        omega
  · calc
      _ ≤ 10000000000000000000 * R ^ 4 + (c.size + 1) * (128 * R ^ 2 + 1) + 1 :=
        Nat.add_le_add_right hc.2 1
      _ ≤ 100000000000000000000 * R ^ 4 := by omega

@[scoped fun_prop] theorem keepInputs_realizes {ρ : Type} [UniqueEncoding Tree ρ]
    {n m : ρ → ℕ} {c : (x : ρ) → Circuit .booleanAlgebra (n x) (m x)} {b : Bounds ρ}
    (h : Realizes (fun x => (⟨n x, m x, c x⟩ : KeepInput)) b) :
    Realizes (fun x => ⌜(c x).keepInputs⌝ₜ)
      (compBounds (fun x => (⟨n x, m x, c x⟩ : KeepInput)) b keepBounds) :=
  h.comp (keepImplementation.realizes.mono keep_bounds_le)

end Complexity.TreeProgram.Source
