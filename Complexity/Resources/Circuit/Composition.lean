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
@[dominated] theorem size_encode_liftInputs {n k : ℕ} (wires : Fin n → Fin k) :
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

theorem dominated_one_pow {α : Type*} (R : α → ℕ) (hR : ∀ x, 0 < R x) (d : ℕ) :
    Dominated (fun _ => 1) (fun x => R x ^ d) :=
  Dominated.one fun x => Nat.pow_pos (hR x)

theorem dominated_pow_pow_of_le {α : Type*} (R : α → ℕ) (hR : ∀ x, 0 < R x)
    {d e : ℕ} (h : d ≤ e) : Dominated (fun x => R x ^ d) (fun x => R x ^ e) :=
  Dominated.of_le fun x => Nat.pow_le_pow_right (hR x) h

/-- The arguments of `Circuit.relabel`. -/
@[tree_encoding]
structure RelabelInput where
  /-- Available wires of the circuit. -/
  n : ℕ
  /-- Outputs of the circuit. -/
  m : ℕ
  /-- Available wires after relabeling. -/
  k : ℕ
  /-- The circuit to relabel. -/
  circuit : Circuit .booleanAlgebra n m
  /-- The substitution of available wires. -/
  wires : Fin n → Fin k

def relabelFn (x : RelabelInput) := x.circuit.relabel x.wires

def relabelTest (x : RelabelInput) :=
  match x.circuit with | .outputs _ => false | .gate _ _ _ => true

def relabelNextFn (x : RelabelInput) : RelabelInput :=
  match x.circuit with
  | .outputs _ => x
  | .gate _ _ next => ⟨x.n + 1, x.m, x.k + 1, next, Circuit.liftInputs x.wires⟩

def relabelFinishFn : (x : {x // relabelTest x = false}) → Circuit .booleanAlgebra x.1.k x.1.m
  | ⟨⟨_, _, _, .outputs select, wires⟩, _⟩ => .outputs (wires ∘ select)
  | ⟨⟨_, _, _, .gate _ _ _, _⟩, h⟩ => False.elim (by cases h)

def relabelResumeFn : (x : {x // relabelTest x = true}) →
    Circuit .booleanAlgebra (relabelNextFn x.1).k (relabelNextFn x.1).m →
    Circuit .booleanAlgebra x.1.k x.1.m
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
  measure x := x.circuit.size
  decreases := by
    rintro ⟨n, m, k, c, wires⟩ h
    cases c <;> simp_all [relabelTest, relabelNextFn]

def relabelScale (x : RelabelInput) : ℕ := x.n + x.m + x.k + 2 * x.circuit.size + 1

theorem relabelScale_pos (x : RelabelInput) : 0 < relabelScale x := Nat.succ_pos _

theorem relabelScale_next_le (x : RelabelInput) :
    relabelScale (relabelNextFn x) ≤ relabelScale x := by
  rcases x with ⟨n, m, k, c, w⟩
  cases c <;>
    simp -implicitDefEqProofs only [relabelNextFn, relabelScale, Circuit.size_gate] <;> omega

theorem size_encode_relabelInput_le (x : RelabelInput) :
    ⌜x⌝ₜ.size ≤ 128 * relabelScale x ^ 2 := by
  rcases x with ⟨n, m, k, c, w⟩
  obtain ⟨S, hS⟩ : ∃ S, relabelScale ⟨n, m, k, c, w⟩ = S := ⟨_, rfl⟩
  have hS' : S = n + m + k + 2 * c.size + 1 := hS.symm
  rw [hS]
  have hc := c.size_encode_numeric_le
  have hcp : (c.size + m + 1) * (n + c.size + 1) ≤ S ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul (by omega : c.size + m + 1 ≤ S)
      (by omega : n + c.size + 1 ≤ S)
  have hw := size_encode_fin_function_le w (4 * k + 1) (fun i => by
    have := size_encode_nat_le (w i).val
    have := (w i).isLt
    simpa only [encode_fin] using (by omega : ⌜(w i).val⌝ₜ.size ≤ 4 * k + 1))
  have hwp := Nat.mul_le_mul (by omega : n ≤ S) (by omega : 4 * k + 1 + 1 ≤ 6 * S)
  have hn := size_encode_nat_le n
  have hm := size_encode_nat_le m
  have hk := size_encode_nat_le k
  simp only [RelabelInput.encode_mk, size_encode_prod]
  nlinarith

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

def relabelCheck : Implementation relabelTest
    (fun x => ⌜x⌝ₜ.size ^ 3) (fun x => ⌜x⌝ₜ.size ^ 2) := by
  source_fun_prop
  all_goals dominated

def relabelNext : Implementation relabelNextFn
    (fun x => ⌜x⌝ₜ.size ^ 3) (fun x => ⌜x⌝ₜ.size ^ 2) := by
  source_fun_prop
  all_goals dominated

attribute [local fun_prop] Implementation.finComp in
def relabelFinish : Implementation (fun x => ⌜relabelFinishFn x⌝ₜ)
    (fun x => ⌜x⌝ₜ.size ^ 3) (fun x => ⌜x⌝ₜ.size ^ 2) := by
  source_fun_prop
  all_goals dominated

attribute [local fun_prop] Implementation.finComp in
def relabelResume : Implementation (fun x : relabelRecursion.Return => ⌜relabelResumeFn x.1 x.2⌝ₜ)
    (fun x => ⌜x⌝ₜ.size ^ 3) (fun x => ⌜x⌝ₜ.size ^ 2) := by
  source_fun_prop
  all_goals dominated

/-- The recursive program, with the structural cost of its callbacks bounded by its scale. -/
def relabelImplementation : Implementation (fun x => ⌜relabelFn x⌝ₜ)
    (fun x => relabelScale x ^ 7) (fun x => relabelScale x ^ 4) :=
  have hsize := Dominated.of_le_mul 128 size_encode_relabelInput_le
  have hpow (d : ℕ) : Dominated (fun x : RelabelInput => ⌜x⌝ₜ.size ^ d)
      (fun x => relabelScale x ^ (2 * d)) := by simpa only [pow_mul] using hsize.pow d
  have hstop (d : ℕ) := (hpow d).comp (Subtype.val (p := fun x => relabelTest x = false))
  have hreturn := relabelRecursion.dominated_size_return relabelScale relabelScale_pos
    (fun x _ => relabelScale_next_le x) hsize (Dominated.of_le_mul 100 size_encode_relabelFn_le)
  (relabelRecursion.implementationOfScale relabelCheck relabelNext relabelFinish relabelResume
    relabelScale relabelScale_pos (fun x _ => relabelScale_next_le x) hsize (hpow 3) (hpow 2)
    (hpow 3) (hpow 2) (hstop 3) (hstop 2) (hreturn 3) (hreturn 2)).mono
    (Dominated.of_le_mul 2 fun x => by
      have h : x.circuit.size + 1 ≤ relabelScale x := by dsimp [relabelScale]; omega
      have := Nat.mul_le_mul_right (relabelScale x ^ 6) h
      have := Nat.pow_le_pow_right (relabelScale_pos x) (by decide : 6 ≤ 7)
      simp only [relabelRecursion, Nat.reduceMul, pow_succ] at *
      nlinarith)
    (Dominated.of_le_mul 3 fun x => by
      have h : x.circuit.size + 1 ≤ relabelScale x := by dsimp [relabelScale]; omega
      have h₃ := Nat.pow_le_pow_right (relabelScale_pos x) (by decide : 3 ≤ 4)
      have h₁ := Nat.pow_le_pow_right (relabelScale_pos x) (by decide : 1 ≤ 4)
      have := Nat.mul_le_mul_right (relabelScale x ^ 2 + 1) h
      simp only [relabelRecursion, Nat.reduceMul]
      nlinarith)

/-- Relabel a circuit computed by a selected implementation. -/
def Implementation.relabel {ρ : Type} [UniqueEncoding Tree ρ]
    {n m k : ρ → ℕ}
    {c : (x : ρ) → Circuit .booleanAlgebra (n x) (m x)}
    {w : (x : ρ) → Fin (n x) → Fin (k x)} {t p : ρ → ℕ}
    (h : Implementation (fun x => (⟨n x, m x, k x, c x, w x⟩ : RelabelInput)) t p) :
    Implementation (fun x => ⌜(c x).relabel (w x)⌝ₜ)
      (fun x => t x + relabelScale ⟨n x, m x, k x, c x, w x⟩ ^ 7)
      (fun x => max (p x) (relabelScale ⟨n x, m x, k x, c x, w x⟩ ^ 4)) :=
  h.comp relabelImplementation

attribute [scoped fun_prop] Implementation.relabel

/-- The arguments of `Circuit.comp`. -/
@[tree_encoding]
structure CompInput where
  /-- Inputs of the first circuit. -/
  n : ℕ
  /-- Outputs of the first circuit and inputs of the second. -/
  m : ℕ
  /-- Outputs of the second circuit. -/
  k : ℕ
  /-- The circuit run first. -/
  first : Circuit .booleanAlgebra n m
  /-- The circuit fed by its outputs. -/
  second : Circuit .booleanAlgebra m k

def compFn (x : CompInput) := x.first.comp x.second

def compTest (x : CompInput) :=
  match x.first with | .outputs _ => false | .gate _ _ _ => true

def compNextFn (x : CompInput) : CompInput :=
  match x.first with
  | .outputs _ => x
  | .gate _ _ next => ⟨x.n + 1, x.m, x.k, next, x.second⟩

def compFinishFn : (x : {x // compTest x = false}) → Circuit .booleanAlgebra x.1.n x.1.k
  | ⟨⟨n, m, k, .outputs select, d⟩, _⟩ => relabelFn ⟨m, k, n, d, select⟩
  | ⟨⟨_, _, _, .gate _ _ _, _⟩, h⟩ => False.elim (by cases h)

def compResumeFn : (x : {x // compTest x = true}) →
    Circuit .booleanAlgebra (compNextFn x.1).n (compNextFn x.1).k →
    Circuit .booleanAlgebra x.1.n x.1.k
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
  measure x := x.first.size
  decreases := by
    rintro ⟨n, m, k, c, d⟩ h
    cases c <;> simp_all [compTest, compNextFn]

def compScale (x : CompInput) : ℕ :=
  x.n + x.m + x.k + 2 * (x.first.size + x.second.size) + 1

theorem compScale_pos (x : CompInput) : 0 < compScale x := Nat.succ_pos _

theorem compScale_next_le (x : CompInput) : compScale (compNextFn x) ≤ compScale x := by
  rcases x with ⟨n, m, k, c, d⟩
  cases c <;> simp -implicitDefEqProofs only [compNextFn, compScale, Circuit.size_gate] <;> omega

theorem size_encode_compInput_le (x : CompInput) : ⌜x⌝ₜ.size ≤ 256 * compScale x ^ 2 := by
  rcases x with ⟨n, m, k, c, d⟩
  obtain ⟨S, hS⟩ : ∃ S, compScale ⟨n, m, k, c, d⟩ = S := ⟨_, rfl⟩
  have hS' : S = n + m + k + 2 * (c.size + d.size) + 1 := hS.symm
  rw [hS]
  have hc := c.size_encode_numeric_le
  have hd := d.size_encode_numeric_le
  have hcp : (c.size + m + 1) * (n + c.size + 1) ≤ S ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul (by omega : c.size + m + 1 ≤ S)
      (by omega : n + c.size + 1 ≤ S)
  have hdp : (d.size + k + 1) * (m + d.size + 1) ≤ S ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul (by omega : d.size + k + 1 ≤ S)
      (by omega : m + d.size + 1 ≤ S)
  have hn := size_encode_nat_le n
  have hm := size_encode_nat_le m
  have hk := size_encode_nat_le k
  simp only [CompInput.encode_mk, size_encode_prod]
  nlinarith

theorem size_encode_compFn_le (x : CompInput) : ⌜compFn x⌝ₜ.size ≤ 100 * compScale x ^ 2 := by
  rcases x with ⟨n, m, k, c, d⟩
  have h := (c.comp d).size_encode_numeric_le
  simp -implicitDefEqProofs only [Circuit.size_comp] at h
  apply h.trans
  simpa -implicitDefEqProofs only [pow_two, Nat.mul_assoc] using Nat.mul_le_mul
    (Nat.mul_le_mul_left 100 (by dsimp [compScale]; omega :
      c.size + d.size + k + 1 ≤ compScale ⟨n, m, k, c, d⟩))
    (by dsimp [compScale]; omega : n + (c.size + d.size) + 1 ≤ compScale ⟨n, m, k, c, d⟩)

def compCheck : Implementation compTest (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  all_goals dominated

def compNext : Implementation compNextFn (fun x => ⌜x⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  all_goals dominated

def compFinish : Implementation (fun x => ⌜compFinishFn x⌝ₜ)
    (fun x => compScale x.1 ^ 7) (fun x => ⌜x⌝ₜ.size + compScale x.1 ^ 4) := by
  source_fun_prop
  all_goals dominated [relabelScale, compScale]

def compResume : Implementation (fun x : compRecursion.Return => ⌜compResumeFn x.1 x.2⌝ₜ)
    (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  all_goals dominated

/-- The terminal relabel call is paid once, so the time expression has degree seven, not eight. -/
def compImplementation : Implementation (fun x => ⌜compFn x⌝ₜ)
    (fun x => compScale x ^ 7) (fun x => compScale x ^ 4) :=
  have hsize := Dominated.of_le_mul 256 size_encode_compInput_le
  have hpos x := Nat.pow_pos (n := 2) (compScale_pos x)
  have hreturn := compRecursion.dominated_size_return compScale compScale_pos
    (fun x _ => compScale_next_le x) hsize (Dominated.of_le_mul 100 size_encode_compFn_le) 1
  (compRecursion.implementationOfScale compCheck compNext compFinish compResume compScale
    compScale_pos (fun x _ => compScale_next_le x) hsize (Dominated.one hpos)
    (hsize.mono_pow (by decide : 2 ≤ 4) compScale_pos) hsize
    (hsize.mono_pow (by decide : 2 ≤ 4) compScale_pos) (Dominated.refl _)
    (((hsize.mono_pow (by decide : 2 ≤ 4) compScale_pos).comp Subtype.val).add_same
      (Dominated.refl _))
    (Dominated.one fun x => hpos x.1)
    (by simpa only [pow_one] using
      hreturn.mono_pow (by decide : 2 * 1 ≤ 4) fun x => compScale_pos x.1)).mono
    (Dominated.of_le_mul 2 fun x => by
      have h : x.first.size + 1 ≤ compScale x := by dsimp [compScale]; omega
      have := Nat.mul_le_mul_right (compScale x ^ 2) h
      have := Nat.pow_le_pow_right (compScale_pos x) (by decide : 3 ≤ 7)
      simp only [compRecursion, pow_succ] at *
      nlinarith)
    (Dominated.of_le_mul 3 fun x => by
      have h : x.first.size + 1 ≤ compScale x := by dsimp [compScale]; omega
      have h₃ := Nat.pow_le_pow_right (compScale_pos x) (by decide : 3 ≤ 4)
      have h₁ := Nat.pow_le_pow_right (compScale_pos x) (by decide : 1 ≤ 4)
      have := Nat.mul_le_mul_right (compScale x ^ 2 + 1) h
      simp only [compRecursion]
      nlinarith)

/-- Compose circuits computed by a selected implementation. -/
def Implementation.circuitComp {ρ : Type} [UniqueEncoding Tree ρ]
    {n m k : ρ → ℕ}
    {c : (x : ρ) → Circuit .booleanAlgebra (n x) (m x)}
    {d : (x : ρ) → Circuit .booleanAlgebra (m x) (k x)} {t p : ρ → ℕ}
    (h : Implementation (fun x => (⟨n x, m x, k x, c x, d x⟩ : CompInput)) t p) :
    Implementation (fun x => ⌜(c x).comp (d x)⌝ₜ)
      (fun x => t x + compScale ⟨n x, m x, k x, c x, d x⟩ ^ 7)
      (fun x => max (p x) (compScale ⟨n x, m x, k x, c x, d x⟩ ^ 4)) :=
  h.comp compImplementation

attribute [scoped fun_prop] Implementation.circuitComp

/-- The argument of `Circuit.keepInputs`. -/
@[tree_encoding]
structure KeepInput where
  /-- Inputs of the circuit. -/
  n : ℕ
  /-- Outputs of the circuit. -/
  m : ℕ
  /-- The circuit whose inputs are kept. -/
  circuit : Circuit .booleanAlgebra n m

def keepFn (x : KeepInput) := x.circuit.keepInputs

def keepTest (x : KeepInput) :=
  match x.circuit with | .outputs _ => false | .gate _ _ _ => true

def keepNextFn (x : KeepInput) : KeepInput :=
  match x.circuit with
  | .outputs _ => x
  | .gate _ _ next => ⟨x.n + 1, x.m, next⟩

/-- The output table of a terminal state. -/
@[tree_encoding]
structure KeepOutputsInput where
  /-- Inputs of the circuit. -/
  n : ℕ
  /-- Outputs of the circuit. -/
  m : ℕ
  /-- The selected outputs. -/
  select : Fin m → Fin n

/-- An outputs circuit gains its identity outputs without changing existing wires. -/
def keepOutputsFn (x : KeepOutputsInput) : Circuit .booleanAlgebra x.n (x.n + x.m) :=
  .outputs (Fin.append id x.select)

def keepFinishFn : (x : {x // keepTest x = false}) → Circuit .booleanAlgebra x.1.n (x.1.n + x.1.m)
  | ⟨⟨n, m, .outputs select⟩, _⟩ => keepOutputsFn ⟨n, m, select⟩
  | ⟨⟨_, _, .gate _ _ _⟩, h⟩ => False.elim (by cases h)

def keepResumeFn : (x : {x // keepTest x = true}) →
    Circuit .booleanAlgebra (keepNextFn x.1).n ((keepNextFn x.1).n + (keepNextFn x.1).m) →
    Circuit .booleanAlgebra x.1.n (x.1.n + x.1.m)
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
  measure x := x.circuit.size
  decreases := by
    rintro ⟨n, m, c⟩ h
    cases c <;> simp_all [keepTest, keepNextFn]

def keepScale (x : KeepInput) : ℕ := x.n + x.m + 2 * x.circuit.size + 1

theorem keepScale_pos (x : KeepInput) : 0 < keepScale x := Nat.succ_pos _

theorem keepScale_next_le (x : KeepInput) : keepScale (keepNextFn x) ≤ keepScale x := by
  rcases x with ⟨n, m, c⟩
  cases c <;> simp -implicitDefEqProofs only [keepNextFn, keepScale, Circuit.size_gate] <;> omega

theorem size_encode_keepInput_le (x : KeepInput) : ⌜x⌝ₜ.size ≤ 128 * keepScale x ^ 2 := by
  rcases x with ⟨n, m, c⟩
  obtain ⟨S, hS⟩ : ∃ S, keepScale ⟨n, m, c⟩ = S := ⟨_, rfl⟩
  have hS' : S = n + m + 2 * c.size + 1 := hS.symm
  rw [hS]
  have hc := c.size_encode_numeric_le
  have hcp : (c.size + m + 1) * (n + c.size + 1) ≤ S ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul (by omega : c.size + m + 1 ≤ S)
      (by omega : n + c.size + 1 ≤ S)
  have hn := size_encode_nat_le n
  have hm := size_encode_nat_le m
  simp only [KeepInput.encode_mk, size_encode_prod]
  nlinarith

theorem size_encode_keepFn_le (x : KeepInput) : ⌜keepFn x⌝ₜ.size ≤ 100 * keepScale x ^ 2 := by
  rcases x with ⟨n, m, c⟩
  have h := c.keepInputs.size_encode_numeric_le
  simp -implicitDefEqProofs only [Circuit.size_keepInputs] at h
  apply h.trans
  simpa -implicitDefEqProofs only [pow_two, Nat.mul_assoc] using Nat.mul_le_mul
    (Nat.mul_le_mul_left 100 (by dsimp [keepScale]; omega :
      c.size + (n + m) + 1 ≤ keepScale ⟨n, m, c⟩))
    (by dsimp [keepScale]; omega : n + c.size + 1 ≤ keepScale ⟨n, m, c⟩)

def keepCheck : Implementation keepTest (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  all_goals dominated

def keepNext : Implementation keepNextFn (fun x => ⌜x⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  all_goals dominated

def keepOutputs : Implementation (fun x => ⌜keepOutputsFn x⌝ₜ)
    (fun x => (x.n + x.m + 1) ^ 2) (fun x => (x.n + x.m + 1) ^ 2) := by
  source_fun_prop using tabulate
  all_goals dominated

/-- The output table of a terminal state. -/
def keepFinishInput : {x // keepTest x = false} → KeepOutputsInput
  | ⟨⟨_, _, .gate _ _ _⟩, h⟩ => False.elim (by cases h)
  | ⟨⟨n, m, .outputs w⟩, _⟩ => ⟨n, m, w⟩

def keepFinishInputImplementation :
    Implementation keepFinishInput (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  all_goals dominated

def keepFinish : Implementation (fun x => ⌜keepFinishFn x⌝ₜ)
    (fun x => keepScale x.1 ^ 2) (fun x => keepScale x.1 ^ 2) := by
  refine ((keepFinishInputImplementation.comp keepOutputs).congr ?_).mono ?_ ?_
  · funext ⟨⟨n, m, c⟩, h⟩
    cases c with
    | outputs _ => rfl
    | gate _ _ _ => cases h
  all_goals
    apply Dominated.of_le_mul 129
    rintro ⟨⟨n, m, c⟩, h⟩
    cases c with
    | outputs w =>
      have hs := size_encode_keepInput_le ⟨n, m, .outputs w⟩
      have hp : 0 < (n + m + 1) ^ 2 := Nat.pow_pos (Nat.succ_pos _)
      simp only [keepFinishInput, keepScale, Circuit.size_outputs, UniqueEncoding.encode_subtype,
        max_le_iff, Nat.mul_zero, Nat.add_zero] at hs ⊢
      omega
    | gate _ _ _ => cases h

/-- The live return value and gate fields needed by the return callback. -/
abbrev KeepGateInput := Σ n, Σ m, Σ k, FirstOrder.Language.booleanAlgebra.Functions k ×
  (Fin k → Fin n) × Circuit .booleanAlgebra (n + 1) (n + 1 + m)

def keepGateFn (x : KeepGateInput) : Tree :=
  ⌜Circuit.gate x.2.2.2.1 x.2.2.2.2.1
    (x.2.2.2.2.2.mapOutputs
      (Fin.append (fun i : Fin x.1 => Fin.castAdd x.2.1 i.castSucc)
        (Fin.natAdd (x.1 + 1))))⌝ₜ

def keepGateScale (x : KeepGateInput) := x.1 + x.2.1 + x.2.2.2.2.2.size + 1

def keepGateImplementation : Implementation keepGateFn
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
  source_fun_prop using tabulate
  all_goals
    simp only [Sigma.encode_mk, Tree.encode_self,
      size_encode_prod, size_encode_unit, Circuit.encode_outputs,
      Dominated.add_iff, Dominated.max_iff, Dominated.zero,
      true_and, List.map_const', List.sum_replicate,
      List.length_finRange, ← List.ofFn_eq_map, Nat.nsmul_eq_mul, Nat.mul_one]
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

def keepResumeInput : keepRecursion.Return → KeepGateInput
  | ⟨⟨⟨_, _, .outputs _⟩, h⟩, _⟩ => False.elim (by cases h)
  | ⟨⟨⟨n, m, .gate (k := k) op args _⟩, _⟩, result⟩ => ⟨n, m, k, op, args, result⟩

def keepResumeInputImplementation :
    Implementation keepResumeInput (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  all_goals dominated

def keepReturnScale (x : keepRecursion.Return) : ℕ := x.1.1.n + x.1.1.m + x.2.size + 1

def keepResume : Implementation (fun x : keepRecursion.Return => ⌜keepResumeFn x.1 x.2⌝ₜ)
    (fun x => keepReturnScale x ^ 7) (fun x => ⌜x⌝ₜ.size + keepReturnScale x ^ 4) := by
  have hscale (x : keepRecursion.Return) :
      keepGateScale (keepResumeInput x) = keepReturnScale x := by
    rcases x with ⟨⟨⟨n, m, c⟩, h⟩, result⟩
    cases c with
    | outputs _ => cases h
    | gate _ _ _ => rfl
  refine ((keepResumeInputImplementation.comp keepGateImplementation).congr ?_).mono ?_ ?_
  · funext ⟨⟨⟨n, m, c⟩, h⟩, result⟩
    cases c with
    | outputs _ => cases h
    | gate _ _ _ => rfl
  · simp only [hscale]
    exact (Dominated.const_of_pos 1 (fun _ => Nat.pow_pos (Nat.succ_pos _))).add_same
      (Dominated.refl _)
  · simp only [hscale]
    exact Dominated.of_le fun _ => max_le (Nat.le_add_right ..) (Nat.le_add_left ..)

/-- The selected recursive program for `keepInputs`, with its polynomial growth. -/
def keepImplementation : Implementation (fun x => ⌜keepFn x⌝ₜ)
    (fun x => keepScale x ^ 8) (fun x => keepScale x ^ 4) :=
  have hsize := Dominated.of_le_mul 128 size_encode_keepInput_le
  have hpos x := Nat.pow_pos (n := 2) (keepScale_pos x)
  have hreturn : Dominated (fun x : {x // keepRecursion.test x = true} =>
      ⌜(⟨x, keepFn (keepRecursion.next x.1)⟩ : keepRecursion.Return)⌝ₜ.size)
      (fun x => keepScale x.1 ^ 4) := by
    simpa only [pow_one] using (keepRecursion.dominated_size_return keepScale keepScale_pos
      (fun x _ => keepScale_next_le x) hsize (Dominated.of_le_mul 100 size_encode_keepFn_le)
      1).mono_pow (by decide : 2 * 1 ≤ 4) fun x => keepScale_pos x.1
  have hscale : Dominated (fun x : {x // keepRecursion.test x = true} =>
      keepReturnScale ⟨x, keepFn (keepRecursion.next x.1)⟩) (fun x => keepScale x.1) :=
    Dominated.of_le fun x => by
      rcases x with ⟨⟨n, m, c⟩, h⟩
      cases c with
      | outputs _ => cases h
      | gate op args next =>
        change n + m + next.keepInputs.size + 1 ≤ _
        simp only [Circuit.size_keepInputs, keepScale, Circuit.size_gate]
        omega
  (keepRecursion.implementationOfScale keepCheck keepNext keepFinish keepResume keepScale
    keepScale_pos (fun x _ => keepScale_next_le x) hsize (Dominated.one fun x =>
      Nat.pow_pos (n := 7) (keepScale_pos x))
    (hsize.mono_pow (by decide : 2 ≤ 4) keepScale_pos)
    (hsize.mono_pow (by decide : 2 ≤ 7) keepScale_pos)
    (hsize.mono_pow (by decide : 2 ≤ 4) keepScale_pos) (Dominated.refl _)
    ((Dominated.refl _).mono_pow (by decide : 2 ≤ 4) fun x => keepScale_pos x.1) (hscale.pow 7)
    (hreturn.add_same (hscale.pow 4))).mono
    (Dominated.of_le_mul 2 fun x => by
      have h : x.circuit.size + 1 ≤ keepScale x := by dsimp [keepScale]; omega
      have := Nat.mul_le_mul_right (keepScale x ^ 7) h
      have := Nat.pow_le_pow_right (keepScale_pos x) (by decide : 2 ≤ 8)
      simp only [keepRecursion, pow_succ] at *
      nlinarith)
    (Dominated.of_le_mul 3 fun x => by
      have h : x.circuit.size + 1 ≤ keepScale x := by dsimp [keepScale]; omega
      have h₃ := Nat.pow_le_pow_right (keepScale_pos x) (by decide : 3 ≤ 4)
      have h₁ := Nat.pow_le_pow_right (keepScale_pos x) (by decide : 1 ≤ 4)
      have := Nat.mul_le_mul_right (keepScale x ^ 2 + 1) h
      simp only [keepRecursion]
      nlinarith)

/-- Keep the inputs of a circuit computed by a selected implementation. -/
def Implementation.keepInputs {ρ : Type} [UniqueEncoding Tree ρ]
    {n m : ρ → ℕ} {c : (x : ρ) → Circuit .booleanAlgebra (n x) (m x)} {t p : ρ → ℕ}
    (h : Implementation (fun x => (⟨n x, m x, c x⟩ : KeepInput)) t p) :
    Implementation (fun x => ⌜(c x).keepInputs⌝ₜ)
      (fun x => t x + keepScale ⟨n x, m x, c x⟩ ^ 8)
      (fun x => max (p x) (keepScale ⟨n x, m x, c x⟩ ^ 4)) :=
  h.comp keepImplementation

attribute [scoped fun_prop] Implementation.keepInputs

end Complexity.TreeProgram.Source
