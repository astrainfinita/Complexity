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

/-- Adding the new input wire appends one index to the old table; the source translation computes
the lifted table as this vector. -/
@[source_view] theorem ofFn_liftInputs {n k : ℕ} (f : Fin n → Fin k) :
    Vector.ofFn (liftInputs f) = (Vector.ofFn (Fin.castSucc ∘ f)).push (Fin.last k) := by
  simp only [liftInputs, Vector.ofFn_fin_snoc]

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

theorem hasProgram_relabelTest : HasProgram relabelTest hole(⊢ program)
    (fun x => ⌜x⌝ₜ.size ^ 3) (fun x => ⌜x⌝ₜ.size ^ 2) := by
  abstract_hole program using programRelabelTest
  fill_hole program in source_fun_prop

theorem hasProgram_relabelNextFn : HasProgram relabelNextFn hole(⊢ program)
    (fun x => ⌜x⌝ₜ.size ^ 3) (fun x => ⌜x⌝ₜ.size ^ 2) := by
  abstract_hole program using programRelabelNextFn
  fill_hole program in source_fun_prop

attribute [local fun_prop] HasProgram.fin_comp in
theorem hasProgram_relabelFinishFn : HasProgram relabelFinishFn hole(⊢ program)
    (fun x => ⌜x⌝ₜ.size ^ 3) (fun x => ⌜x⌝ₜ.size ^ 2) := by
  abstract_hole program using programRelabelFinishFn
  fill_hole program in source_fun_prop

attribute [local fun_prop] HasProgram.fin_comp in
theorem hasProgram_relabelResume :
    HasProgram (fun x : relabelRecursion.Return => relabelResumeFn x.1 x.2) hole(⊢ program)
      (fun x => ⌜x⌝ₜ.size ^ 3) (fun x => ⌜x⌝ₜ.size ^ 2) := by
  abstract_hole program using programRelabelResume
  fill_hole program in source_fun_prop

/-- The recursive program, with the structural cost of its callbacks bounded by its scale. -/
@[source] theorem hasProgram_relabelFn : HasProgram relabelFn hole(⊢ program)
    (fun x => relabelScale x ^ 7) (fun x => relabelScale x ^ 4) := by
  abstract_hole program using programRelabelFn
  have hsize := Dominated.of_le_mul 128 size_encode_relabelInput_le
  have hpow (d : ℕ) : Dominated (fun x : RelabelInput => ⌜x⌝ₜ.size ^ d)
      (fun x => relabelScale x ^ (2 * d)) := by simpa only [pow_mul] using hsize.pow d
  have hstop (d : ℕ) := (hpow d).comp (Subtype.val (p := fun x => relabelTest x = false))
  have hreturn := relabelRecursion.dominated_size_return relabelScale relabelScale_pos
    (fun x _ => relabelScale_next_le x) hsize (Dominated.of_le_mul 100 size_encode_relabelFn_le)
  fill_hole program in
    exact (relabelRecursion.hasProgram_of_scale hasProgram_relabelTest
      hasProgram_relabelNextFn hasProgram_relabelFinishFn
      hasProgram_relabelResume
      relabelScale relabelScale_pos (fun x _ => relabelScale_next_le x) hsize (hpow 3) (hpow 2)
      (hpow 3) (hpow 2) (hstop 3) (hstop 2) (hreturn 3) (hreturn 2)).mono
      (by dominated [relabelScale, relabelRecursion])
      (by dominated [relabelScale, relabelRecursion])

/-- Relabel a circuit computed by a selected implementation. -/
theorem HasProgram.relabel {ρ : Type} [UniqueEncoding Tree ρ]
    {n m k : ρ → ℕ}
    {c : (x : ρ) → Circuit .booleanAlgebra (n x) (m x)}
    {w : (x : ρ) → Fin (n x) → Fin (k x)} {t p : ρ → ℕ}
    {q : Value → Code Value}
    (h : HasProgram (fun x => (⟨n x, m x, k x, c x, w x⟩ : RelabelInput)) q t p) :
    HasProgram (fun x => (c x).relabel (w x)) (fun v => q v >>= programRelabelFn)
      (fun x => t x + relabelScale ⟨n x, m x, k x, c x, w x⟩ ^ 7)
      (fun x => max (p x) (relabelScale ⟨n x, m x, k x, c x, w x⟩ ^ 4)) :=
  h.comp_dependent hasProgram_relabelFn

attribute [scoped fun_prop] HasProgram.relabel

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

theorem hasProgram_compTest :
    HasProgram compTest hole(⊢ program) (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programCompTest
  fill_hole program in source_fun_prop

theorem hasProgram_compNextFn :
    HasProgram compNextFn hole(⊢ program) (fun x => ⌜x⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programCompNextFn
  fill_hole program in source_fun_prop

theorem hasProgram_compFinishFn : HasProgram compFinishFn hole(⊢ program)
    (fun x => compScale x.1 ^ 7) (fun x => ⌜x⌝ₜ.size + compScale x.1 ^ 4) := by
  abstract_hole program using programCompFinishFn
  fill_hole program in source_fun_prop (disch := dominated [relabelScale, compScale])

theorem hasProgram_compResume :
    HasProgram (fun x : compRecursion.Return => compResumeFn x.1 x.2) hole(⊢ program)
    (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programCompResume
  fill_hole program in source_fun_prop

/-- The terminal relabel call is paid once, so the time expression has degree seven, not eight. -/
theorem hasProgram_compFn : HasProgram compFn hole(⊢ program)
    (fun x => compScale x ^ 7) (fun x => compScale x ^ 4) := by
  abstract_hole program using programCompFn
  have hsize := Dominated.of_le_mul 256 size_encode_compInput_le
  have hpos x := Nat.pow_pos (n := 2) (compScale_pos x)
  have hreturn := compRecursion.dominated_size_return compScale compScale_pos
    (fun x _ => compScale_next_le x) hsize (Dominated.of_le_mul 100 size_encode_compFn_le) 1
  fill_hole program in
    exact (compRecursion.hasProgram_of_scale hasProgram_compTest
      hasProgram_compNextFn hasProgram_compFinishFn
      hasProgram_compResume compScale
      compScale_pos (fun x _ => compScale_next_le x) hsize (Dominated.one hpos)
      (hsize.mono_pow (by decide : 2 ≤ 4) compScale_pos) hsize
      (hsize.mono_pow (by decide : 2 ≤ 4) compScale_pos) (Dominated.refl _)
      (((hsize.mono_pow (by decide : 2 ≤ 4) compScale_pos).comp Subtype.val).add_same
        (Dominated.refl _))
      (Dominated.one fun x => hpos x.1)
      (by simpa only [pow_one] using
        hreturn.mono_pow (by decide : 2 * 1 ≤ 4) fun x => compScale_pos x.1)).mono
      (by dominated [compScale, compRecursion]) (by dominated [compScale, compRecursion])

/-- Compose circuits computed by a selected implementation. -/
theorem HasProgram.circuitComp {ρ : Type} [UniqueEncoding Tree ρ]
    {n m k : ρ → ℕ}
    {c : (x : ρ) → Circuit .booleanAlgebra (n x) (m x)}
    {d : (x : ρ) → Circuit .booleanAlgebra (m x) (k x)} {t p : ρ → ℕ}
    {q : Value → Code Value}
    (h : HasProgram (fun x => (⟨n x, m x, k x, c x, d x⟩ : CompInput)) q t p) :
    HasProgram (fun x => (c x).comp (d x)) (fun v => q v >>= programCompFn)
      (fun x => t x + compScale ⟨n x, m x, k x, c x, d x⟩ ^ 7)
      (fun x => max (p x) (compScale ⟨n x, m x, k x, c x, d x⟩ ^ 4)) :=
  h.comp_dependent hasProgram_compFn

attribute [scoped fun_prop] HasProgram.circuitComp

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

theorem hasProgram_keepTest :
    HasProgram keepTest hole(⊢ program) (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programKeepTest
  fill_hole program in source_fun_prop

theorem hasProgram_keepNextFn :
    HasProgram keepNextFn hole(⊢ program) (fun x => ⌜x⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programKeepNextFn
  fill_hole program in source_fun_prop

theorem hasProgram_keepOutputsFn : HasProgram keepOutputsFn hole(⊢ program)
    (fun x => (x.n + x.m + 1) ^ 2) (fun x => (x.n + x.m + 1) ^ 2) := by
  abstract_hole program using programKeepOutputsFn
  fill_hole program in source_fun_prop using tabulate

/-- The output table of a terminal state. -/
def keepFinishInput : {x // keepTest x = false} → KeepOutputsInput
  | ⟨⟨_, _, .gate _ _ _⟩, h⟩ => False.elim (by cases h)
  | ⟨⟨n, m, .outputs w⟩, _⟩ => ⟨n, m, w⟩

theorem hasProgram_keepFinishInput :
    HasProgram keepFinishInput hole(⊢ program) (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programKeepFinishInput
  fill_hole program in source_fun_prop

theorem hasProgram_keepFinishFn : HasProgram keepFinishFn hole(⊢ program)
    (fun x => keepScale x.1 ^ 2) (fun x => keepScale x.1 ^ 2) := by
  abstract_hole program using programKeepFinishFn
  fill_hole program in
    refine ((hasProgram_keepFinishInput.comp_dependent hasProgram_keepOutputsFn).of_encode ?_).mono
      ?_ ?_
  · rintro ⟨⟨n, m, c⟩, h⟩
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

/-- Selecting the outputs of a circuit computed by a selected implementation. -/
theorem HasProgram.mapOutputs {ρ : Type} [UniqueEncoding Tree ρ] {n m k : ρ → ℕ}
    {c : (x : ρ) → Circuit .booleanAlgebra (n x) (m x)} {f : (x : ρ) → Fin (k x) → Fin (m x)}
    {t p : ρ → ℕ}
    {q : Value → Code Value}
    (h : HasProgram (fun x => (⟨n x, m x, k x, c x, .outputs (f x)⟩ : CompInput)) q t p) :
    HasProgram (fun x => (c x).mapOutputs (f x)) (fun v => q v >>= programCompFn)
      (fun x => t x + compScale ⟨n x, m x, k x, c x, .outputs (f x)⟩ ^ 7)
      (fun x => max (p x) (compScale ⟨n x, m x, k x, c x, .outputs (f x)⟩ ^ 4)) :=
  h.comp_dependent hasProgram_compFn

attribute [scoped fun_prop] HasProgram.mapOutputs

/-- The live return value and gate fields needed by the return callback. -/
abbrev KeepGateInput := Σ n, Σ m, Σ k, FirstOrder.Language.booleanAlgebra.Functions k ×
  (Fin k → Fin n) × Circuit .booleanAlgebra (n + 1) (n + 1 + m)

def keepGateFn (x : KeepGateInput) : Circuit .booleanAlgebra x.1 (x.1 + x.2.1) :=
  .gate x.2.2.2.1 x.2.2.2.2.1
    (x.2.2.2.2.2.mapOutputs
      (Fin.append (fun i : Fin x.1 => Fin.castAdd x.2.1 i.castSucc)
        (Fin.natAdd (x.1 + 1))))

def keepGateScale (x : KeepGateInput) := x.1 + x.2.1 + x.2.2.2.2.2.size + 1

theorem hasProgram_keepGateFn : HasProgram keepGateFn hole(⊢ program)
    (fun x => keepGateScale x ^ 7) (fun x => keepGateScale x ^ 4) := by
  abstract_hole program using programKeepGateFn
  have hk : Dominated (fun x : KeepGateInput => x.2.2.1) keepGateScale :=
    (Dominated.const_of_pos 2 fun _ => Nat.succ_pos _).mono_left fun x => by
      rcases x with ⟨n, m, k, op, args, result⟩
      cases op <;> dsimp <;> decide
  have : Dominated (fun x : KeepGateInput => ⌜x.2.2.2.1⌝ₜ.size) keepGateScale :=
    (Dominated.const_of_pos 11 fun _ => Nat.succ_pos _).mono_left fun x => by
      rcases x with ⟨n, m, k, op, args, result⟩
      cases op <;> simp [encode_unit]
  have := Dominated.size_encode_fin_function (fun x : KeepGateInput => x.2.2.2.2.1) hk
    (.of_le fun x => by dsimp [keepGateScale]; omega) fun _ => Nat.succ_pos _
  have := Dominated.size_encode_circuit (fun x : KeepGateInput => x.2.2.2.2.2)
    (R := keepGateScale) (.of_le_mul 2 fun x => by dsimp [keepGateScale]; omega)
    (.of_le_mul 2 fun x => by dsimp [keepGateScale]; omega)
    (.of_le fun x => by dsimp [keepGateScale]; omega) fun _ => Nat.succ_pos _
  have := hk.size_encode_nat fun _ => Nat.succ_pos _
  have := Dominated.size_encode_circuit (R := keepGateScale) (fun x : KeepGateInput =>
      x.2.2.2.2.2.mapOutputs
        (Fin.append (fun i : Fin x.1 => Fin.castAdd x.2.1 i.castSucc) (Fin.natAdd (x.1 + 1))))
    (.of_le_mul 2 fun x => by dsimp [keepGateScale]; omega)
    (.of_le fun x => by dsimp [keepGateScale]; omega)
    (.of_le fun x => by simp only [Circuit.size_mapOutputs]; dsimp [keepGateScale]; omega)
    fun _ => Nat.succ_pos _
  fill_hole program in
    source_fun_prop (disch := (try simp only [Sigma.size_encode_eq, Prod.size_encode_eq]); dominated
      [keepGateScale, compScale, Circuit.size_mapOutputs, Circuit.size_outputs]) using tabulate

def keepResumeInput : keepRecursion.Return → KeepGateInput
  | ⟨⟨⟨_, _, .outputs _⟩, h⟩, _⟩ => False.elim (by cases h)
  | ⟨⟨⟨n, m, .gate (k := k) op args _⟩, _⟩, result⟩ => ⟨n, m, k, op, args, result⟩

theorem hasProgram_keepResumeInput :
    HasProgram keepResumeInput hole(⊢ program) (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programKeepResumeInput
  fill_hole program in source_fun_prop

def keepReturnScale (x : keepRecursion.Return) : ℕ := x.1.1.n + x.1.1.m + x.2.size + 1

theorem hasProgram_keepResume :
    HasProgram (fun x : keepRecursion.Return => keepResumeFn x.1 x.2) hole(⊢ program)
      (fun x => keepReturnScale x ^ 7) (fun x => ⌜x⌝ₜ.size + keepReturnScale x ^ 4) := by
  abstract_hole program using programKeepResume
  have hscale (x : keepRecursion.Return) :
      keepGateScale (keepResumeInput x) = keepReturnScale x := by
    rcases x with ⟨⟨⟨n, m, c⟩, h⟩, result⟩
    cases c with
    | outputs _ => cases h
    | gate _ _ _ => rfl
  fill_hole program in
    refine ((hasProgram_keepResumeInput.comp_dependent hasProgram_keepGateFn).of_encode ?_).mono
      ?_ ?_
  · rintro ⟨⟨⟨n, m, c⟩, h⟩, result⟩
    cases c with
    | outputs _ => cases h
    | gate _ _ _ => rfl
  · simp only [hscale]
    exact (Dominated.const_of_pos 1 (fun _ => Nat.pow_pos (Nat.succ_pos _))).add_same
      (Dominated.refl _)
  · simp only [hscale]
    exact Dominated.of_le fun _ => max_le (Nat.le_add_right ..) (Nat.le_add_left ..)

/-- The selected recursive program for `keepInputs`, with its polynomial growth. -/
theorem hasProgram_keepFn : HasProgram keepFn hole(⊢ program)
    (fun x => keepScale x ^ 8) (fun x => keepScale x ^ 4) := by
  abstract_hole program using programKeepFn
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
  fill_hole program in
    exact (keepRecursion.hasProgram_of_scale hasProgram_keepTest
      hasProgram_keepNextFn hasProgram_keepFinishFn
      hasProgram_keepResume keepScale
      keepScale_pos (fun x _ => keepScale_next_le x) hsize (Dominated.one fun x =>
        Nat.pow_pos (n := 7) (keepScale_pos x))
      (hsize.mono_pow (by decide : 2 ≤ 4) keepScale_pos)
      (hsize.mono_pow (by decide : 2 ≤ 7) keepScale_pos)
      (hsize.mono_pow (by decide : 2 ≤ 4) keepScale_pos) (Dominated.refl _)
      ((Dominated.refl _).mono_pow (by decide : 2 ≤ 4) fun x => keepScale_pos x.1) (hscale.pow 7)
      (hreturn.add_same (hscale.pow 4))).mono
      (by dominated [keepScale, keepRecursion]) (by dominated [keepScale, keepRecursion])

/-- Keep the inputs of a circuit computed by a selected implementation. -/
theorem HasProgram.keepInputs {ρ : Type} [UniqueEncoding Tree ρ]
    {n m : ρ → ℕ} {c : (x : ρ) → Circuit .booleanAlgebra (n x) (m x)} {t p : ρ → ℕ}
    {q : Value → Code Value}
    (h : HasProgram (fun x => (⟨n x, m x, c x⟩ : KeepInput)) q t p) :
    HasProgram (fun x => (c x).keepInputs) (fun v => q v >>= programKeepFn)
      (fun x => t x + keepScale ⟨n x, m x, c x⟩ ^ 8)
      (fun x => max (p x) (keepScale ⟨n x, m x, c x⟩ ^ 4)) :=
  h.comp_dependent hasProgram_keepFn

attribute [scoped fun_prop] HasProgram.keepInputs

end Complexity.TreeProgram.Source
