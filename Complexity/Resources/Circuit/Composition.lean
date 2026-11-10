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

/-- A numeric bound on Boolean-circuit encoding size, including every stored wire. Its two factors
form one product, which `dominated` compares with the square of a scale bounding each factor. -/
@[dominated] theorem size_encode_le {n m : ℕ} (c : Circuit .booleanAlgebra n m) :
    ⌜c⌝ₜ.size ≤ 100 * ((c.size + m + 1) * (n + c.size + 1)) := by
  induction c with
  | @outputs n m select =>
    have hs := size_encode_fin_table_le select
    simp only [encode_outputs, size_encode_prod, size_encode_unit, size_outputs] at *
    nlinarith
  | @gate n m k op args next ih =>
    have hk : k ≤ 2 := by cases op <;> decide
    have ho : ⌜op⌝ₜ.size ≤ 11 := by cases op <;> simp [encode_unit]
    have ha := size_encode_fin_table_le args
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

namespace Complexity.TreeProgram.Source

open Internal (HasProgramInO)

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

theorem hasProgramIn_relabelTest : HasProgramIn relabelTest hole(⊢ program)
    IsO(fun x => ⌜x⌝ₜ.size ^ 3) IsO(fun x => ⌜x⌝ₜ.size ^ 2) := by
  abstract_hole program using programRelabelTest
  fill_hole program in source_fun_prop

theorem hasProgramIn_relabelNextFn : HasProgramIn relabelNextFn hole(⊢ program)
    IsO(fun x => ⌜x⌝ₜ.size ^ 3) IsO(fun x => ⌜x⌝ₜ.size ^ 2) := by
  abstract_hole program using programRelabelNextFn
  fill_hole program in source_fun_prop

attribute [local fun_prop] HasProgramInO.fin_comp in
theorem hasProgramIn_relabelFinishFn : HasProgramIn relabelFinishFn hole(⊢ program)
    IsO(fun x => ⌜x⌝ₜ.size ^ 3) IsO(fun x => ⌜x⌝ₜ.size ^ 2) := by
  abstract_hole program using programRelabelFinishFn
  fill_hole program in source_fun_prop

attribute [local fun_prop] HasProgramInO.fin_comp in
theorem hasProgramIn_relabelResume :
    HasProgramIn (fun x : relabelRecursion.Return => relabelResumeFn x.1 x.2) hole(⊢ program)
      IsO(fun x => ⌜x⌝ₜ.size ^ 3) IsO(fun x => ⌜x⌝ₜ.size ^ 2) := by
  abstract_hole program using programRelabelResume
  fill_hole program in source_fun_prop

/-- The recursive program, with the structural cost of its callbacks bounded by its scale. -/
@[program] theorem hasProgramIn_relabelFn : HasProgramIn relabelFn hole(⊢ program)
    IsO(fun x => relabelScale x ^ 7) IsO(fun x => relabelScale x ^ 4) := by
  abstract_hole program using programRelabelFn
  refine HasProgramInO.toHasProgramIn ?_
  have hsize : Dominated (fun x : RelabelInput => ⌜x⌝ₜ.size) (fun x => relabelScale x ^ 2) := by
    dominated [relabelScale]
  have hpow (d : ℕ) : Dominated (fun x : RelabelInput => ⌜x⌝ₜ.size ^ d)
      (fun x => relabelScale x ^ (2 * d)) := by simpa only [pow_mul] using hsize.pow d
  have hstop (d : ℕ) := (hpow d).comp (Subtype.val (p := fun x => relabelTest x = false))
  have hreturn := relabelRecursion.dominated_size_return relabelScale relabelScale_pos
    (fun x _ => relabelScale_next_le x) hsize
    (by dominated [relabelScale, relabelFn, Circuit.size_relabel])
  fill_hole program in
    exact (relabelRecursion.hasProgramInO_of_scale hasProgramIn_relabelTest.toHasProgramInO
      hasProgramIn_relabelNextFn.toHasProgramInO hasProgramIn_relabelFinishFn.toHasProgramInO
      hasProgramIn_relabelResume.toHasProgramInO
      relabelScale relabelScale_pos (fun x _ => relabelScale_next_le x) hsize (hpow 3) (hpow 2)
      (hpow 3) (hpow 2) (hstop 3) (hstop 2) (hreturn 3) (hreturn 2)).mono
      (by dominated [relabelScale, relabelRecursion])
      (by dominated [relabelScale, relabelRecursion])

/-- Relabel a circuit computed by a selected implementation. -/
theorem Internal.HasProgramInO.relabel {ρ : Type} [UniqueEncoding Tree ρ]
    {n m k : ρ → ℕ}
    {c : (x : ρ) → Circuit .booleanAlgebra (n x) (m x)}
    {w : (x : ρ) → Fin (n x) → Fin (k x)} {t p : ρ → ℕ}
    {q : Value → Code Value}
    (h : HasProgramInO (fun x => (⟨n x, m x, k x, c x, w x⟩ : RelabelInput)) q t p) :
    HasProgramInO (fun x => (c x).relabel (w x)) (fun v => q v >>= programRelabelFn)
      (fun x => t x + relabelScale ⟨n x, m x, k x, c x, w x⟩ ^ 7)
      (fun x => max (p x) (relabelScale ⟨n x, m x, k x, c x, w x⟩ ^ 4)) :=
  h.comp_dependent hasProgramIn_relabelFn.toHasProgramInO

attribute [scoped fun_prop] HasProgramInO.relabel

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

theorem hasProgramIn_compTest :
    HasProgramIn compTest hole(⊢ program) IsO(fun _ => 1) IsO(fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programCompTest
  fill_hole program in source_fun_prop

theorem hasProgramIn_compNextFn :
    HasProgramIn compNextFn hole(⊢ program) IsO(fun x => ⌜x⌝ₜ.size) IsO(fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programCompNextFn
  fill_hole program in source_fun_prop

theorem hasProgramIn_compFinishFn : HasProgramIn compFinishFn hole(⊢ program)
    IsO(fun x => compScale x.1 ^ 7) IsO(fun x => ⌜x⌝ₜ.size + compScale x.1 ^ 4) := by
  abstract_hole program using programCompFinishFn
  fill_hole program in source_fun_prop (disch := dominated [relabelScale, compScale])

theorem hasProgramIn_compResume :
    HasProgramIn (fun x : compRecursion.Return => compResumeFn x.1 x.2) hole(⊢ program)
    IsO(fun _ => 1) IsO(fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programCompResume
  fill_hole program in source_fun_prop

/-- The terminal relabel call is paid once, so the time expression has degree seven, not eight. -/
theorem hasProgramIn_compFn : HasProgramIn compFn hole(⊢ program)
    IsO(fun x => compScale x ^ 7) IsO(fun x => compScale x ^ 4) := by
  abstract_hole program using programCompFn
  refine HasProgramInO.toHasProgramIn ?_
  have hsize : Dominated (fun x : CompInput => ⌜x⌝ₜ.size) (fun x => compScale x ^ 2) := by
    dominated [compScale]
  have hpos x := Nat.pow_pos (n := 2) (compScale_pos x)
  have hreturn := compRecursion.dominated_size_return compScale compScale_pos
    (fun x _ => compScale_next_le x) hsize
    (by dominated [compScale, compFn, Circuit.size_comp]) 1
  fill_hole program in
    exact (compRecursion.hasProgramInO_of_scale hasProgramIn_compTest.toHasProgramInO
      hasProgramIn_compNextFn.toHasProgramInO hasProgramIn_compFinishFn.toHasProgramInO
      hasProgramIn_compResume.toHasProgramInO compScale
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
theorem Internal.HasProgramInO.circuitComp {ρ : Type} [UniqueEncoding Tree ρ]
    {n m k : ρ → ℕ}
    {c : (x : ρ) → Circuit .booleanAlgebra (n x) (m x)}
    {d : (x : ρ) → Circuit .booleanAlgebra (m x) (k x)} {t p : ρ → ℕ}
    {q : Value → Code Value}
    (h : HasProgramInO (fun x => (⟨n x, m x, k x, c x, d x⟩ : CompInput)) q t p) :
    HasProgramInO (fun x => (c x).comp (d x)) (fun v => q v >>= programCompFn)
      (fun x => t x + compScale ⟨n x, m x, k x, c x, d x⟩ ^ 7)
      (fun x => max (p x) (compScale ⟨n x, m x, k x, c x, d x⟩ ^ 4)) :=
  h.comp_dependent hasProgramIn_compFn.toHasProgramInO

attribute [scoped fun_prop] HasProgramInO.circuitComp

/-- Selecting the outputs of a circuit computed by a selected implementation. -/
theorem Internal.HasProgramInO.mapOutputs {ρ : Type} [UniqueEncoding Tree ρ] {n m k : ρ → ℕ}
    {c : (x : ρ) → Circuit .booleanAlgebra (n x) (m x)} {f : (x : ρ) → Fin (k x) → Fin (m x)}
    {t p : ρ → ℕ}
    {q : Value → Code Value}
    (h : HasProgramInO (fun x => (⟨n x, m x, k x, c x, .outputs (f x)⟩ : CompInput)) q t p) :
    HasProgramInO (fun x => (c x).mapOutputs (f x)) (fun v => q v >>= programCompFn)
      (fun x => t x + compScale ⟨n x, m x, k x, c x, .outputs (f x)⟩ ^ 7)
      (fun x => max (p x) (compScale ⟨n x, m x, k x, c x, .outputs (f x)⟩ ^ 4)) :=
  h.comp_dependent hasProgramIn_compFn.toHasProgramInO

attribute [scoped fun_prop] HasProgramInO.mapOutputs

/-- The arguments of `Circuit.keepWires`. -/
@[tree_encoding]
structure KeepWiresInput where
  /-- Kept wires. -/
  p : ℕ
  /-- Available wires of the circuit. -/
  n : ℕ
  /-- Outputs of the circuit. -/
  m : ℕ
  /-- The circuit whose wires are kept. -/
  circuit : Circuit .booleanAlgebra n m
  /-- The kept wires. -/
  keep : Fin p → Fin n

/-- `Circuit.keepWires` on its packed arguments. -/
def keepWiresFn (x : KeepWiresInput) := x.circuit.keepWires x.keep

/-- Whether the circuit still has a gate to pass. -/
def keepWiresTest (x : KeepWiresInput) :=
  match x.circuit with | .outputs _ => false | .gate _ _ _ => true

/-- Pass the first gate, carrying the kept wires to the indices of its continuation. -/
def keepWiresNextFn (x : KeepWiresInput) : KeepWiresInput :=
  match x.circuit with
  | .outputs _ => x
  | .gate _ _ next => ⟨x.p, x.n + 1, x.m, next, Fin.castSucc ∘ x.keep⟩

/-- An outputs circuit returns the kept wires followed by its outputs. -/
def keepWiresFinishFn : (x : {x // keepWiresTest x = false}) →
    Circuit .booleanAlgebra x.1.n (x.1.p + x.1.m)
  | ⟨⟨_, _, _, .outputs select, keep⟩, _⟩ => .outputs (Fin.append keep select)
  | ⟨⟨_, _, _, .gate _ _ _, _⟩, h⟩ => False.elim (by cases h)

/-- Put the passed gate in front of the result for its continuation. -/
def keepWiresResumeFn : (x : {x // keepWiresTest x = true}) →
    Circuit .booleanAlgebra (keepWiresNextFn x.1).n
      ((keepWiresNextFn x.1).p + (keepWiresNextFn x.1).m) →
    Circuit .booleanAlgebra x.1.n (x.1.p + x.1.m)
  | ⟨⟨_, _, _, .outputs _, _⟩, h⟩, _ => False.elim (by cases h)
  | ⟨⟨_, _, _, .gate op args _, _⟩, _⟩, result => .gate op args result

/-- The structural recursion of `keepWires` over the gates. -/
def keepWiresRecursion : Recursion keepWiresFn where
  test := keepWiresTest
  next := keepWiresNextFn
  finish := keepWiresFinishFn
  resume := keepWiresResumeFn
  finish_eq := by
    rintro ⟨⟨p, n, m, c, keep⟩, h⟩
    cases c <;> dsimp [keepWiresTest] at h ⊢ <;> first | contradiction | rfl
  resume_eq := by
    rintro ⟨⟨p, n, m, c, keep⟩, h⟩
    cases c <;> dsimp [keepWiresTest] at h ⊢ <;> first | contradiction | rfl
  measure x := x.circuit.size
  decreases := by
    rintro ⟨p, n, m, c, keep⟩ h
    cases c <;> simp_all [keepWiresTest, keepWiresNextFn]

/-- The numeric scale of the growth of `keepWires`: the dimensions and twice the gate count. -/
def keepWiresScale (x : KeepWiresInput) : ℕ := x.p + x.n + x.m + 2 * x.circuit.size + 1

theorem keepWiresScale_pos (x : KeepWiresInput) : 0 < keepWiresScale x := Nat.succ_pos _

theorem keepWiresScale_next_le (x : KeepWiresInput) :
    keepWiresScale (keepWiresNextFn x) ≤ keepWiresScale x := by
  rcases x with ⟨p, n, m, c, keep⟩
  cases c <;>
    simp -implicitDefEqProofs only [keepWiresNextFn, keepWiresScale, Circuit.size_gate] <;> omega

theorem hasProgramIn_keepWiresTest : HasProgramIn keepWiresTest hole(⊢ program)
    IsO(fun x => ⌜x⌝ₜ.size ^ 3) IsO(fun x => ⌜x⌝ₜ.size ^ 2) := by
  abstract_hole program using programKeepWiresTest
  fill_hole program in source_fun_prop

theorem hasProgramIn_keepWiresNextFn : HasProgramIn keepWiresNextFn hole(⊢ program)
    IsO(fun x => ⌜x⌝ₜ.size ^ 3) IsO(fun x => ⌜x⌝ₜ.size ^ 2) := by
  abstract_hole program using programKeepWiresNextFn
  fill_hole program in source_fun_prop

theorem hasProgramIn_keepWiresFinishFn : HasProgramIn keepWiresFinishFn hole(⊢ program)
    IsO(fun x => ⌜x⌝ₜ.size ^ 3) IsO(fun x => ⌜x⌝ₜ.size ^ 2) := by
  abstract_hole program using programKeepWiresFinishFn
  fill_hole program in source_fun_prop

theorem hasProgramIn_keepWiresResume :
    HasProgramIn (fun x : keepWiresRecursion.Return => keepWiresResumeFn x.1 x.2) hole(⊢ program)
      IsO(fun x => ⌜x⌝ₜ.size ^ 3) IsO(fun x => ⌜x⌝ₜ.size ^ 2) := by
  abstract_hole program using programKeepWiresResume
  fill_hole program in source_fun_prop

/-- The recursive program, with the structural cost of its callbacks bounded by its scale. -/
theorem hasProgramIn_keepWiresFn : HasProgramIn keepWiresFn hole(⊢ program)
    IsO(fun x => keepWiresScale x ^ 7) IsO(fun x => keepWiresScale x ^ 4) := by
  abstract_hole program using programKeepWiresFn
  refine HasProgramInO.toHasProgramIn ?_
  have hsize : Dominated (fun x : KeepWiresInput => ⌜x⌝ₜ.size)
      (fun x => keepWiresScale x ^ 2) := by
    dominated [keepWiresScale]
  have hpow (d : ℕ) : Dominated (fun x : KeepWiresInput => ⌜x⌝ₜ.size ^ d)
      (fun x => keepWiresScale x ^ (2 * d)) := by simpa only [pow_mul] using hsize.pow d
  have hstop (d : ℕ) := (hpow d).comp (Subtype.val (p := fun x => keepWiresTest x = false))
  have hreturn := keepWiresRecursion.dominated_size_return keepWiresScale keepWiresScale_pos
    (fun x _ => keepWiresScale_next_le x) hsize
    (by dominated [keepWiresScale, keepWiresFn, Circuit.size_keepWires])
  fill_hole program in
    exact (keepWiresRecursion.hasProgramInO_of_scale hasProgramIn_keepWiresTest.toHasProgramInO
      hasProgramIn_keepWiresNextFn.toHasProgramInO hasProgramIn_keepWiresFinishFn.toHasProgramInO
      hasProgramIn_keepWiresResume.toHasProgramInO
      keepWiresScale keepWiresScale_pos (fun x _ => keepWiresScale_next_le x) hsize (hpow 3)
      (hpow 2) (hpow 3) (hpow 2) (hstop 3) (hstop 2) (hreturn 3) (hreturn 2)).mono
      (by dominated [keepWiresScale, keepWiresRecursion])
      (by dominated [keepWiresScale, keepWiresRecursion])

/-- Keep selected wires of a circuit computed by a selected implementation. -/
theorem Internal.HasProgramInO.keepWires {ρ : Type} [UniqueEncoding Tree ρ]
    {p n m : ρ → ℕ} {c : (x : ρ) → Circuit .booleanAlgebra (n x) (m x)}
    {w : (x : ρ) → Fin (p x) → Fin (n x)} {t s : ρ → ℕ}
    {q : Value → Code Value}
    (h : HasProgramInO (fun x => (⟨p x, n x, m x, c x, w x⟩ : KeepWiresInput)) q t s) :
    HasProgramInO (fun x => (c x).keepWires (w x)) (fun v => q v >>= programKeepWiresFn)
      (fun x => t x + keepWiresScale ⟨p x, n x, m x, c x, w x⟩ ^ 7)
      (fun x => max (s x) (keepWiresScale ⟨p x, n x, m x, c x, w x⟩ ^ 4)) :=
  h.comp_dependent hasProgramIn_keepWiresFn.toHasProgramInO

attribute [scoped fun_prop] HasProgramInO.keepWires

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

def keepScale (x : KeepInput) : ℕ := x.n + x.m + 2 * x.circuit.size + 1

/-- The program for `keepWires` on the identity table, with its polynomial growth. -/
theorem hasProgramIn_keepFn : HasProgramIn keepFn hole(⊢ program)
    IsO(fun x => keepScale x ^ 7) IsO(fun x => keepScale x ^ 4) := by
  abstract_hole program using programKeepFn
  fill_hole program in
    source_fun_prop (disch := dominated [keepScale, keepWiresScale]) using tabulate

/-- Keep the inputs of a circuit computed by a selected implementation. -/
theorem Internal.HasProgramInO.keepInputs {ρ : Type} [UniqueEncoding Tree ρ]
    {n m : ρ → ℕ} {c : (x : ρ) → Circuit .booleanAlgebra (n x) (m x)} {t p : ρ → ℕ}
    {q : Value → Code Value}
    (h : HasProgramInO (fun x => (⟨n x, m x, c x⟩ : KeepInput)) q t p) :
    HasProgramInO (fun x => (c x).keepInputs) (fun v => q v >>= programKeepFn)
      (fun x => t x + keepScale ⟨n x, m x, c x⟩ ^ 7)
      (fun x => max (p x) (keepScale ⟨n x, m x, c x⟩ ^ 4)) :=
  h.comp_dependent hasProgramIn_keepFn.toHasProgramInO

attribute [scoped fun_prop] HasProgramInO.keepInputs

end Complexity.TreeProgram.Source
