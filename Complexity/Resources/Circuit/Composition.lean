/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Tactic.TreeProgram.Library
public import Complexity.Tactic.TreeProgram.Recursion
public import Complexity.Resources.Circuit.Cases
public import Complexity.ModelTheory.Algebra.BooleanAlgebra.TreeEncoding
public import Complexity.Models.Circuit.Composition

/-! # Certified circuit relabeling and composition

The descriptors retain the dependent `Circuit` types and store wire tables as `FinVector`s. Every
callback matches on circuits with `Circuit.casesFinVector` and its variants and is translated by the
common source mechanism; the recursion backend supplies the stack and its resource certificate.
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
    have hs := size_encode_finVector_fin_le (FinVector.ofFn select)
    simp only [encode_outputs, size_encode_prod, size_encode_unit, size_outputs] at *
    nlinarith
  | @gate n m k op args next ih =>
    have hk : k ≤ 2 := by cases op <;> decide
    have ho : ⌜op⌝ₜ.size ≤ 11 := by cases op <;> simp [encode_unit]
    have ha := size_encode_finVector_fin_le (FinVector.ofFn args)
    have hargs : ⌜FinVector.ofFn args⌝ₜ.size ≤ 8 * n + 5 := by nlinarith
    have hk' := size_encode_nat_le k
    simp only [encode_gate, size_encode_prod, size_encode_unit, size_gate]
    nlinarith

end Complexity.Circuit

namespace Complexity.TreeProgram.Source

open Internal (HasProgramInO)

/-- The arguments of `Circuit.relabel`, with its wire substitution stored as a `FinVector`. -/
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
  wires : FinVector (Fin k) n

/-- `Circuit.relabel` on its packed arguments. -/
def relabelFn (x : RelabelInput) := x.circuit.relabel x.wires.get

/-- Whether the circuit still has a gate to relabel. -/
def relabelTest (x : RelabelInput) : Bool :=
  x.circuit.casesFinVector (fun _ _ => false) fun _ _ _ _ => true

/-- Pass the first gate, extending the substitution across the wire it computes. The dimensions
are those after a gate even on an outputs circuit, where the step is never taken. -/
def relabelNextFn (x : RelabelInput) : RelabelInput :=
  ⟨x.n + 1, x.m, x.k + 1,
    x.circuit.casesFinVector (fun v _ => .outputs (v.map Fin.castSucc).get) fun _ _ next _ => next,
    (x.wires.map Fin.castSucc).push (Fin.last x.k)⟩

/-- An outputs circuit reads its outputs through the substitution. -/
def relabelFinishFn (x : {x // relabelTest x = false}) : Circuit .booleanAlgebra x.1.k x.1.m :=
  x.1.circuit.casesFinVectorOutputs (fun v _ => .outputs (v.map x.1.wires.get).get)
    fun _ _ _ h => by simpa [relabelTest, Circuit.casesFinVector_of_eq_gate _ _ h] using x.2

/-- Put the passed gate, with its arguments substituted, in front of the result for its
continuation. -/
def relabelResumeFn (x : {x // relabelTest x = true})
    (result : Circuit .booleanAlgebra (relabelNextFn x.1).k (relabelNextFn x.1).m) :
    Circuit .booleanAlgebra x.1.k x.1.m :=
  x.1.circuit.casesFinVectorGate
    (fun _ h => by simpa [relabelTest, Circuit.casesFinVector_of_eq_outputs _ _ h] using x.2)
    fun op v _ _ => .gate op (v.map x.1.wires.get).get result

/-- The structural recursion of `relabel` over the gates. -/
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

/-- The numeric scale of the growth of `relabel`: the dimensions and twice the gate count. -/
def relabelScale (x : RelabelInput) : ℕ := x.n + x.m + x.k + 2 * x.circuit.size + 1

theorem relabelScale_next_le (x : RelabelInput) (h : relabelTest x = true) :
    relabelScale (relabelNextFn x) ≤ relabelScale x := by
  rcases x with ⟨n, m, k, c, w⟩
  cases c
  · cases h
  · simp only [relabelNextFn, relabelScale, Circuit.casesFinVector_gate, Circuit.size_gate]
    omega

-- The test and step callbacks are stated with their natural growths, constant or linear in code
-- size; `hasProgramIn_relabelFn` takes them polynomial in these by `HasProgramIn.isPoly` and
-- compares the growths with the scale.
theorem hasProgramIn_relabelTest : HasProgramIn relabelTest hole(⊢ program)
    IsO(fun _ => 1) IsO(fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programRelabelTest
  fill_hole program in source_fun_prop

theorem hasProgramIn_relabelNextFn : HasProgramIn relabelNextFn hole(⊢ program)
    IsO(fun x => ⌜x⌝ₜ.size) IsO(fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programRelabelNextFn
  fill_hole program in source_fun_prop

-- For now the finish and resume callbacks keep their degrees: their costs are inside a match on
-- the circuit, which `dominated` compares pointwise only on `IsPoly` goals.
attribute [local fun_prop] HasProgramInO.finVector_map_get in
theorem hasProgramIn_relabelFinishFn : HasProgramIn relabelFinishFn hole(⊢ program)
    IsO(fun x => ⌜x⌝ₜ.size ^ 3) IsO(fun x => ⌜x⌝ₜ.size ^ 2) := by
  abstract_hole program using programRelabelFinishFn
  fill_hole program in source_fun_prop

attribute [local fun_prop] HasProgramInO.finVector_map_get in
theorem hasProgramIn_relabelResume :
    HasProgramIn (fun x : relabelRecursion.Return => relabelResumeFn x.1 x.2) hole(⊢ program)
      IsO(fun x => ⌜x⌝ₜ.size ^ 3) IsO(fun x => ⌜x⌝ₜ.size ^ 2) := by
  abstract_hole program using programRelabelResume
  fill_hole program in source_fun_prop

/-- The recursive program, polynomial in `relabelScale`: the recursion cost of its callbacks. -/
@[program] theorem hasProgramIn_relabelFn :
    HasProgramIn relabelFn hole(⊢ program) (IsPoly relabelScale) (IsPoly relabelScale) := by
  abstract_hole program using programRelabelFn
  have hsize : IsPoly relabelScale fun x => ⌜x⌝ₜ.size := by dominated [relabelScale]
  fill_hole program in
    exact relabelRecursion.hasProgramIn_isPoly relabelScale relabelScale_next_le
      (by dominated [relabelScale, relabelRecursion]) hsize
      (by dominated [relabelScale, relabelFn, Circuit.size_relabel])
      hasProgramIn_relabelTest.isPoly (.const 1) hsize
      hasProgramIn_relabelNextFn.isPoly hsize hsize
      hasProgramIn_relabelFinishFn.isPoly ((hsize.comp .refl).pow 3) ((hsize.comp .refl).pow 2)
      hasProgramIn_relabelResume.isPoly (IsPoly.refl.pow 3) (IsPoly.refl.pow 2)

/-- Relabel a circuit computed by a selected implementation, by a `FinVector` of wires. -/
theorem Internal.HasProgramInO.relabel {ρ : Type} [UniqueEncoding Tree ρ]
    {n m k : ρ → ℕ}
    {c : (x : ρ) → Circuit .booleanAlgebra (n x) (m x)}
    {w : (x : ρ) → FinVector (Fin (k x)) (n x)} {t p : ρ → ℕ}
    {q : Value → Code Value}
    (h : HasProgramInO (fun x => (⟨n x, m x, k x, c x, w x⟩ : RelabelInput)) q t p) :
    HasProgramInO (fun x => (c x).relabel (w x).get) (fun v => q v >>= programRelabelFn)
      (fun x => t x + hasProgramIn_relabelFn.time ⟨n x, m x, k x, c x, w x⟩)
      (fun x => max (p x) (hasProgramIn_relabelFn.peak ⟨n x, m x, k x, c x, w x⟩)) :=
  h.comp_dependent hasProgramIn_relabelFn.hasProgramInO

attribute [fun_prop] HasProgramInO.relabel

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

/-- `Circuit.comp` on its packed arguments. -/
def compFn (x : CompInput) := x.first.comp x.second

/-- Whether the first circuit still has a gate to pass. -/
def compTest (x : CompInput) : Bool :=
  x.first.casesFinVector (fun _ _ => false) fun _ _ _ _ => true

/-- Pass the first gate of the first circuit, keeping the second circuit. The dimensions are those
after a gate even on an outputs circuit, where the step is never taken. -/
def compNextFn (x : CompInput) : CompInput :=
  ⟨x.n + 1, x.m, x.k,
    x.first.casesFinVector (fun v _ => .outputs (v.map Fin.castSucc).get) fun _ _ next _ => next,
    x.second⟩

/-- The output table of the first circuit once it has no gate. For now the finish is split into
this table and a call of `relabelFn`, since on `IsPoly` goals `dominated` compares the cost inside a
match only pointwise. -/
def compOutputs (x : {x // compTest x = false}) : FinVector (Fin x.1.n) x.1.m :=
  x.1.first.casesFinVectorOutputs (fun v _ => v)
    fun _ _ _ h => by simpa [compTest, Circuit.casesFinVector_of_eq_gate _ _ h] using x.2

/-- With no gate left, the second circuit reads the outputs of the first. -/
def compFinishFn (x : {x // compTest x = false}) : Circuit .booleanAlgebra x.1.n x.1.k :=
  relabelFn ⟨x.1.m, x.1.k, x.1.n, x.1.second, compOutputs x⟩

/-- Put the passed gate in front of the result for its continuation. -/
def compResumeFn (x : {x // compTest x = true})
    (result : Circuit .booleanAlgebra (compNextFn x.1).n (compNextFn x.1).k) :
    Circuit .booleanAlgebra x.1.n x.1.k :=
  x.1.first.casesFinVectorGate
    (fun _ h => by simpa [compTest, Circuit.casesFinVector_of_eq_outputs _ _ h] using x.2)
    fun op v _ _ => .gate op v.get result

/-- The structural recursion of `comp` over the gates of the first circuit. -/
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

/-- The numeric scale of the growth of `comp`: the dimensions and twice the gate counts of both
circuits. -/
def compScale (x : CompInput) : ℕ :=
  x.n + x.m + x.k + 2 * (x.first.size + x.second.size) + 1

theorem compScale_next_le (x : CompInput) (h : compTest x = true) :
    compScale (compNextFn x) ≤ compScale x := by
  rcases x with ⟨n, m, k, c, d⟩
  cases c
  · cases h
  · simp only [compNextFn, compScale, Circuit.casesFinVector_gate, Circuit.size_gate]
    omega

-- The test, step, outputs and resume callbacks are stated with their natural growths, constant or
-- linear in code size; `hasProgramIn_compFn` takes them polynomial in these by
-- `HasProgramIn.isPoly` and compares the growths with the scale.
theorem hasProgramIn_compTest :
    HasProgramIn compTest hole(⊢ program) IsO(fun _ => 1) IsO(fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programCompTest
  fill_hole program in source_fun_prop

theorem hasProgramIn_compNextFn :
    HasProgramIn compNextFn hole(⊢ program) IsO(fun x => ⌜x⌝ₜ.size) IsO(fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programCompNextFn
  fill_hole program in source_fun_prop

@[program] theorem hasProgramIn_compOutputs :
    HasProgramIn compOutputs hole(⊢ program) IsO(fun _ => 1) IsO(fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programCompOutputs
  fill_hole program in source_fun_prop

/-- The terminal relabelling, polynomial in the scale of its composition. -/
theorem hasProgramIn_compFinishFn : HasProgramIn compFinishFn hole(⊢ program)
    (IsPoly fun x => compScale x.1) (IsPoly fun x => compScale x.1) := by
  abstract_hole program using programCompFinishFn
  fill_hole program in source_fun_prop (disch := dominated [compScale, relabelScale])

theorem hasProgramIn_compResume :
    HasProgramIn (fun x : compRecursion.Return => compResumeFn x.1 x.2) hole(⊢ program)
    IsO(fun _ => 1) IsO(fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programCompResume
  fill_hole program in source_fun_prop

/-- The recursive program, polynomial in `compScale`: the recursion cost of its callbacks, with the
terminal relabelling paid once. -/
theorem hasProgramIn_compFn :
    HasProgramIn compFn hole(⊢ program) (IsPoly compScale) (IsPoly compScale) := by
  abstract_hole program using programCompFn
  have hsize : IsPoly compScale fun x => ⌜x⌝ₜ.size := by dominated [compScale]
  fill_hole program in
    exact compRecursion.hasProgramIn_isPoly compScale compScale_next_le
      (by dominated [compScale, compRecursion]) hsize
      (by dominated [compScale, compFn, Circuit.size_comp])
      hasProgramIn_compTest.isPoly (.const 1) hsize
      hasProgramIn_compNextFn.isPoly hsize hsize
      hasProgramIn_compFinishFn .refl .refl
      hasProgramIn_compResume.isPoly (.const 1) .refl

/-- Compose circuits computed by a selected implementation. -/
theorem Internal.HasProgramInO.circuitComp {ρ : Type} [UniqueEncoding Tree ρ]
    {n m k : ρ → ℕ}
    {c : (x : ρ) → Circuit .booleanAlgebra (n x) (m x)}
    {d : (x : ρ) → Circuit .booleanAlgebra (m x) (k x)} {t p : ρ → ℕ}
    {q : Value → Code Value}
    (h : HasProgramInO (fun x => (⟨n x, m x, k x, c x, d x⟩ : CompInput)) q t p) :
    HasProgramInO (fun x => (c x).comp (d x)) (fun v => q v >>= programCompFn)
      (fun x => t x + hasProgramIn_compFn.time ⟨n x, m x, k x, c x, d x⟩)
      (fun x => max (p x) (hasProgramIn_compFn.peak ⟨n x, m x, k x, c x, d x⟩)) :=
  h.comp_dependent hasProgramIn_compFn.hasProgramInO

attribute [fun_prop] HasProgramInO.circuitComp

/-- Select outputs of a circuit computed by a selected implementation, by a `FinVector`. -/
theorem Internal.HasProgramInO.mapOutputs {ρ : Type} [UniqueEncoding Tree ρ] {n m k : ρ → ℕ}
    {c : (x : ρ) → Circuit .booleanAlgebra (n x) (m x)}
    {w : (x : ρ) → FinVector (Fin (m x)) (k x)} {t p : ρ → ℕ}
    {q : Value → Code Value}
    (h : HasProgramInO (fun x => (⟨n x, m x, k x, c x, .outputs (w x).get⟩ : CompInput)) q t p) :
    HasProgramInO (fun x => (c x).mapOutputs (w x).get) (fun v => q v >>= programCompFn)
      (fun x => t x + hasProgramIn_compFn.time ⟨n x, m x, k x, c x, .outputs (w x).get⟩)
      (fun x => max (p x) (hasProgramIn_compFn.peak ⟨n x, m x, k x, c x, .outputs (w x).get⟩)) :=
  h.comp_dependent hasProgramIn_compFn.hasProgramInO

attribute [fun_prop] HasProgramInO.mapOutputs

/-- The arguments of `Circuit.keepWires`, with the kept wires stored as a `FinVector`. -/
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
  keep : FinVector (Fin n) p

/-- `Circuit.keepWires` on its packed arguments. -/
def keepWiresFn (x : KeepWiresInput) := x.circuit.keepWires x.keep.get

/-- Whether the circuit still has a gate to pass. -/
def keepWiresTest (x : KeepWiresInput) : Bool :=
  x.circuit.casesFinVector (fun _ _ => false) fun _ _ _ _ => true

/-- Pass the first gate, carrying the kept wires to the indices of its continuation. The
dimensions are those after a gate even on an outputs circuit, where the step is never taken. -/
def keepWiresNextFn (x : KeepWiresInput) : KeepWiresInput :=
  ⟨x.p, x.n + 1, x.m,
    x.circuit.casesFinVector (fun v _ => .outputs (v.map Fin.castSucc).get) fun _ _ next _ => next,
    x.keep.map Fin.castSucc⟩

/-- An outputs circuit returns the kept wires followed by its outputs. -/
def keepWiresFinishFn (x : {x // keepWiresTest x = false}) :
    Circuit .booleanAlgebra x.1.n (x.1.p + x.1.m) :=
  x.1.circuit.casesFinVectorOutputs (fun v _ => .outputs (x.1.keep ++ v).get)
    fun _ _ _ h => by simpa [keepWiresTest, Circuit.casesFinVector_of_eq_gate _ _ h] using x.2

/-- Put the passed gate in front of the result for its continuation. -/
def keepWiresResumeFn (x : {x // keepWiresTest x = true})
    (result : Circuit .booleanAlgebra (keepWiresNextFn x.1).n
      ((keepWiresNextFn x.1).p + (keepWiresNextFn x.1).m)) :
    Circuit .booleanAlgebra x.1.n (x.1.p + x.1.m) :=
  x.1.circuit.casesFinVectorGate
    (fun _ h => by simpa [keepWiresTest, Circuit.casesFinVector_of_eq_outputs _ _ h] using x.2)
    fun op v _ _ => .gate op v.get result

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

theorem keepWiresScale_next_le (x : KeepWiresInput) (h : keepWiresTest x = true) :
    keepWiresScale (keepWiresNextFn x) ≤ keepWiresScale x := by
  rcases x with ⟨p, n, m, c, keep⟩
  cases c
  · cases h
  · simp only [keepWiresNextFn, keepWiresScale, Circuit.casesFinVector_gate, Circuit.size_gate]
    omega

-- The callbacks are stated with their natural growths, constant or linear in code size;
-- `hasProgramIn_keepWiresFn` takes them polynomial in these by `HasProgramIn.isPoly` and compares
-- the growths with the scale.
theorem hasProgramIn_keepWiresTest : HasProgramIn keepWiresTest hole(⊢ program)
    IsO(fun _ => 1) IsO(fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programKeepWiresTest
  fill_hole program in source_fun_prop

theorem hasProgramIn_keepWiresNextFn : HasProgramIn keepWiresNextFn hole(⊢ program)
    IsO(fun x => ⌜x⌝ₜ.size) IsO(fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programKeepWiresNextFn
  fill_hole program in source_fun_prop

theorem hasProgramIn_keepWiresFinishFn : HasProgramIn keepWiresFinishFn hole(⊢ program)
    IsO(fun x => ⌜x⌝ₜ.size) IsO(fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programKeepWiresFinishFn
  fill_hole program in source_fun_prop

theorem hasProgramIn_keepWiresResume :
    HasProgramIn (fun x : keepWiresRecursion.Return => keepWiresResumeFn x.1 x.2) hole(⊢ program)
      IsO(fun _ => 1) IsO(fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programKeepWiresResume
  fill_hole program in source_fun_prop

/-- The recursive program, polynomial in `keepWiresScale`: the recursion cost of its callbacks. -/
theorem hasProgramIn_keepWiresFn : HasProgramIn keepWiresFn hole(⊢ program)
    (IsPoly keepWiresScale) (IsPoly keepWiresScale) := by
  abstract_hole program using programKeepWiresFn
  have hsize : IsPoly keepWiresScale fun x => ⌜x⌝ₜ.size := by dominated [keepWiresScale]
  fill_hole program in
    exact keepWiresRecursion.hasProgramIn_isPoly keepWiresScale keepWiresScale_next_le
      (by dominated [keepWiresScale, keepWiresRecursion])
      hsize (by dominated [keepWiresScale, keepWiresFn, Circuit.size_keepWires])
      hasProgramIn_keepWiresTest.isPoly (.const 1) hsize
      hasProgramIn_keepWiresNextFn.isPoly hsize hsize
      hasProgramIn_keepWiresFinishFn.isPoly (hsize.comp .refl) (hsize.comp .refl)
      hasProgramIn_keepWiresResume.isPoly (.const 1) .refl

/-- Keep selected wires of a circuit computed by a selected implementation, given as a
`FinVector`. -/
theorem Internal.HasProgramInO.keepWires {ρ : Type} [UniqueEncoding Tree ρ]
    {p n m : ρ → ℕ} {c : (x : ρ) → Circuit .booleanAlgebra (n x) (m x)}
    {w : (x : ρ) → FinVector (Fin (n x)) (p x)} {t s : ρ → ℕ}
    {q : Value → Code Value}
    (h : HasProgramInO (fun x => (⟨p x, n x, m x, c x, w x⟩ : KeepWiresInput)) q t s) :
    HasProgramInO (fun x => (c x).keepWires (w x).get) (fun v => q v >>= programKeepWiresFn)
      (fun x => t x + hasProgramIn_keepWiresFn.time ⟨p x, n x, m x, c x, w x⟩)
      (fun x => max (s x) (hasProgramIn_keepWiresFn.peak ⟨p x, n x, m x, c x, w x⟩)) :=
  h.comp_dependent hasProgramIn_keepWiresFn.hasProgramInO

attribute [fun_prop] HasProgramInO.keepWires

/-- The argument of `Circuit.keepInputs`. -/
@[tree_encoding]
structure KeepInput where
  /-- Inputs of the circuit. -/
  n : ℕ
  /-- Outputs of the circuit. -/
  m : ℕ
  /-- The circuit whose inputs are kept. -/
  circuit : Circuit .booleanAlgebra n m

/-- `Circuit.keepInputs` on its packed argument, as `keepWires` on the `FinVector` of all
inputs. -/
def keepFn (x : KeepInput) := x.circuit.keepWires (FinVector.finRange x.n).get

/-- The numeric scale of the growth of `keepInputs`: the dimensions and twice the gate count. -/
def keepScale (x : KeepInput) : ℕ := x.n + x.m + 2 * x.circuit.size + 1

/-- The program for `keepWires` on the `FinVector` of all inputs, polynomial in `keepScale`. -/
theorem hasProgramIn_keepFn :
    HasProgramIn keepFn hole(⊢ program) (IsPoly keepScale) (IsPoly keepScale) := by
  abstract_hole program using programKeepFn
  fill_hole program in source_fun_prop (disch := dominated [keepScale, keepWiresScale])

/-- Keep the inputs of a circuit computed by a selected implementation. -/
theorem Internal.HasProgramInO.keepInputs {ρ : Type} [UniqueEncoding Tree ρ]
    {n m : ρ → ℕ} {c : (x : ρ) → Circuit .booleanAlgebra (n x) (m x)} {t p : ρ → ℕ}
    {q : Value → Code Value}
    (h : HasProgramInO (fun x => (⟨n x, m x, c x⟩ : KeepInput)) q t p) :
    HasProgramInO (fun x => (c x).keepInputs) (fun v => q v >>= programKeepFn)
      (fun x => t x + hasProgramIn_keepFn.time ⟨n x, m x, c x⟩)
      (fun x => max (p x) (hasProgramIn_keepFn.peak ⟨n x, m x, c x⟩)) :=
  h.comp_dependent hasProgramIn_keepFn.hasProgramInO

attribute [fun_prop] HasProgramInO.keepInputs

end Complexity.TreeProgram.Source
