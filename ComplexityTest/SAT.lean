/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Problems.CircuitSAT.KSAT
import Complexity.Problems.KSAT.Membership
import Complexity.Resources.Circuit.Tseitin
import Complexity.Encoding.RawWord
meta import Complexity.Models.Circuit.Tseitin
meta import Complexity.Problems.KSAT.Verifier

namespace Complexity.SATTest

section Circuits

open FirstOrder FirstOrder.BooleanAlgebra

example : CircuitSAT ⟨0, Circuit.ofGate topFunc Fin.elim0⟩ := by simp

example : ¬ CircuitSAT ⟨0, Circuit.ofGate botFunc Fin.elim0⟩ := by simp

def contradiction : Circuit Language.booleanAlgebra 1 1 :=
  .gate complFunc ![0] (.gate infFunc ![0, 1] (.outputs fun _ => 2))

theorem not_contradiction : ¬ CircuitSAT ⟨1, contradiction⟩ := by
  rintro ⟨x, h⟩
  simp [contradiction, Function.comp_def, Fin.snoc] at h

example : ¬ KSAT 3 ⟨contradiction.tseitin, contradiction.tseitin_width⟩ := by
  simpa only [← CircuitSAT.iff_ksat] using not_contradiction

#guard contradiction.tseitin.length == 6

example : KSAT 3
    ⟨(Circuit.ofGate topFunc (Fin.elim0 : Fin 0 → Fin 0)).tseitin,
      Circuit.tseitin_width _⟩ := by
  rw [← CircuitSAT.iff_ksat]
  simp

example : ¬ KSAT 3
    ⟨(Circuit.ofGate botFunc (Fin.elim0 : Fin 0 → Fin 0)).tseitin,
      Circuit.tseitin_width _⟩ := by
  rw [← CircuitSAT.iff_ksat]
  simp

/-- Sharing an input wire does not introduce an independent Boolean choice. -/
example (b : Bool) :
    (∃ a : ℕ → Bool, a 0 = b ∧
      (Circuit.ofGate infFunc ![0, 0] : Circuit _ 1 1).tseitin.eval a = true) ↔ b = true := by
  simpa using ((Circuit.ofGate infFunc ![0, 0] : Circuit _ 1 1).eval_eq_true_iff_tseitin
    (fun _ => b)).symm

/-- Unused inputs need neither fresh clauses nor a densely allocated variable table. -/
example : (Circuit.outputs (fun _ => (1000000 : Fin 1000001)) :
    Circuit .booleanAlgebra 1000001 1).tseitin = [ [CNF.Literal.pos 1000000] ] := by
  simp

/-- The bound applies directly to the serialized input and the width-certified output. -/
example (p : Σ n, Circuit .booleanAlgebra n 1) :
    ⌜(⟨p.2.tseitin, p.2.tseitin_width⟩ : KCNF 3 ℕ)⌝₂.length ≤ 8 * ⌜p⌝₂.length ^ 2 := by
  rcases p with ⟨n, c⟩
  simpa using c.size_encode_tseitin_le

section FixedInterpretation

local instance : Language.booleanAlgebra.Structure Bool where
  funMap _ _ := false

example : (Circuit.ofGate topFunc (Fin.elim0 : Fin 0 → Fin 0)).eval Fin.elim0 0 = false := rfl

example : CircuitSAT ⟨0, Circuit.ofGate topFunc Fin.elim0⟩ := by simp

example : KSAT 3
    ⟨(Circuit.ofGate topFunc (Fin.elim0 : Fin 0 → Fin 0)).tseitin,
      Circuit.tseitin_width _⟩ := by
  rw [← CircuitSAT.iff_ksat]
  simp

end FixedInterpretation

end Circuits

open CNF

def sample : KCNF 3 ℕ := ⟨[[.pos 0, .neg 1], [.neg 0]], by decide⟩

example : KSAT 3 sample := ⟨fun _ => false, rfl⟩

example (k : ℕ) : KSAT k ⟨[], by simp⟩ := by simp

example (k : ℕ) : ¬ KSAT k ⟨[[]], by simp⟩ := KSAT.not_of_nil_mem (by simp)

example : ¬ KSAT 1 ⟨[[.pos 0], [.neg 0]], by decide⟩ := by
  rintro ⟨x, h⟩
  cases hx : x 0 <;> simp [CNF.eval, hx] at h

example : KSAT 4 ⟨[[.pos 1000000, .neg 0, .neg 1, .neg 2]], by decide⟩ :=
  ⟨fun _ => true, rfl⟩

example : UniqueEncoding Tree (CNF ℕ) := inferInstance

example (f : CNF ℕ) : decode (CNF ℕ) (encode Tree f) = Part.some f :=
  UniqueEncoding.decode_encode f

example (k : ℕ) (f : KCNF k ℕ) : encode Tree f = encode Tree f.val := rfl

example (k : ℕ) (f : KCNF k ℕ) : decode (KCNF k ℕ) (encode Tree f) = Part.some f :=
  UniqueEncoding.decode_encode f

example : decode (KCNF 3 ℕ)
    (encode Tree ([[.pos 0, .pos 0, .pos 0, .pos 0]] : CNF ℕ)) = Part.none := by
  apply Part.eq_none_iff.mpr
  intro f hf
  have hcode := UniqueEncoding.mem_decode_iff.mp hf
  have heq : f.val = [[.pos 0, .pos 0, .pos 0, .pos 0]] := by
    simpa only [UniqueEncoding.encode_subtype, UniqueEncoding.encode_inj] using hcode
  have hwidth := f.property [.pos 0, .pos 0, .pos 0, .pos 0]
  simp [heq] at hwidth

example : encode Tree ([] : CNF ℕ) = .nil := rfl

example : encode Tree ([[]] : CNF ℕ) = .pair .nil .nil := rfl

example : decode (Literal ℕ) (Tree.pair .nil (.pair .nil (.pair .nil .nil))) = Part.none := by
  apply Part.eq_none_iff.mpr
  rintro ⟨a, p⟩ h
  rw [UniqueEncoding.mem_decode_iff] at h
  cases p <;> simp at h

section Verifiers

open FirstOrder.BooleanAlgebra

/-- One variable with a large number; a witness lists only true variables. -/
def sparse : KCNF 2 ℕ := ⟨[[.pos 1000000, .neg 0]], by decide⟩

#guard KSAT.verify 2 (sparse, [1000000])
#guard KSAT.verify 2 (sparse, [])
#guard !KSAT.verify 1 (⟨[[.pos 1000000], [.neg 1000000]], by decide⟩, [1000000])

-- Variables missing from the witness are false.
#guard !KSAT.verify 1 (⟨[[.pos 3]], by decide⟩, [0, 1, 2])

example : KSAT 2 sparse :=
  (KSAT.exists_verify_iff sparse).mpr ⟨[], List.nil_sublist _, rfl⟩

-- Circuits need no verifier of their own: the verifier of `3`-SAT after the Tseitin reduction
-- accepts exactly the satisfiable circuits, with the witnesses of the Tseitin formula. Guards
-- that the reduction and the verifier chain as stated, which the membership of `CircuitSAT` in
-- NP relies on.
example (c : Σ n, Circuit .booleanAlgebra n 1) :
    CircuitSAT c ↔ ∃ w : List ℕ, w.Sublist (CircuitSAT.toKSAT c).val.atoms ∧
      KSAT.verify 3 (CircuitSAT.toKSAT c, w) = true :=
  (CircuitSAT.toKSAT_correct c).trans (KSAT.exists_verify_iff _)

end Verifiers

open TreeProgram TreeProgram.Code

example {α : Type*} [UniqueEncoding Tree α] (a : α) :
    (Literal.Code.mk .input .nil).Computes
      (encode Tree a) (encode Tree (Literal.neg a)) := by
  simp [computes_iff]

-- The sparse verifier of `k`-SAT is polynomial-time in the size-charged tree model. Guards the
-- exit `KSAT.verify_fp`; its program is found by the translation alone, through the rule for
-- `CNF.eval` with the assignment as a callback and the view equation of membership.
example : KSAT.verify 3 ∈ FP .sizeCostTree := KSAT.verify_fp 3

-- Guards that the size of the Tseitin formula is known to `dominated`, also under the constructor
-- of the `3`-CNF that the reduction returns: no hint is passed.
open TreeProgram.Source in
example : IsPoly (fun c : Σ n, Circuit .booleanAlgebra n 1 => ⌜c⌝ₜ.size) fun c =>
    ⌜(⟨c.2.tseitin, c.2.tseitin_width⟩ : KCNF 3 ℕ)⌝ₜ.size := by
  dominated

-- Guards the statement of the verifier's program: a polynomial time and a linear peak.
open TreeProgram.Source in
example : HasProgramIn (KSAT.verify 3) KSAT.programVerify
    (IsPoly fun x => ⌜x⌝ₜ.size) IsO(fun x => ⌜x⌝ₜ.size) :=
  KSAT.hasProgramIn_verify 3

end Complexity.SATTest
