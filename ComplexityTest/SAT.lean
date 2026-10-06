/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Problems.CircuitSAT.Basic
import Complexity.Problems.ThreeSAT.Basic
import Complexity.Data.CNF.TreeEncoding
import Complexity.Encoding.Nat

namespace Complexity.SATTest

section Circuits

open FirstOrder FirstOrder.BooleanAlgebra

example : CircuitSAT ⟨0, Circuit.ofGate topFunc Fin.elim0⟩ := by simp

example : ¬ CircuitSAT ⟨0, Circuit.ofGate botFunc Fin.elim0⟩ := by simp

def contradiction : Circuit Language.booleanAlgebra 1 1 :=
  .gate complFunc ![0] (.gate infFunc ![0, 1] (.outputs fun _ => 2))

example : ¬ CircuitSAT ⟨1, contradiction⟩ := by
  rintro ⟨x, h⟩
  simp [contradiction, Function.comp_def, Fin.snoc] at h

section FixedInterpretation

local instance : Language.booleanAlgebra.Structure Bool where
  funMap _ _ := false

example : (Circuit.ofGate topFunc (Fin.elim0 : Fin 0 → Fin 0)).eval Fin.elim0 0 = false := rfl

example : CircuitSAT ⟨0, Circuit.ofGate topFunc Fin.elim0⟩ := by simp

end FixedInterpretation

end Circuits

open CNF

def sample : ThreeCNF ℕ := ⟨[[.pos 0, .neg 1], [.neg 0]], by decide⟩

example : ThreeSAT sample := ⟨fun _ => false, rfl⟩

example : ThreeSAT ⟨[], by simp⟩ := by simp

example : ¬ ThreeSAT ⟨[[]], by decide⟩ := ThreeSAT.not_of_nil_mem (by simp)

example : ¬ ThreeSAT ⟨[[.pos 0], [.neg 0]], by decide⟩ := by
  rintro ⟨x, h⟩
  cases hx : x 0 <;> simp [CNF.eval, hx] at h

example : ThreeSAT ⟨[[.pos 1000000]], by decide⟩ := ⟨fun _ => true, rfl⟩

example : UniqueEncoding Tree (CNF ℕ) := inferInstance

example (f : CNF ℕ) : decode (CNF ℕ) (encode Tree f) = Part.some f :=
  UniqueEncoding.decode_encode f

example (f : ThreeCNF ℕ) : encode Tree f = encode Tree f.val := rfl

example (f : ThreeCNF ℕ) : decode (ThreeCNF ℕ) (encode Tree f) = Part.some f :=
  UniqueEncoding.decode_encode f

example : decode (ThreeCNF ℕ)
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

open TreeProgram TreeProgram.Code

example {α : Type*} [UniqueEncoding Tree α] (a : α) :
    (Literal.Code.mk .input .nil).Computes
      (encode Tree a) (encode Tree (Literal.neg a)) := by
  simp [computes_iff]

end Complexity.SATTest
