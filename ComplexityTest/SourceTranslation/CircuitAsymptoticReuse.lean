/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import ComplexityTest.SourceTranslation.CircuitComposition

open Complexity TreeProgram Complexity.TreeProgram.Source
open Complexity.TreeProgram.Source.Internal (HasProgramInO)
open ComplexityTest.SourceTranslation.CircuitComposition

namespace ComplexityTest.SourceTranslation.CircuitAsymptoticReuse

-- Importing the selected implementation restores exactly the same program and growth.
example : HasProgramInO rewireStored programRewireStored (fun x => ⌜x⌝ₜ.size ^ 7)
    (fun x => ⌜x⌝ₜ.size ^ 4) := by
  source_fun_prop

example : HasProgramInO relabelFn programRelabelFn
    (fun x => relabelScale x ^ 7) (fun x => relabelScale x ^ 4) :=
  hasProgramIn_relabelFn.toHasProgramInO
example : HasProgramInO compFn programCompFn
    (fun x => compScale x ^ 7) (fun x => compScale x ^ 4) := hasProgramIn_compFn.toHasProgramInO
example : HasProgramInO keepFn programKeepFn
    (fun x => keepScale x ^ 7) (fun x => keepScale x ^ 4) := hasProgramIn_keepFn.toHasProgramInO

-- The ordinary composition adapter consumes the raw selected implementation.
example {ρ : Type} [UniqueEncoding Tree ρ] {q : Value → Code Value} {t p : ρ → ℕ}
    (h : HasProgramInO (fun _ : ρ => (⟨0, 0, 0, Circuit.id _ 0, Circuit.id _ 0⟩ : CompInput))
      q t p) :=
  (h.circuitComp : type_of% (h.comp_dependent hasProgramIn_compFn.toHasProgramInO))

example : programKeepWiresFn = Recursion.code programKeepWiresTest programKeepWiresNextFn
    programKeepWiresFinishFn programKeepWiresResume := rfl

-- Binary dimensions are not bounded by code size without a hypothesis. Restrict only the
-- external source type; map_input reuses the same program and its all-input certificate. The
-- output types depend on the input, so the class membership is stated for the output codes.
abbrev StoredComp := {x : CompInput // x.n ≤ ⌜x⌝ₜ.size}
abbrev StoredKeep := {x : KeepInput // x.n ≤ ⌜x⌝ₜ.size}

private theorem restrict_fdtisp {α : Type} [UniqueEncoding Tree α] {f : α → Tree}
    {program : Value → Code Value} (scale : α → ℕ) (d : ℕ)
    (hf : HasProgramInO f program (fun x => scale x ^ d) (fun x => scale x ^ 4))
    (P : α → Prop)
    (size : Dominated (fun x : {x // P x} => scale x.1) (fun x => ⌜x⌝ₜ.size)) :
    (fun x : {x // P x} => f x.1) ∈ FDTISP .tree (fun n => n ^ d) (fun n => n ^ 4) :=
  ((hf.map_input Subtype.val (fun x => (UniqueEncoding.encode_subtype x).symm)).mono
    (size.pow d) (size.pow 4)).mem_fdtisp_pow (by decide)

example : (fun x : StoredComp => ⌜compFn x.1⌝ₜ) ∈
    FDTISP .tree (fun n => n ^ 7) (fun n => n ^ 4) := by
  apply restrict_fdtisp compScale 7
    (hasProgramIn_compFn.toHasProgramInO.of_encode fun _ => Tree.encode_self _)
  refine Dominated.of_le_mul 8 ?_
  rintro ⟨⟨n, m, k, c, d⟩, hn⟩
  have hm := c.outputs_le_size_encode
  have hk := d.outputs_le_size_encode
  have hc := c.size_le_size_encode
  have hd := d.size_le_size_encode
  have hp := Tree.size_pos ⌜c⌝ₜ
  simp only [compScale, UniqueEncoding.encode_subtype, CompInput.encode_mk, size_encode_prod] at hn ⊢
  omega

example : (fun x : StoredKeep => ⌜keepFn x.1⌝ₜ) ∈
    FDTISP .tree (fun n => n ^ 7) (fun n => n ^ 4) := by
  apply restrict_fdtisp keepScale 7
    (hasProgramIn_keepFn.toHasProgramInO.of_encode fun _ => Tree.encode_self _)
  refine Dominated.of_le_mul 5 ?_
  rintro ⟨⟨n, m, c⟩, hn⟩
  have hm := c.outputs_le_size_encode
  have hc := c.size_le_size_encode
  have hp := Tree.size_pos ⌜c⌝ₜ
  simp only [keepScale, UniqueEncoding.encode_subtype, KeepInput.encode_mk, size_encode_prod] at hn ⊢
  omega

-- Ordinary nested source calls use the selected keep implementation, retaining structural costs.
example : HasProgramInO preserve hole(⊢ program) (fun x => ⌜x⌝ₜ.size + keepScale ⟨x.1, x.2.1, x.2.2⟩ ^ 7)
    (fun x => ⌜preserve x⌝ₜ.size + ⌜x⌝ₜ.size + keepScale ⟨x.1, x.2.1, x.2.2⟩ ^ 4) := by
  fill_hole program in source_fun_prop (disch := dominated [preserve])

end ComplexityTest.SourceTranslation.CircuitAsymptoticReuse
