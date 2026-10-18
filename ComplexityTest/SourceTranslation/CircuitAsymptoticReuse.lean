/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import ComplexityTest.SourceTranslation.CircuitComposition

open Complexity TreeProgram Complexity.TreeProgram.Source
open ComplexityTest.SourceTranslation.CircuitComposition

namespace ComplexityTest.SourceTranslation.CircuitAsymptoticReuse

-- Importing the selected implementation restores exactly the same program and growth.
example : (by source_fun_prop : Implementation rewireStored _ _).program =
    rewireStoredImplementation.program := rfl
example : Implementation rewireStored (fun x => ⌜x⌝ₜ.size ^ 7) (fun x => ⌜x⌝ₜ.size ^ 4) := by
  source_fun_prop

example : Implementation (fun x => ⌜relabelFn x⌝ₜ)
    (fun x => relabelScale x ^ 7) (fun x => relabelScale x ^ 4) := relabelImplementation
example : Implementation (fun x => ⌜compFn x⌝ₜ)
    (fun x => compScale x ^ 7) (fun x => compScale x ^ 4) := compImplementation
example : Implementation (fun x => ⌜keepFn x⌝ₜ)
    (fun x => keepScale x ^ 8) (fun x => keepScale x ^ 4) := keepImplementation

-- The ordinary composition adapter consumes the raw selected implementation.
example {ρ : Type} [UniqueEncoding Tree ρ] {t p : ρ → ℕ}
    (h : Implementation (fun _ : ρ => (⟨0, 0, 0, Circuit.id _ 0, Circuit.id _ 0⟩ : CompInput)) t p) :
    (h.circuitComp).program = (h.comp compImplementation).program := rfl

example : keepImplementation.program =
    (keepRecursion.implementation keepCheck keepNext keepFinish
      keepResume).program := rfl

-- Binary dimensions are not bounded by code size without a hypothesis. Restrict only the
-- external source type; mapInput reuses the same program and its all-input certificate.
abbrev StoredComp := {x : CompInput // x.n ≤ ⌜x⌝ₜ.size}
abbrev StoredKeep := {x : KeepInput // x.n ≤ ⌜x⌝ₜ.size}

private theorem restrict_ftisp {α : Type} [UniqueEncoding Tree α] {f : α → Tree}
    (scale : α → ℕ) (d : ℕ) (hf : Implementation f (fun x => scale x ^ d) (fun x => scale x ^ 4))
    (P : α → Prop)
    (size : Dominated (fun x : {x // P x} => scale x.1) (fun x => ⌜x⌝ₜ.size)) :
    (fun x : {x // P x} => f x.1) ∈ FTISP .tree (fun n => n ^ d) (fun n => n ^ 4) :=
  ((hf.mapInput (γ := {x // P x}) Subtype.val
    (fun x => (UniqueEncoding.encode_subtype x).symm)).mono (size.pow d) (size.pow 4)).mem_ftisp_pow
      (by decide)

example : (fun x : StoredComp => ⌜compFn x.1⌝ₜ) ∈
    FTISP .tree (fun n => n ^ 7) (fun n => n ^ 4) := by
  apply restrict_ftisp compScale 7 compImplementation
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
    FTISP .tree (fun n => n ^ 8) (fun n => n ^ 4) := by
  apply restrict_ftisp keepScale 8 keepImplementation
  refine Dominated.of_le_mul 5 ?_
  rintro ⟨⟨n, m, c⟩, hn⟩
  have hm := c.outputs_le_size_encode
  have hc := c.size_le_size_encode
  have hp := Tree.size_pos ⌜c⌝ₜ
  simp only [keepScale, UniqueEncoding.encode_subtype, KeepInput.encode_mk, size_encode_prod] at hn ⊢
  omega

-- Ordinary nested source calls use the selected keep implementation, retaining structural costs.
example : Implementation preserve (fun x => ⌜x⌝ₜ.size + keepScale ⟨x.1, x.2.1, x.2.2⟩ ^ 8)
    (fun x => ⌜preserve x⌝ₜ.size + ⌜x⌝ₜ.size + keepScale ⟨x.1, x.2.1, x.2.2⟩ ^ 4) := by
  source_fun_prop
  all_goals dominated [preserve]

end ComplexityTest.SourceTranslation.CircuitAsymptoticReuse
