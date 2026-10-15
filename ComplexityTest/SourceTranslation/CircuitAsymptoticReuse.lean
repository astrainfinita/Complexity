/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import ComplexityTest.SourceTranslation.CircuitComposition

open Complexity TreeProgram Complexity.TreeProgram.Source
open ComplexityTest.SourceTranslation.CircuitComposition

namespace ComplexityTest.SourceTranslation.CircuitAsymptoticReuse

noncomputable def recalled : Implementation rewireStored := by source_fun_prop

-- Importing the saved asymptotic result restores exactly the previously selected program.
example : recalled.program = rewireStoredImplementation.program := by
  simpa only [recalled] using rewireStored_ftisp.program_sourceImplementation
example : recalled.HasGrowth (fun x => ⌜x⌝ₜ.size ^ 7) (fun x => ⌜x⌝ₜ.size ^ 4) :=
  rewireStored_ftisp.hasGrowth_sourceImplementation

example : relabelImplementation.HasGrowth
    (fun x => relabelScale x ^ 7) (fun x => relabelScale x ^ 4) := relabel_growth
example : compImplementation.HasGrowth
    (fun x => compScale x ^ 7) (fun x => compScale x ^ 4) := comp_growth
example : keepImplementation.HasGrowth
    (fun x => keepScale x ^ 8) (fun x => keepScale x ^ 4) := keep_growth

-- The ordinary composition adapter consumes the raw selected implementation.
example {ρ : Type} [UniqueEncoding Tree ρ]
    (h : Implementation (fun _ : ρ => (⟨0, 0, 0, Circuit.id _ 0, Circuit.id _ 0⟩ : CompInput))) :
    (h.circuitComp).program = (h.comp compImplementation).program := rfl

example : keepImplementation.program =
    (keepRecursion.implementation keepCheck keepNext keepFinish
      keepResume).program := rfl

-- Binary dimensions are not bounded by code size without a hypothesis. Restrict only the
-- external source type; mapInput reuses the same program and its all-input certificate.
abbrev StoredComp := {x : CompInput // x.1 ≤ ⌜x⌝ₜ.size}
abbrev StoredKeep := {x : KeepInput // x.1 ≤ ⌜x⌝ₜ.size}

private theorem restrict_ftisp {α : Type} [UniqueEncoding Tree α] {f : α → Tree}
    (hf : Implementation f) (scale : α → ℕ) (d : ℕ)
    (growth : hf.HasGrowth (fun x => scale x ^ d) (fun x => scale x ^ 4))
    (P : α → Prop)
    (size : Dominated (fun x : {x // P x} => scale x.1) (fun x => ⌜x⌝ₜ.size)) :
    (fun x : {x // P x} => f x.1) ∈ FTISP .tree (fun n => n ^ d) (fun n => n ^ 4) := by
  let implementation := hf.mapInput (γ := {x // P x}) Subtype.val
    (fun x => (UniqueEncoding.encode_subtype x).symm)
  have h : implementation.HasGrowth
      (fun x => ⌜x⌝ₜ.size ^ d) (fun x => ⌜x⌝ₜ.size ^ 4) := by
    constructor
    · exact ((Dominated.comp growth.1 Subtype.val).trans (size.pow d))
    · exact ((Dominated.comp growth.2 Subtype.val).trans (size.pow 4))
  exact h.mem_ftisp_pow (by decide)

example : (fun x : StoredComp => ⌜compFn x.1⌝ₜ) ∈
    FTISP .tree (fun n => n ^ 7) (fun n => n ^ 4) := by
  apply restrict_ftisp compImplementation compScale 7 comp_growth
  refine Dominated.of_le_mul 8 ?_
  rintro ⟨⟨n, m, k, c, d⟩, hn⟩
  have hm := c.outputs_le_size_encode
  have hk := d.outputs_le_size_encode
  have hc := c.size_le_size_encode
  have hd := d.size_le_size_encode
  have hp := Tree.size_pos ⌜c⌝ₜ
  simp only [compScale, UniqueEncoding.encode_subtype, Sigma.encode_mk, size_encode_prod] at hn ⊢
  omega

example : (fun x : StoredKeep => ⌜keepFn x.1⌝ₜ) ∈
    FTISP .tree (fun n => n ^ 8) (fun n => n ^ 4) := by
  apply restrict_ftisp keepImplementation keepScale 8 keep_growth
  refine Dominated.of_le_mul 5 ?_
  rintro ⟨⟨n, m, c⟩, hn⟩
  have hm := c.outputs_le_size_encode
  have hc := c.size_le_size_encode
  have hp := Tree.size_pos ⌜c⌝ₜ
  simp only [keepScale, UniqueEncoding.encode_subtype, Sigma.encode_mk, size_encode_prod] at hn ⊢
  omega

-- Ordinary nested source calls use the saved keep specification, retaining structural costs.
noncomputable def preserveImplementation : Implementation preserve := by source_fun_prop
example : preserveImplementation.HasGrowth
    (fun x => ⌜x⌝ₜ.size + keepScale x ^ 8) (fun x => ⌜preserve x⌝ₜ.size + ⌜x⌝ₜ.size + keepScale x ^ 4) := by
  source_fun_prop
  · simp only [Dominated.add_iff]
    repeat' apply And.intro
    all_goals first
      | exact Dominated.const_of_pos _ (fun x => Nat.add_pos_left (Tree.size_pos _) _)
      | (apply Dominated.of_le
         rintro ⟨n, m, c⟩
         simp only [Sigma.encode_mk, size_encode_prod]
         omega)
  · apply Dominated.of_le
    rintro ⟨n, m, c⟩
    simp only [Function.comp_apply, preserve, keepFn, Sigma.encode_mk, size_encode_prod,
      Tree.encode_self, max_self]
    omega

end ComplexityTest.SourceTranslation.CircuitAsymptoticReuse
