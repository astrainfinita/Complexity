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
example : HasProgramInO rewireStored programRewireStored hasProgramIn_rewireStored.time
    hasProgramIn_rewireStored.peak := by
  source_fun_prop

-- The generators state the kind of their growths, polynomial in their scales.
example : HasProgramIn relabelFn programRelabelFn (IsPoly relabelScale) (IsPoly relabelScale) :=
  hasProgramIn_relabelFn
example : HasProgramIn compFn programCompFn (IsPoly compScale) (IsPoly compScale) :=
  hasProgramIn_compFn
example : HasProgramIn keepFn programKeepFn (IsPoly keepScale) (IsPoly keepScale) :=
  hasProgramIn_keepFn

-- The ordinary composition adapter consumes the raw selected implementation.
example {ρ : Type} [UniqueEncoding Tree ρ] {q : Value → Code Value} {t p : ρ → ℕ}
    (h : HasProgramInO (fun _ : ρ => (⟨0, 0, 0, Circuit.id _ 0, Circuit.id _ 0⟩ : CompInput))
      q t p) :=
  (h.circuitComp : type_of% (h.comp_dependent hasProgramIn_compFn.hasProgramInO))

example : programKeepWiresFn = Recursion.code programKeepWiresTest programKeepWiresNextFn
    programKeepWiresFinishFn programKeepWiresResume := rfl

-- Binary dimensions are not bounded by code size without a hypothesis. Restrict only the
-- external source type; map_input reuses the same program and its all-input certificate. The
-- output types depend on the input, so the class membership is stated for the output codes.
abbrev StoredComp := {x : CompInput // x.n ≤ ⌜x⌝ₜ.size}
abbrev StoredKeep := {x : KeepInput // x.n ≤ ⌜x⌝ₜ.size}

example : (fun x : StoredComp => ⌜compFn x.1⌝ₜ) ∈ FP .tree :=
  ((hasProgramIn_compFn.hasProgramInO.of_encode fun _ => Tree.encode_self _).map_input Subtype.val
    fun x => (UniqueEncoding.encode_subtype x).symm).mem_fp (by
      dominated [compScale, Circuit.outputs_le_size_encode,
        Circuit.size_le_size_encode])

example : (fun x : StoredKeep => ⌜keepFn x.1⌝ₜ) ∈ FP .tree :=
  ((hasProgramIn_keepFn.hasProgramInO.of_encode fun _ => Tree.encode_self _).map_input Subtype.val
    fun x => (UniqueEncoding.encode_subtype x).symm).mem_fp (by
      dominated [keepScale, Circuit.outputs_le_size_encode,
        Circuit.size_le_size_encode])

-- Ordinary nested source calls use the selected keep implementation, retaining structural costs.
example : HasProgramInO preserve hole(⊢ program)
    (fun x => ⌜x⌝ₜ.size + hasProgramIn_keepFn.time ⟨x.1, x.2.1, x.2.2⟩)
    (fun x => ⌜preserve x⌝ₜ.size + ⌜x⌝ₜ.size + hasProgramIn_keepFn.peak ⟨x.1, x.2.1, x.2.2⟩) := by
  fill_hole program in source_fun_prop (disch := dominated [preserve])

end ComplexityTest.SourceTranslation.CircuitAsymptoticReuse
