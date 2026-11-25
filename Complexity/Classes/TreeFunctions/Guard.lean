/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Classes.TreeFunctions.Decompile
public import Complexity.Classes.TreeFunctions.Composition
public import Complexity.Encoding.Option

/-! # Guarding a polynomial-time relation by a recognizer of codes

`p_guard`: a relation on typed witnesses `R : α × W → Prop` decided in polynomial time and a
polynomial-time recognizer of the codes of `W` give a relation on trees decided in polynomial time,
which holds only at codes of `W`.

The abstract members of `FP .sizeCostTree` are decompiled into tree programs
(`exists_hasProgramIn_of_mem_fp`) and composed by the source translation (`model_fun_prop`). The
retyping of a guarded input from `α × Tree` to `α × W` reads the codes of the guard's outputs at
another type, by decoding them (`Part.get`); this retyping, the two workarounds in
`fp_option_elim` and the names are the current state, not decisions.
-/

@[expose] public section

namespace Complexity.TreeMachine

open TreeProgram TreeProgram.Source

variable {α β γ : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β] [UniqueEncoding Tree γ]

/-- `o ↦ o.elim b f` is in `FP .sizeCostTree` when `f` is. -/
theorem fp_option_elim {f : β → γ} (hf : f ∈ FP .sizeCostTree) (b : γ) :
    (fun o : Option β ↦ o.elim b f) ∈ FP .sizeCostTree := by
  obtain ⟨pf, hpf⟩ := exists_hasProgramIn_of_mem_fp hf
  -- The translation takes no free constant, so the default `b` is passed to it as a local function
  -- `c : Unit → γ` with the program writing `⌜b⌝ₜ` (W88); the growths are proved by hand, since
  -- `dominated` compares them only pointwise in the branches of the `match` (W2). Both are the
  -- current workarounds, not decisions.
  obtain ⟨c, hc, hpc⟩ : ∃ c : Unit → γ, c = (fun _ => b) ∧
      HasProgramIn c (fun _ => Code.eval (.ofTree ⌜b⌝ₜ)) IsO(fun _ => 1) IsO(fun _ => 1) :=
    ⟨_, rfl, (Internal.HasProgramInO.const b).toHasProgramIn⟩
  model_fun_prop (disch := skip) via
    (fun o : Option β => match o with | none => c () | some z => f z)
  case source_eq => funext o; cases o <;> simp [hc]
  case time =>
    obtain ⟨T, hT, hTp, hle⟩ := hpf.time_spec.exists_monotone
    refine IsPoly.of_dominated (g := fun o : Option β => 3 + T ⌜o⌝ₜ.size) (by dominated)
      (Dominated.of_le fun o => ?_)
    rcases o with _ | z
    · dsimp only; omega
    · have hs := size_encode_option_some z
      have := hT (show ⌜z⌝ₜ.size ≤ ⌜some z⌝ₜ.size by omega)
      have := hle z
      dsimp only; omega
  case peak =>
    obtain ⟨T, hT, hTp, hle⟩ := hpf.peak_spec.exists_monotone
    refine IsPoly.of_dominated (g := fun o : Option β => 2 + 2 * ⌜o⌝ₜ.size + T ⌜o⌝ₜ.size)
      (by dominated) (Dominated.of_le fun o => ?_)
    rcases o with _ | z
    · simp only [max_le_iff]; omega
    · have hs := size_encode_option_some z
      have := hT (show ⌜z⌝ₜ.size ≤ ⌜some z⌝ₜ.size by omega)
      have := hle z
      simp only [max_le_iff]; omega

/-- A relation on typed witnesses decided in polynomial time, guarded by a polynomial-time
recognizer of the codes of the witness type, is a relation on trees decided in polynomial time that
holds only at codes. -/
theorem p_guard {W : Type*} [UniqueEncoding Tree W]
    (hW : (fun t : Tree => (decode W t).Dom) ∈ P .sizeCostTree)
    {R : α × W → Prop} (hR : R ∈ P .sizeCostTree) :
    (fun x : α × Tree => ∃ w : W, ⌜w⌝ₜ = x.2 ∧ R (x.1, w)) ∈ P .sizeCostTree := by
  obtain ⟨check, hcheck, hdec⟩ := hW
  obtain ⟨V, hV, hRV⟩ := hR
  obtain ⟨pc, hpc⟩ := exists_hasProgramIn_of_mem_fp hcheck
  -- The guard keeps the input when its second component is a code of `W`.
  have hguard : (fun x : α × Tree ↦ if check x.2 then some x else none) ∈ FP .sizeCostTree := by
    model_fun_prop
  -- The same output codes, read at `Option (α × W)`.
  let guard (x : α × Tree) : Option (α × W) :=
    if h : check x.2 = true then some (x.1, (decode W x.2).get ((hdec x.2).1 h)) else none
  have hguard' : guard ∈ FP .sizeCostTree := by
    obtain ⟨u, s, hc, hu⟩ := FP.mem_iff_isPoly.1 hguard
    refine FP.mem_iff_isPoly.2 ⟨u, s, hc.of_encode fun ⟨a, t⟩ => ?_, hu⟩
    by_cases h : check t = true
    · simp only [guard, h, ↓reduceDIte, ↓reduceIte, encode_option_some, encode_prod,
        UniqueEncoding.encode_of_mem_decode (Part.get_mem _), Tree.encode_self]
    · simp only [guard, h, Bool.false_eq_true, ↓reduceDIte, ↓reduceIte, encode_option_none]
  refine P.of_decides (fp_comp (fp_option_elim hV false) hguard') fun ⟨a, t⟩ => ?_
  by_cases h : check t = true
  · have hw := UniqueEncoding.encode_of_mem_decode (Part.get_mem ((hdec t).1 h))
    simp only [Function.comp_apply, guard, h, ↓reduceDIte, Option.elim_some]
    refine (hRV _).trans ⟨fun hv => ⟨_, hw, hv⟩, fun ⟨w, hwt, hv⟩ => ?_⟩
    rwa [← UniqueEncoding.encode_injective (hwt.trans hw.symm)]
  · simp only [Function.comp_apply, guard, h, ↓reduceDIte, Option.elim_none, Bool.false_eq_true,
      false_iff]
    exact fun ⟨w, hwt, _⟩ => h ((hdec t).2 (UniqueEncoding.dom_decode_iff.2 ⟨w, hwt⟩))

end Complexity.TreeMachine
