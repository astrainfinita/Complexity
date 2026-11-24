/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Classes.TreeFunctions.Decompile
public import Complexity.Classes.TreeFunctions.Composition
public import Complexity.Encoding.Option

/-! # Guarding a polynomial-time function by a recognizer of codes

`fp_guard`: a verifier on typed witnesses `V : α × W → Bool` and a polynomial-time recognizer of
the codes of `W` give a polynomial-time verifier on trees that rejects the trees that are not
codes of `W`.

The abstract members of `FP .sizeCostTree` are decompiled into tree programs
(`exists_hasProgramIn_of_mem_fp`) and composed by the source translation (`model_fun_prop`). The
retyping of a guarded input from `α × Tree` to `α × W` reads the codes of the guard's outputs at
another type. This is the current way to compose with an abstract member of `FP`, not a decision;
the names are provisional.
-/

@[expose] public section

namespace Complexity.TreeMachine

open TreeProgram TreeProgram.Source

variable {α β γ : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β] [UniqueEncoding Tree γ]

/-- `o ↦ o.elim b f`: the decompiled program of `f` on the value of the option, by translation.

The translation takes no free constant, so the default `b` is passed to it as a local function
`c : Unit → γ` with the program writing `⌜b⌝ₜ`; the growths are proved by hand, since `dominated`
compares them only pointwise in the branches of the `match`. Both are the current workarounds,
not decisions. -/
theorem fp_option_elim {f : β → γ} (hf : f ∈ FP .sizeCostTree) (b : γ) :
    (fun o : Option β ↦ o.elim b f) ∈ FP .sizeCostTree := by
  obtain ⟨pf, hpf⟩ := exists_hasProgramIn_of_mem_fp hf
  obtain ⟨c, hc, hpc⟩ : ∃ c : Unit → γ, c = (fun _ => b) ∧
      HasProgramIn c (fun _ => Code.eval (.ofTree ⌜b⌝ₜ)) IsO(fun _ => 1) IsO(fun _ => 1) :=
    ⟨_, rfl, (Internal.HasProgramInO.const b).toHasProgramIn⟩
  model_fun_prop via (fun o : Option β => match o with | none => c () | some z => f z)
  case source_eq => funext o; cases o <;> simp [hc]
  case time =>
    obtain ⟨T, hT, hTp, hle⟩ := hpf.time_spec.exists_monotone
    refine IsPoly.of_dominated (g := fun o : Option β => 3 + T ⌜o⌝ₜ.size) (by dominated)
      (Dominated.of_le fun o => ?_)
    rcases o with _ | z
    · dsimp only; omega
    · have hs : ⌜z⌝ₜ.size + 2 = ⌜some z⌝ₜ.size := by
        simp only [encode_option_some, size_encode_prod, size_encode_unit]; omega
      have := hT (show ⌜z⌝ₜ.size ≤ ⌜some z⌝ₜ.size by omega)
      have := hle z
      dsimp only; omega
  case peak =>
    obtain ⟨T, hT, hTp, hle⟩ := hpf.peak_spec.exists_monotone
    refine IsPoly.of_dominated (g := fun o : Option β => 2 + 2 * ⌜o⌝ₜ.size + T ⌜o⌝ₜ.size)
      (by dominated) (Dominated.of_le fun o => ?_)
    rcases o with _ | z
    · simp only [max_le_iff]; omega
    · have hs : ⌜z⌝ₜ.size + 2 = ⌜some z⌝ₜ.size := by
        simp only [encode_option_some, size_encode_prod, size_encode_unit]; omega
      have := hT (show ⌜z⌝ₜ.size ≤ ⌜some z⌝ₜ.size by omega)
      have := hle z
      simp only [max_le_iff]; omega

/-- A verifier on typed witnesses, guarded by a polynomial-time recognizer of the codes of the
witness type, is a polynomial-time verifier on trees that rejects the trees that are not codes. -/
theorem fp_guard {W : Type*} [UniqueEncoding Tree W] (check : Tree → Bool)
    (hcheck : check ∈ FP .sizeCostTree) (hW : ∀ t, check t = true ↔ ∃ w : W, ⌜w⌝ₜ = t)
    (V : α × W → Bool) (hV : V ∈ FP .sizeCostTree) :
    ∃ V' : α × Tree → Bool, V' ∈ FP .sizeCostTree ∧
      ∀ a t, V' (a, t) = true ↔ ∃ w : W, ⌜w⌝ₜ = t ∧ V (a, w) = true := by
  obtain ⟨pc, hpc⟩ := exists_hasProgramIn_of_mem_fp hcheck
  -- The guard keeps the input when its second component is a code of `W`.
  have hguard : (fun x : α × Tree ↦ if check x.2 then some x else none) ∈ FP .sizeCostTree := by
    model_fun_prop
  -- The same output codes, read at `Option (α × W)`.
  let guard (x : α × Tree) : Option (α × W) :=
    if h : check x.2 = true then some (x.1, ((hW x.2).1 h).choose) else none
  have hguard' : guard ∈ FP .sizeCostTree := by
    obtain ⟨u, s, hc, hu⟩ := FP.mem_iff_isPoly.1 hguard
    refine FP.mem_iff_isPoly.2 ⟨u, s, hc.of_encode fun ⟨a, t⟩ => ?_, hu⟩
    by_cases h : check t = true
    · simp only [guard, h, ↓reduceDIte, ↓reduceIte, encode_option_some, encode_prod,
        ((hW t).1 h).choose_spec, Tree.encode_self]
    · simp only [guard, h, Bool.false_eq_true, ↓reduceDIte, ↓reduceIte, encode_option_none]
  refine ⟨fun x => (guard x).elim false V, fp_comp (fp_option_elim hV false) hguard',
    fun a t => ?_⟩
  by_cases h : check t = true
  · have hw := ((hW t).1 h).choose_spec
    simp only [guard, h, ↓reduceDIte, Option.elim_some]
    exact ⟨fun hv => ⟨_, hw, hv⟩, fun ⟨w, hwt, hv⟩ => by
      rwa [← UniqueEncoding.encode_injective (hwt.trans hw.symm)]⟩
  · simp only [guard, h, ↓reduceDIte, Option.elim_none, Bool.false_eq_true, false_iff]
    exact fun ⟨w, hwt, _⟩ => h ((hW t).2 ⟨w, hwt⟩)

end Complexity.TreeMachine
