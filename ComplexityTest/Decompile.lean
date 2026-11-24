/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Classes.TreeFunctions.Guard

open Complexity TreeProgram TreeProgram.Source

namespace Complexity.DecompileTest

variable {α β γ : Type} [UniqueEncoding Tree α] [UniqueEncoding Tree β] [UniqueEncoding Tree γ]

-- Guards that an abstract member of `FP` is composed by the source translation once decompiled:
-- mapping the second component of a pair. The size of the callee's output is supplied by
-- `size_encode` at the argument the call receives. If this needs more, composing with abstract
-- members costs more than the decompiled program and one `model_fun_prop`.
example {g : β → γ} (hg : g ∈ FP .sizeCostTree) :
    (fun x : α × β ↦ (x.1, g x.2)) ∈ FP .sizeCostTree := by
  obtain ⟨pg, hpg⟩ := TreeMachine.exists_hasProgramIn_of_mem_fp hg
  have := hpg.hasProgramInO.size_encode.comp (fun x : α × β => x.2)
  model_fun_prop

-- Guards pairing two abstract members, with the sizes of both outputs supplied.
example {f : α → β} {g : α → γ} (hf : f ∈ FP .sizeCostTree) (hg : g ∈ FP .sizeCostTree) :
    (fun x ↦ (f x, g x)) ∈ FP .sizeCostTree := by
  obtain ⟨pf, hpf⟩ := TreeMachine.exists_hasProgramIn_of_mem_fp hf
  obtain ⟨pg, hpg⟩ := TreeMachine.exists_hasProgramIn_of_mem_fp hg
  have := hpf.hasProgramInO.size_encode
  have := hpg.hasProgramInO.size_encode
  model_fun_prop

-- Guards composition of two abstract members, with the size of the intermediate value supplied.
-- Unlike `TreeMachine.fp_comp`, this route needs unique encodings, so it does not replace it.
example {f : α → β} {g : β → γ} (hg : g ∈ FP .sizeCostTree) (hf : f ∈ FP .sizeCostTree) :
    g ∘ f ∈ FP .sizeCostTree := by
  obtain ⟨pf, hpf⟩ := TreeMachine.exists_hasProgramIn_of_mem_fp hf
  obtain ⟨pg, hpg⟩ := TreeMachine.exists_hasProgramIn_of_mem_fp hg
  have := hpf.hasProgramInO.size_encode
  model_fun_prop

-- Records a limit (W69): without the size of the decompiled callee's output, the peak growth
-- `⌜(x.1, g x.2)⌝ₜ.size` is left open. If this starts to succeed, the translation knows the output
-- sizes of local implementations, and the `size_encode` facts above can be dropped.
example {g : β → γ} (hg : g ∈ FP .sizeCostTree) :
    (fun x : α × β ↦ (x.1, g x.2)) ∈ FP .sizeCostTree := by
  obtain ⟨pg, hpg⟩ := TreeMachine.exists_hasProgramIn_of_mem_fp hg
  fail_if_success (model_fun_prop; done)
  have := hpg.hasProgramInO.size_encode.comp (fun x : α × β => x.2)
  model_fun_prop

-- Records a limit: a free variable used as a constant has no implementation for the translation,
-- which asks for a `HasProgramIn` hypothesis. If this starts to succeed, the local function
-- `c : Unit → γ` in `TreeMachine.fp_option_elim` is no longer needed.
example (b : γ) : (fun _ : Bool => b) ∈ FP .sizeCostTree := by
  fail_if_success model_fun_prop
  exact (Internal.HasProgramInO.const b).mem_fp_sizeCost (by dominated) (by dominated)

-- Records a limit: `Option.elim` has no selected implementation, so `TreeMachine.fp_option_elim`
-- translates a `match` given with `via`. If this starts to succeed, the `via` is no longer needed.
example (f : α → Bool) (hf : f ∈ FP .sizeCostTree) :
    (fun o : Option α ↦ o.elim false f) ∈ FP .sizeCostTree := by
  obtain ⟨pf, hpf⟩ := TreeMachine.exists_hasProgramIn_of_mem_fp hf
  fail_if_success model_fun_prop
  exact TreeMachine.fp_option_elim hf false

-- Records a limit: `bif` (`cond`) has no selected implementation, unlike `if`. If this starts to
-- succeed, `cond` is translated as `if` is.
example : (fun y : α × Bool ↦ bif y.2 then some y.1 else none) ∈ FP .sizeCostTree := by
  fail_if_success model_fun_prop
  model_fun_prop via (fun y : α × Bool ↦ if y.2 then some y.1 else none)
  case source_eq => funext y; cases y.2 <;> rfl

end Complexity.DecompileTest
