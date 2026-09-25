/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Program.Pair
public import Complexity.Models.TuringMachine.Program.Specification.Trace

/-! # Configuration specifications for composing tree programs -/

@[expose] public section

namespace Complexity.TreeMachine.Program

open TM.Program.Word Std.WP

variable {κ : Type} [DecidableEq κ] {xs : Array (Option Bool)}

/-- Pair construction on configurations, hiding the internal visitation history. -/
@[spec]
theorem spec_pair_cfg (c : TM.Cfg κ (Option Bool) Unit xs) (i j l : κ)
    (u v : List Bool) (z : ℕ) (hij : i ≠ j) (hil : i ≠ l)
    (hw : c.workTapes i = tape []) (hu : c.workTapes j = tape u)
    (hv : c.workTapes l = tape v) (hi : c.workPos i = 0)
    (hj : c.workPos j = 0) (hl : c.workPos l = 0) :
    Triple ((pair i j l).verify (TM.Program.cfgSemantics xs))
      (fun s b ↦ s = c ∧ b = 9 * (u.length + v.length) + 20 + z)
      (fun _ s b ↦ s = paired c i u v ∧ b = z) () := by
  let L : κ → ℤ := fun q ↦ min (c.workPos q) (-1)
  let R : κ → ℤ := fun q ↦ max (c.workPos q) (u.length + v.length + 1)
  have hf : PairFootprint c i j l u v L R := by
    constructor
    · intro q
      simp only [L, R, Set.mem_Icc]
      omega
    · intro r hl hr
      have hm (q : κ) : (r : ℤ) ∈ Set.Icc (L q) (R q) := by
        simp only [L, R, Set.mem_Icc]
        omega
      exact ⟨hm i, hm j, hm l⟩
  apply TM.Program.cfg_of_trace (spec_pair c i j l u v L R z hij hil hw hu hv hi hj hl hf)
  · rintro s b ⟨hs, hb⟩
    subst s
    exact ⟨rfl, hf.1, hb⟩
  · intro a s b h
    exact ⟨h.1, h.2.2⟩

end Complexity.TreeMachine.Program
