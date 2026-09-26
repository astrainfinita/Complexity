/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Program.Pair
public import Complexity.Models.TuringMachine.Program.Specification.Tracked

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
  let V : κ → NonemptyInterval ℤ := fun q ↦
    ⟨(min (c.workPos q) (-1), max (c.workPos q) (u.length + v.length + 1)), by omega⟩
  have hf : PairFootprint i j l u v V := by
    intro r hl hr
    have hm (q : κ) : (r : ℤ) ∈ V q := by
      simp only [V, NonemptyInterval.mem_mk]
      omega
    exact ⟨hm i, hm j, hm l⟩
  apply TM.Program.cfg_of_tracked (spec_pair c i j l u v V z hij hil hw hu hv hi hj hl hf)
  · rintro s b ⟨hs, hb⟩
    subst s
    refine ⟨rfl, fun q ↦ ?_, hb⟩
    change c.workPos q ∈ V q
    simp only [V, NonemptyInterval.mem_mk]
    omega
  · intro a s b h
    exact ⟨h.1, h.2.2⟩

end Complexity.TreeMachine.Program
