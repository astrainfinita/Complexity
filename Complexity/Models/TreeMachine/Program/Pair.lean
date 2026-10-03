/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TuringMachine.Program.Word.Configuration
public import Complexity.Models.TuringMachine.Program.Word.Write

/-! # Pair construction by composing verified tape programs -/

@[expose] public section

set_option experimental.vcgen true

namespace Complexity.TreeMachine.Program

open TM TM.Program.Word

open Std.WP

variable {κ : Type} [DecidableEq κ] {xs : Array (Option Bool)}

/-- Construct the pair of two encoded trees, then restore the destination head. -/
def pair (i j l : κ) : TM.Program κ (Option Bool) Unit := do
  put i (some true)
  append i j
  append i l
  rewind i

/-- Pair construction changes only the destination tape; all heads return to their entries. -/
def paired (c : TM.Cfg κ (Option Bool) Unit xs) (i : κ) (u v : List Bool) :
    TM.Cfg κ (Option Bool) Unit xs :=
  { c with workTapes := Function.update c.workTapes i (tape (true :: (u ++ v))) }

/-- Pair construction preserves the complete configuration and exact remaining budget.
The two source indices may coincide; only the destination must be distinct from each. -/
@[spec]
theorem spec_pair_cfg (c : TM.Cfg κ (Option Bool) Unit xs) (i j l : κ)
    (u v : List Bool) (z : ℕ) (hij : i ≠ j) (hil : i ≠ l)
    (hw : c.workTapes i = tape []) (hu : c.workTapes j = tape u)
    (hv : c.workTapes l = tape v) (hi : c.workPos i = 0)
    (hj : c.workPos j = 0) (hl : c.workPos l = 0) :
    Triple ((pair i j l).verify (TM.Program.cfgSemantics xs))
      (fun s b ↦ s = c ∧ b = 9 * (u.length + v.length) + 20 + z)
      (fun _ s b ↦ s = paired c i u v ∧ b = z) () := by
  let d := apply (putAction i (some true)) c
  let e := appended d i j [true] u
  let f := appended e i l (true :: u) v
  have hd (q : κ) : d.workPos q = if q = i then c.workPos q + 1 else c.workPos q :=
    workPos_putAction c i (some true) q
  have hdj : d.workPos j = 0 := by simp [hd, hij.symm, hj]
  have hdl : d.workPos l = 0 := by simp [hd, hil.symm, hl]
  have he (q : κ) : e.workPos q = if q = i then d.workPos q + u.length else d.workPos q :=
    workPos_appended_of_home d i j [true] u hij hdj q
  have hel : e.workPos l = 0 := by simp [he, hil.symm, hdl]
  have hf (q : κ) : f.workPos q = if q = i then e.workPos q + v.length else e.workPos q :=
    workPos_appended_of_home e i l (true :: u) v hil hel q
  have h₁ := spec_append_cfg d i j [true] [] u
    ((3 * v.length + 2) + (3 * v.length + 4) +
      (3 * (u.length + v.length + 1) + 4) + z)
    hij
    (by simp [d, putAction, hij.symm, hu])
    (by simpa using hdj)
    (by simpa [d, putAction, hw, hi] using tape_append [] true)
    (by simp [hd, hi])
  have h₂ := spec_append_cfg e i l (true :: u) [] v
    (3 * (u.length + v.length + 1) + 4 + z) hil
    (by simp [e, appended, d, putAction, hil.symm, hv])
    (by simpa using hel)
    (by simp [e, appended])
    (by simp [he, hd, hi]; omega)
  have h₃ := spec_rewind_cfg f i (true :: (u ++ v))
    (u.length + v.length + 1) z
    (by simp [f, appended])
    (by simp [hf, he, hd, hi]; omega)
    (by simp)
  have heq : { f with workPos := Function.update f.workPos i 0 } = paired c i u v := by
    apply TM.Cfg.ext
    · exact Subsingleton.elim _ _
    · rfl
    · funext q
      by_cases h : q = i <;>
        simp [f, e, d, appended, paired, putAction, h]
    · funext q
      by_cases h : q = i
      · subst q
        simpa [paired] using hi.symm
      · simp [paired, h, hf, he, hd]
    · rfl
  unfold pair put
  vcgen [h₁, h₂, h₃]
  all_goals simp_all [f, e, d] <;> omega

end Complexity.TreeMachine.Program
