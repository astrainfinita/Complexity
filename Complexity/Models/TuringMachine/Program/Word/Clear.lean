/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TuringMachine.Program.Word.Configuration

/-! # Erasing an unmarked word and returning its head home

The forward scan locates the right end. Erasing from right to left preserves a contiguous
prefix, so the first blank encountered is the left boundary and no marker is needed.
-/

@[expose] public section

set_option experimental.vcgen true

namespace Complexity.TM.Program.Word

open Std.WP

variable {κ : Type} [DecidableEq κ] {xs : Array (Option Bool)}

/-- Erase one cell while moving left in the same transition. -/
def eraseAction (i : κ) : Action κ (Option Bool) Unit :=
  { idle (κ := κ) with
    work := fun j ↦ (if j = i then some none else none, if j = i then -1 else 0) }

/-- Erase the last remaining bit, or stop on the left blank. -/
def clearBody (i : κ) : Program κ (Option Bool) Bool := do
  let a ← read i
  if a.isSome then
    act (eraseAction i)
    pure false
  else pure true

/-- Scan to the end, erase the word backwards, and restore its head to address zero. -/
def clear (i : κ) : Program κ (Option Bool) Unit := do
  seek i .pos (· = none)
  move i .neg
  repeatUntil (clearBody i)
  move i .pos

/-- The selected tape is blank and at home; every other field stays unchanged. -/
def cleared (c : Cfg κ (Option Bool) Unit xs) (i : κ) : Cfg κ (Option Bool) Unit xs :=
  { c with workTapes := Function.update c.workTapes i ∅
           workPos := Function.update c.workPos i 0 }

private def clearAt (c : Cfg κ (Option Bool) Unit xs) (i : κ) (w : List Bool) (r : ℕ) :
    Cfg κ (Option Bool) Unit xs :=
  { c with workTapes := Function.update c.workTapes i (tape (w.take (w.length - r)))
           workPos := Function.update c.workPos i (((w.length - r : ℕ) : ℤ) - 1) }

private theorem clearAt_read (c : Cfg κ (Option Bool) Unit xs) (i : κ)
    (w : List Bool) (r : ℕ) (hr : r < w.length) :
    (clearAt c i w r).workSymbols i = some w[w.length - r - 1] := by
  have hm : ((w.length - r : ℕ) : ℤ) - 1 = (w.length - r - 1 : ℕ) := by omega
  simp only [Cfg.workSymbols, clearAt, Function.update_self, hm]
  rw [tape_get, List.getElem?_take, ite_eq_left (by omega), List.getElem?_eq_getElem (by omega)]

private theorem clearAt_next (c : Cfg κ (Option Bool) Unit xs) (i : κ)
    (w : List Bool) (r : ℕ) (hr : r < w.length) :
    apply (eraseAction i) (clearAt c i w r) = clearAt c i w
      (r + 1) := by
  have hm : w.length - r = (w.length - (r + 1)) + 1 := by omega
  have hp : ((w.length - r : ℕ) : ℤ) - 1 = (w.length - (r + 1) : ℕ) := by omega
  have ht : (tape (w.take (w.length - r))).set (((w.length - r : ℕ) : ℤ) - 1) none =
      tape (w.take (w.length - (r + 1))) := by
    rw [hp, hm, List.take_succ_eq_append_getElem (by omega)]
    have hlen : (w.take (w.length - (r + 1))).length = w.length - (r + 1) := by simp
    simpa only [hlen] using tape_erase_append (w.take (w.length - (r + 1)))
      w[w.length - (r + 1)]
  apply Cfg.ext
  · exact Subsingleton.elim _ _
  · exact moveInputPos_zero _
  · funext j
    by_cases h : j = i
    · subst j
      simpa only [apply_workTapes, eraseAction, clearAt, Function.update_self, ite_true] using ht
    · simp [eraseAction, clearAt, h]
  · funext j
    by_cases h : j = i
    · subst j
      simp only [apply_workPos, eraseAction, clearAt, Function.update_self, ite_true, SignType.cast]
      omega
    · simp [eraseAction, clearAt, h]
  · rfl

private theorem clear_loop_spec (c : Cfg κ (Option Bool) Unit xs) (i : κ)
    (w : List Bool) (z : ℕ) :
    Triple ((repeatUntil (clearBody i)).verify (cfgSemantics xs))
      (fun s b ↦ s = clearAt c i w 0 ∧ b = 3 * w.length + 2 + z)
      (fun _ s b ↦ s = clearAt c i w w.length ∧ b = z) () := by
  apply Complexity.Program.spec_repeatUntil_count idle (clearBody i)
    (cfgSemantics xs) (fun r s ↦ s = clearAt c i w r)
    (fun s ↦ s = clearAt c i w w.length) w.length 2 1 z
  · intro r hr s hs
    exact idle_apply s
  · intro r hr q
    have he := clearAt_read c i w r hr
    have hn := clearAt_next c i w r hr
    unfold clearBody
    vcgen
    all_goals simp_all
  · intro q
    have he : (clearAt c i w w.length).workSymbols i = none := by
      simp [Cfg.workSymbols, clearAt]
      rfl
    unfold clearBody
    vcgen
    all_goals simp_all

private theorem seek_end_spec (c : Cfg κ (Option Bool) Unit xs) (i : κ)
    (w : List Bool) (z : ℕ) (hw : c.workTapes i = tape w) (hp : c.workPos i = 0) :
    Triple ((seek i .pos (· = none)).verify (cfgSemantics xs))
      (fun s b ↦ s = c ∧ b = 3 * w.length + 2 + z)
      (fun _ s b ↦ s = c.setWorkPos i w.length ∧ b = z) () := by
  let I := fun (r : ℕ) (s : Cfg κ (Option Bool) Unit xs) ↦ s = c.setWorkPos i r
  have hl : Triple ((seek i .pos (· = none)).verify (cfgSemantics xs))
      (fun s b ↦ I 0 s ∧ b = 3 * w.length + 2 + z)
      (fun _ s b ↦ I w.length s ∧ b = z) () := by
    apply spec_seek (cfgSemantics xs) rfl i .pos (· = none) I w.length z
    · intro r hr s hs
      exact idle_apply s
    · intro r hr s hs
      subst s
      constructor
      · change (c.setWorkPos i (r : ℤ)).workSymbols i ≠ none
        rw [Cfg.workSymbols_setWorkPos_self, hw, tape_get, List.getElem?_eq_getElem hr]
        simp
      · simpa [I, cfgSemantics, eval, moveAction, SignType.cast] using
          moveAction_setWorkPos c i r .pos
    · intro s hs
      subst s
      change (c.setWorkPos i (w.length : ℤ)).workSymbols i = none
      rw [Cfg.workSymbols_setWorkPos_self, hw, tape_length]
  simpa only [I, Nat.cast_zero, ← hp, Cfg.setWorkPos_self] using hl

/-- Clearing restores the complete empty-tape configuration in `6 * length + 6` steps. -/
@[spec]
theorem spec_clear_cfg (c : Cfg κ (Option Bool) Unit xs) (i : κ) (w : List Bool) (z : ℕ)
    (hw : c.workTapes i = tape w) (hp : c.workPos i = 0) :
    Triple ((clear i).verify (cfgSemantics xs))
      (fun s b ↦ s = c ∧ b = 6 * w.length + 6 + z)
      (fun _ s b ↦ s = cleared c i ∧ b = z) () := by
  have hs := seek_end_spec c i w (3 * w.length + 4 + z) hw hp
  have hl := clear_loop_spec c i w (z + 1)
  have h₁ := (moveAction_setWorkPos c i w.length .neg).trans
    (show _ = clearAt c i w 0 by
      simp [clearAt, ← hw, Cfg.setWorkPos, SignType.cast, sub_eq_add_neg])
  have h₂ := (moveAction_apply i .pos (clearAt c i w w.length)).trans
    (show _ = cleared c i by simp [clearAt, cleared, Cfg.setWorkPos, SignType.cast])
  unfold clear
  vcgen [hs, hl]
  all_goals simp_all [moveAction] <;> omega

end Complexity.TM.Program.Word
