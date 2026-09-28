/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TuringMachine.Program.Seek
public import Complexity.Models.TuringMachine.Program.Word.Basic
public import Complexity.Models.TuringMachine.Program.Specification.History
public import Mathlib.Data.Int.Interval

/-! # Rewinding an unmarked binary word

A head within the word or at its right end can find the left blank by first moving left.
The final right move returns to address zero, also for the empty word.
-/

@[expose] public section

set_option experimental.vcgen true

namespace Complexity.TM.Program.Word

open Std.WP
open Controller (History)

variable {κ : Type} [DecidableEq κ] {xs : Array (Option Bool)}

/-- Return a word's head to address zero, preserving all stored cells. -/
def rewind (j : κ) : TM.Program κ (Option Bool) Unit := do
  move j .neg
  seek j .neg (· = none)
  move j .pos

private theorem read_atPos (c : Cfg κ (Option Bool) Unit xs) (j : κ)
    (bs : List Bool) (hw : c.workTapes j = tape bs) (m : ℕ) (hm : m < bs.length) :
    (c.setWorkPos j (m : ℤ)).workSymbols j = some bs[m] := by
  rw [Cfg.workSymbols_setWorkPos_self, hw, tape_get, List.getElem?_eq_getElem hm]

private theorem loop_spec (c : Cfg κ (Option Bool) Unit xs) (j : κ) (bs : List Bool)
    (h q : ℕ) (V : κ → NonemptyInterval ℤ) (hw : c.workTapes j = tape bs) (hlen : h ≤ bs.length)
    (hleft : (-1 : ℤ) ∈ V j) :
    Triple ((seek j .neg (· = none)).verify (semantics xs))
      (fun s b ↦ s.last = c.setWorkPos j ((h : ℤ) - 1) ∧ s.visited ≤ V ∧ b = 3 * h + 2 + q)
      (fun _ s b ↦ s.last = c.setWorkPos j (-1) ∧ s.visited ≤ V ∧ b = q) () := by
  let I := fun r (s : History (Cfg κ (Option Bool) Unit xs) (Action κ (Option Bool) Unit)) ↦
    s.last = c.setWorkPos j ((h - r : ℕ) - 1) ∧ s.visited ≤ V
  have hl : Triple ((seek j .neg (· = none)).verify (semantics xs))
      (fun s b ↦ I 0 s ∧ b = 3 * h + 2 + q)
      (fun _ s b ↦ I h s ∧ b = q) () := by
    apply spec_seek (semantics xs) rfl j .neg (· = none) I h q
    · intro r hr s hs
      simpa [I] using hs
    · intro r hr s hs
      have he : h - r = h - (r + 1) + 1 := by omega
      constructor
      · change s.last.workSymbols j ≠ none
        rw [hs.1, he]
        simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
        rw [read_atPos c j bs hw _ (by omega)]
        simp
      · have hc : apply (moveAction (Γ :=
        Option Bool) j .neg) s.last =
            c.setWorkPos j ((h - (r + 1) : ℕ) - 1) := by
          rw [hs.1, moveAction_setWorkPos]
          congr 1
          simp only [SignType.cast, he, Nat.cast_add, Nat.cast_one]
          omega
        refine ⟨by simpa only [semantics_act, History.apply_last] using hc, ?_⟩
        apply moveAction_visited_le j .neg s V hs.2
        rw [hc]
        simp only [Cfg.setWorkPos_workPos, Function.update_self]
        have hhead := (s.head_mem_of_visited_le hs.2 j).2
        simp only [hs.1, Cfg.setWorkPos_workPos, Function.update_self] at hhead
        exact ⟨hleft.1.trans (by omega), by omega⟩
    · intro s hs
      change s.last.workSymbols j = none
      rw [hs.1]
      simp [Cfg.workSymbols, hw]
  simpa only [I, Nat.sub_zero, Nat.sub_self, Nat.cast_zero, zero_sub, and_assoc] using hl

/-- Rewind within the word, retaining the continuation's credits and the complete footprint. -/
theorem spec_rewind_credit (c : Cfg κ (Option Bool) Unit xs) (j : κ) (bs : List Bool)
    (h z : ℕ) (V : κ → NonemptyInterval ℤ) (hw : c.workTapes j = tape bs)
    (hp : c.workPos j = (h : ℤ)) (hlen : h ≤ bs.length)
    (hleft : (-1 : ℤ) ∈ V j) :
    Triple ((rewind j).verify (semantics xs))
      (fun s b ↦ s.last = c ∧ s.visited ≤ V ∧ b = 3 * h + 4 + z)
      (fun _ s b ↦ s.last = c.setWorkPos j 0 ∧ s.visited ≤ V ∧ b = z) () := by
  have hl := loop_spec c j bs h (z + 1) V hw hlen hleft
  unfold rewind
  vcgen [hl]
  case vc1 =>
    rename_i s b hs a t d ht
    rcases ht with ⟨rfl, rfl, rfl⟩
    obtain ⟨hc, hF, hb⟩ := hs
    refine ⟨?_, ?_, by omega⟩
    · simpa only [History.apply_last, moveAction, hc, hp, SignType.cast, sub_eq_add_neg] using
        moveAction_apply j .neg s.last
    · apply moveAction_visited_le j .neg s V hF
      have hhead : (h : ℤ) ≤ (V j).snd := by
        simpa only [hc, hp] using (s.head_mem_of_visited_le hF j).2
      have hstart : (h : ℤ) - 1 ∈ V j := ⟨hleft.1.trans (by omega), by omega⟩
      simpa [hc, hp, SignType.cast, sub_eq_add_neg] using hstart
  case vc2 =>
    rename_i s b hs a t d ht u v f hv x y g hy
    rcases hy with ⟨rfl, rfl, rfl⟩
    obtain ⟨hc, hF, hb⟩ := hv
    refine ⟨?_, ?_, by omega⟩
    · simpa only [History.apply_last, moveAction, hc, Cfg.setWorkPos_workPos,
        Function.update_self, Cfg.setWorkPos_setWorkPos, SignType.cast, neg_add_cancel] using
        moveAction_apply j .pos v.last
    · apply moveAction_visited_le j .pos v V hF
      have hhead : (h : ℤ) ≤ (V j).snd := by
        simpa only [hs.1, hp] using (s.head_mem_of_visited_le hs.2.1 j).2
      have hzero : (0 : ℤ) ∈ V j := ⟨hleft.1.trans (by omega), by omega⟩
      simpa [hc, SignType.cast] using hzero
  all_goals
    simp_all only []
    omega

/-- Rewinding from position `h` takes `3 * h + 4` transitions, visiting the left blank. -/
theorem spec_rewind (c : Cfg κ (Option Bool) Unit xs) (j : κ) (bs : List Bool)
    (h : ℕ) (V : κ → NonemptyInterval ℤ) (hw : c.workTapes j = tape bs)
    (hp : c.workPos j = (h : ℤ)) (hlen : h ≤ bs.length)
    (hleft : (-1 : ℤ) ∈ V j) :
    Triple ((rewind j).verify (semantics xs))
      (fun s b ↦ s.last = c ∧ s.visited ≤ V ∧ b = 3 * h + 4)
      (fun _ s b ↦ s.last = c.setWorkPos j 0 ∧ s.visited ≤ V ∧ b = 0) () := by
  simpa using spec_rewind_credit c j bs h 0 V hw hp hlen hleft

/-- Rewinding extends the recorded interval only as far as the left blank. -/
theorem spec_rewind_range
    (s : History (Cfg κ (Option Bool) Unit xs) (Action κ (Option Bool) Unit)) (j : κ)
    (bs : List Bool) (h : ℕ) (hw : s.last.workTapes j = tape bs)
    (hp : s.last.workPos j = (h : ℤ)) (hlen : h ≤ bs.length) :
    Triple ((rewind j).verify (semantics xs))
      (fun t b ↦ t = s ∧ b = 3 * h + 4)
      (fun _ t b ↦ t.last = s.last.setWorkPos j 0 ∧
        t.visited ≤ Function.update s.visited j (s.visited j ⊔ NonemptyInterval.pure (-1)) ∧
        b = 0) () := by
  let V := Function.update s.visited j (s.visited j ⊔ NonemptyInterval.pure (-1))
  have hleft : (-1 : ℤ) ∈ V j := by
    simp only [V, Function.update_self]
    change NonemptyInterval.pure (-1) ≤ s.visited j ⊔ NonemptyInterval.pure (-1)
    exact le_sup_right
  have hr := spec_rewind s.last j bs h V hw hp hlen hleft
  constructor
  rintro t b ⟨ht, hb⟩
  subst t b
  apply hr.le_wp s (3 * h + 4)
  refine ⟨rfl, ?_, rfl⟩
  exact le_update_self_iff.mpr le_sup_left

end Complexity.TM.Program.Word
