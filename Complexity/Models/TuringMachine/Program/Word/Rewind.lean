/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TuringMachine.Program.Seek
public import Complexity.Models.TuringMachine.Program.Word.Basic
public import Complexity.Models.TuringMachine.Program.Specification.Trace
public import Mathlib.Data.Int.Interval

/-! # Rewinding an unmarked binary word

A head within the word or at its right end can find the left blank by first moving left.
The final right move returns to address zero, also for the empty word.
-/

@[expose] public section

set_option experimental.vcgen true

namespace Complexity.TM.Program.Word

open Std.WP

variable {κ : Type} [DecidableEq κ] {xs : Array (Option Bool)}

/-- Return a word's head to address zero, preserving all stored cells. -/
def rewind (j : κ) : Program κ (Option Bool) Unit := do
  move j .neg
  seek j .neg (· = none)
  move j .pos

private theorem read_atPos (c : Cfg κ (Option Bool) Unit xs) (j : κ)
    (bs : List Bool) (hw : c.workTapes j = tape bs) (m : ℕ) (hm : m < bs.length) :
    (c.setWorkPos j (m : ℤ)).workSymbols j = some bs[m] := by
  rw [Cfg.workSymbols_setWorkPos_self, hw, tape_get, List.getElem?_eq_getElem hm]

private theorem loop_spec (c : Cfg κ (Option Bool) Unit xs) (j : κ) (bs : List Bool)
    (h q : ℕ) (L R : κ → ℤ) (hw : c.workTapes j = tape bs) (hlen : h ≤ bs.length)
    (hf : ∀ m ≤ h, (m : ℤ) ∈ Set.Icc (L j) (R j))
    (hleft : (-1 : ℤ) ∈ Set.Icc (L j) (R j)) :
    Triple ((seek j .neg (· = none)).verify (semantics xs))
      (fun s b ↦ s.cfg = c.setWorkPos j ((h : ℤ) - 1) ∧ s.Within L R ∧ b = 3 * h + 2 + q)
      (fun _ s b ↦ s.cfg = c.setWorkPos j (-1) ∧ s.Within L R ∧ b = q) () := by
  let I := fun r (s : TrackedCfg κ (Option Bool) Unit xs) ↦
    s.cfg = c.setWorkPos j ((h - r : ℕ) - 1) ∧ s.Within L R
  have hl : Triple ((seek j .neg (· = none)).verify (semantics xs))
      (fun s b ↦ I 0 s ∧ b = 3 * h + 2 + q)
      (fun _ s b ↦ I h s ∧ b = q) () := by
    apply spec_seek (semantics xs) rfl j .neg (· = none) I h q
    · intro r hr s hs
      exact apply_idle s
    · intro r hr s hs
      have he : h - r = h - (r + 1) + 1 := by omega
      constructor
      · change s.cfg.workSymbols j ≠ none
        rw [hs.1, he]
        simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
        rw [read_atPos c j bs hw _ (by omega)]
        simp
      · have hc : apply (moveAction (Γ :=
        Option Bool) j .neg) s.cfg =
            c.setWorkPos j ((h - (r + 1) : ℕ) - 1) := by
          rw [hs.1, moveAction_setWorkPos]
          congr 1
          simp only [SignType.cast, he, Nat.cast_add, Nat.cast_one]
          omega
        refine ⟨hc, ?_⟩
        apply moveAction_within j .neg s L R hs.2
        rw [hc]
        simp only [Cfg.setWorkPos_workPos, Function.update_self]
        by_cases hz : h - (r + 1) = 0
        · simpa [hz] using hleft
        · have hm : ((h - (r + 1) : ℕ) : ℤ) - 1 = (h - (r + 1) - 1 : ℕ) := by omega
          rw [hm]
          exact hf _ (by omega)
    · intro s hs
      change s.cfg.workSymbols j = none
      rw [hs.1]
      simp [Cfg.workSymbols, hw]
  simpa only [I, Nat.sub_zero, Nat.sub_self, Nat.cast_zero, zero_sub, and_assoc] using hl

/-- Rewind within the word, retaining the continuation's credits and the complete footprint. -/
theorem spec_rewind_credit (c : Cfg κ (Option Bool) Unit xs) (j : κ) (bs : List Bool)
    (h z : ℕ) (L R : κ → ℤ) (hw : c.workTapes j = tape bs)
    (hp : c.workPos j = (h : ℤ)) (hlen : h ≤ bs.length)
    (hf : ∀ m ≤ h, (m : ℤ) ∈ Set.Icc (L j) (R j))
    (hleft : (-1 : ℤ) ∈ Set.Icc (L j) (R j)) :
    Triple ((rewind j).verify (semantics xs))
      (fun s b ↦ s.cfg = c ∧ s.Within L R ∧ b = 3 * h + 4 + z)
      (fun _ s b ↦ s.cfg = c.setWorkPos j 0 ∧ s.Within L R ∧ b = z) () := by
  have hl := loop_spec c j bs h (z + 1) L R hw hlen hf hleft
  have hstart : (h : ℤ) - 1 ∈ Set.Icc (L j) (R j) := by
    by_cases hz : h = 0
    · simpa [hz] using hleft
    · have hm : (h : ℤ) - 1 = (h - 1 : ℕ) := by omega
      rw [hm]
      exact hf _ (by omega)
  unfold rewind
  vcgen [hl]
  case vc1 =>
    rename_i s b hs a t d ht
    rcases ht with ⟨rfl, rfl, rfl⟩
    obtain ⟨hc, hF, hb⟩ := hs
    refine ⟨?_, ?_, by omega⟩
    · simpa only [apply_cfg, moveAction, hc, hp, SignType.cast, sub_eq_add_neg] using
        moveAction_apply j .neg s.cfg
    · apply moveAction_within j .neg s L R hF
      simpa [hc, hp, SignType.cast, sub_eq_add_neg] using hstart
  case vc2 =>
    rename_i s b hs a t d ht u v f hv x y g hy
    rcases hy with ⟨rfl, rfl, rfl⟩
    obtain ⟨hc, hF, hb⟩ := hv
    refine ⟨?_, ?_, by omega⟩
    · simpa only [apply_cfg, moveAction, hc, Cfg.setWorkPos_workPos,
        Function.update_self, Cfg.setWorkPos_setWorkPos, SignType.cast, neg_add_cancel] using
        moveAction_apply j .pos v.cfg
    · apply moveAction_within j .pos v L R hF
      simpa [hc, SignType.cast] using hf 0 (Nat.zero_le h)
  all_goals
    simp_all only []
    omega

/-- Rewinding from position `h` takes `3 * h + 4` transitions, visiting the left blank. -/
theorem spec_rewind (c : Cfg κ (Option Bool) Unit xs) (j : κ) (bs : List Bool)
    (h : ℕ) (L R : κ → ℤ) (hw : c.workTapes j = tape bs)
    (hp : c.workPos j = (h : ℤ)) (hlen : h ≤ bs.length)
    (hf : ∀ m ≤ h, (m : ℤ) ∈ Set.Icc (L j) (R j))
    (hleft : (-1 : ℤ) ∈ Set.Icc (L j) (R j)) :
    Triple ((rewind j).verify (semantics xs))
      (fun s b ↦ s.cfg = c ∧ s.Within L R ∧ b = 3 * h + 4)
      (fun _ s b ↦ s.cfg = c.setWorkPos j 0 ∧ s.Within L R ∧ b = 0) () := by
  simpa using spec_rewind_credit c j bs h 0 L R hw hp hlen hf hleft

/-- Rewinding extends the recorded interval only as far as the left blank. -/
theorem spec_rewind_range (s : TrackedCfg κ (Option Bool) Unit xs) (j : κ)
    (bs : List Bool) (h : ℕ) (hw : s.cfg.workTapes j = tape bs)
    (hp : s.cfg.workPos j = (h : ℤ)) (hlen : h ≤ bs.length) :
    Triple ((rewind j).verify (semantics xs))
      (fun t b ↦ t = s ∧ b = 3 * h + 4)
      (fun _ t b ↦ t.cfg = s.cfg.setWorkPos j 0 ∧
        t.Within (fun i ↦ if i = j then min (s.visited i).fst (-1) else (s.visited i).fst)
          (fun i ↦ (s.visited i).snd) ∧ b = 0) () := by
  let L := fun i ↦ if i = j then min (s.visited i).fst (-1) else (s.visited i).fst
  have hf : ∀ m ≤ h, (m : ℤ) ∈ Set.Icc (L j) (s.visited j).snd := by
    intro m hm
    have hh := s.head_mem j
    simp only [L, ite_true, Set.mem_Icc]
    omega
  have hleft : (-1 : ℤ) ∈ Set.Icc (L j) (s.visited j).snd := by
    have hh := s.head_mem j
    simp only [L, ite_true, Set.mem_Icc]
    omega
  have hr := spec_rewind s.cfg j bs h L (fun i ↦ (s.visited i).snd) hw hp hlen hf hleft
  constructor
  rintro t b ⟨ht, hb⟩
  subst t b
  apply hr.le_wp s (3 * h + 4)
  refine ⟨rfl, ?_, rfl⟩
  intro i
  dsimp [L]
  split_ifs <;> simp

end Complexity.TM.Program.Word
