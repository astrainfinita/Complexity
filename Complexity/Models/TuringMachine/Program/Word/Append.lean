/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TuringMachine.Program.Word.Copy
public import Complexity.Models.TuringMachine.Program.Word.Rewind

/-!
# Composing suffix copying and source rewinding

The proof uses the two component specifications through verification-condition generation.
No additional transition-level proof is needed for their sequential composition.
-/

@[expose] public section

set_option experimental.vcgen true

namespace Complexity.TM.Program.Word

open Std.WP

variable {κ : Type} [DecidableEq κ] {xs : Array (Option Bool)}

/-- Copy a word and restore the source head, leaving the destination ready to append. -/
def append (i j : κ) : TM.Program κ (Option Bool) Unit := do
  copy i j
  rewind j

/-- Append the source suffix, then return only the source head to its first data cell. -/
def appended (c : TM.Cfg κ (Option Bool) Unit xs) (i j : κ) (w v : List Bool) :
    TM.Cfg κ (Option Bool) Unit xs :=
  { copied c i j w v with workPos := Function.update (copied c i j w v).workPos j 0 }

/-- When the source starts at home, appending changes only the destination head position. -/
theorem workPos_appended_of_home (c : Cfg κ (Option Bool) Unit xs) (i j : κ)
    (w v : List Bool) (hij : i ≠ j) (hj : c.workPos j = 0) (q : κ) :
    (appended c i j w v).workPos q =
      if q = i then c.workPos q + v.length else c.workPos q := by
  by_cases h : q = i
  · subst q
    simp [appended, hij]
  · by_cases h' : q = j
    · subst q
      simp [appended, h, hj]
    · simp [appended, h, h']

/-- Once both heads have been reset, appending changes only the destination word. -/
theorem setWorkPos_appended (c : TM.Cfg κ (Option Bool) Unit xs) (i j : κ)
    (w v : List Bool) (p : ℤ) :
    (appended c i j w v).setWorkPos i p =
      { (c.setWorkPos j 0).setWorkPos i p with
        workTapes := Function.update c.workTapes i (tape (w ++ v)) } := by
  apply TM.Cfg.ext <;> try rfl
  funext l
  by_cases hi : l = i
  · simp [appended, hi]
  · by_cases hj : l = j
    · subst l
      simp [appended, hi]
    · simp [appended, hi, hj]

/-- The complete output of appending, with history and unused credits retained. -/
def AppendPost (c : TM.Cfg κ (Option Bool) Unit xs) (i j : κ) (w v : List Bool)
    (V : κ → NonemptyInterval ℤ) (z : ℕ)
    (s : TM.TrackedCfg κ (Option Bool) Unit xs) (b : ℕ) : Prop :=
  s.cfg = appended c i j w v ∧ s.visited ≤ V ∧ b = z

/-- The copy and rewind bounds add exactly, retaining credits for later programs.

The common footprint includes both forward copying paths and the return past the left blank.
Destination contents, source restoration, and all unrelated fields are specified
by the complete final configuration. -/
@[spec]
theorem spec_append (c : TM.Cfg κ (Option Bool) Unit xs) (i j : κ)
    (w u v : List Bool) (V : κ → NonemptyInterval ℤ) (z : ℕ) (hij : i ≠ j)
    (ht : c.workTapes j = tape (u ++ v))
    (hp : c.workPos j = u.length) (hw : c.workTapes i = tape w)
    (hi : c.workPos i = w.length) (hF : CopyFootprint c i j v V)
    (hleft : (-1 : ℤ) ∈ V j) :
    Triple ((append i j).verify (TM.Program.semantics xs))
      (fun s b ↦ s.cfg = c ∧ s.visited ≤ V ∧
        b = (3 * v.length + 2) + (3 * (u.length + v.length) + 4) + z)
      (fun _ s b ↦ AppendPost c i j w v V z s b) () := by
  have hc := spec_copy c i j w u v V (3 * (u.length + v.length) + 4 + z)
    hij ht hp hw hi hF
  have hr := spec_rewind_credit (copied c i j w v) j (u ++ v)
    (u.length + v.length) z V
    (by simpa [hij.symm] using ht)
    (by simp [hp]) (by simp) hleft
  unfold append
  vcgen [hc, hr]
  case vc1 =>
    rename_i s b hs
    simpa only [Nat.add_assoc] using hs
  case vc2 =>
    rename_i s b hs a t d ht
    exact ht
  case vc3 =>
    rename_i s b hs a t d ht x y e hy
    exact hy

/-- Appending obeys the shared visited-cell bound, independently of execution time. -/
theorem AppendPost.space_le [Fintype κ] {c : TM.Cfg κ (Option Bool) Unit xs} {i j : κ}
    {w v : List Bool} {V : κ → NonemptyInterval ℤ} {z b : ℕ}
    {s : TM.TrackedCfg κ (Option Bool) Unit xs} (h : AppendPost c i j w v V z s b) :
    s.space ≤ ∑ l, ((V l).snd + 1 - (V l).fst).toNat :=
  s.space_le_of_visited_le V h.2.1

end Complexity.TM.Program.Word
