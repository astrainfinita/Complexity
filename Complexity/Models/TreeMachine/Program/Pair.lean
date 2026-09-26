/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TuringMachine.Program.Word.Append
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

/-- A common interval on the three participating tapes suffices, also when sources coincide. -/
def PairFootprint (i j l : κ) (u v : List Bool) (V : κ → NonemptyInterval ℤ) : Prop :=
  ∀ r : ℤ, -1 ≤ r → r ≤ u.length + v.length + 1 → r ∈ V i ∧ r ∈ V j ∧ r ∈ V l

/-- Full configuration and resource postcondition for pair construction. -/
def PairPost (c : TM.Cfg κ (Option Bool) Unit xs) (i : κ) (u v : List Bool)
    (V : κ → NonemptyInterval ℤ) (z : ℕ)
    (s : TM.TrackedCfg κ (Option Bool) Unit xs) (b : ℕ) : Prop :=
  s.cfg = paired c i u v ∧ s.visited ≤ V ∧ b = z

/-- Pair construction by composing the one-step writer, two append routines, and a rewind.
The two source indices may coincide; only the destination must be distinct from each. -/
@[spec]
theorem spec_pair (c : TM.Cfg κ (Option Bool) Unit xs) (i j l : κ)
    (u v : List Bool) (V : κ → NonemptyInterval ℤ) (z : ℕ) (hij : i ≠ j) (hil : i ≠ l)
    (hw : c.workTapes i = tape []) (hu : c.workTapes j = tape u)
    (hv : c.workTapes l = tape v) (hi : c.workPos i = 0)
    (hj : c.workPos j = 0) (hl : c.workPos l = 0) (hF : PairFootprint i j l u v V) :
    Triple ((pair i j l).verify (TM.Program.semantics xs))
      (fun s b ↦ s.cfg = c ∧ s.visited ≤ V ∧ b = 9 * (u.length + v.length) + 20 + z)
      (fun _ s b ↦ PairPost c i u v V z s b) () := by
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
  have hFu : CopyFootprint d i j u V := by
    constructor
    · simpa [hd, hi, add_comm] using (hF (u.length + 1) (by omega) (by omega)).1
    · simpa [hdj] using (hF u.length (by omega) (by omega)).2.1
  have hFv : CopyFootprint e i l v V := by
    constructor
    · simpa [he, hd, hi, add_comm, add_left_comm, add_assoc] using
        (hF (u.length + v.length + 1) (by omega) le_rfl).1
    · simpa [hel] using (hF v.length (by omega) (by omega)).2.2
  have h₁ := spec_append d i j [true] [] u V
    ((3 * v.length + 2) + (3 * v.length + 4) +
      (3 * (u.length + v.length + 1) + 4) + z)
    hij
    (by simp [d, putAction, hij.symm, hu])
    (by simpa using hdj)
    (by simpa [d, putAction, hw, hi] using tape_append [] true)
    (by simp [hd, hi]) hFu
    (hF (-1) (by omega) (by omega)).2.1
  have h₂ := spec_append e i l (true :: u) [] v V
    (3 * (u.length + v.length + 1) + 4 + z) hil
    (by simp [e, appended, d, putAction, hil.symm, hv])
    (by simpa using hel)
    (by simp [e, appended])
    (by simp [he, hd, hi]; omega) hFv
    (hF (-1) (by omega) (by omega)).2.2
  have h₃ := spec_rewind_credit f i (true :: (u ++ v))
    (u.length + v.length + 1) z V
    (by simp [f, appended])
    (by simp [hf, he, hd, hi]; omega)
    (by simp)
    (hF (-1) (by omega) (by omega)).1
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
  case vc1 =>
    rename_i s b hs a t q ht
    rcases ht with ⟨rfl, rfl, rfl⟩
    obtain ⟨hc, hseen, hb⟩ := hs
    refine ⟨?_, ?_, ?_⟩
    · change apply (putAction i (some true)) s.cfg = d
      rw [hc]
    · apply putAction_visited_le s i (some true) V hseen
      rw [hc, hi]
      exact (hF 1 (by omega) (by omega)).1
    · simp only [List.length_nil, Nat.zero_add]
      omega
  case vc2 =>
    rename_i h
    refine ⟨h.1, h.2.1, ?_⟩
    simpa only [List.length_nil, Nat.zero_add, Nat.add_assoc] using h.2.2
  case vc3 =>
    rename_i h
    exact h
  case vc4 =>
    rename_i h
    exact ⟨h.1.trans heq, h.2.1, h.2.2⟩
  case vc5 =>
    rename_i h
    obtain ⟨_, _, hb⟩ := h
    omega

/-- Pair construction stays within the finite common footprint. -/
theorem PairPost.space_le [Fintype κ] {c : TM.Cfg κ (Option Bool) Unit xs} {i : κ}
    {u v : List Bool} {V : κ → NonemptyInterval ℤ} {z b : ℕ}
    {s : TM.TrackedCfg κ (Option Bool) Unit xs} (h : PairPost c i u v V z s b) :
    s.space ≤ ∑ q, ((V q).snd + 1 - (V q).fst).toNat :=
  s.space_le_of_visited_le V h.2.1

end Complexity.TreeMachine.Program
