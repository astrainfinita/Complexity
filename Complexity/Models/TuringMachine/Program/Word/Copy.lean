/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.Program.Traverse
public import Complexity.Models.TuringMachine.Program.Specification.History
public import Complexity.Models.TuringMachine.Program.Word.Basic

/-! # A finite program for appending a binary suffix from another work tape -/

@[expose] public section

set_option experimental.vcgen true

namespace Complexity.TM.Program.Word

open Std.WP
open Controller (History)

variable {κ : Type} [DecidableEq κ] {xs : Array (Option Bool)}

/-- Copy one scanned symbol and advance both heads in one actual transition. -/
def copyToken (i j : κ) (a : (Option Bool)) : TM.Action κ (Option Bool) Unit :=
  { TM.Program.idle (κ := κ) with
    work := fun l ↦ (if l = i then some a else none, if l = i ∨ l = j then 1 else 0) }

/-- Copy one symbol or finish on the first non-bit. -/
def copyBody (i j : κ) : TM.Program κ (Option Bool) Bool := do
  let a ← TM.Program.read j
  if a.isSome then
    TM.Program.act (copyToken i j a)
    pure false
  else
    pure true

/-- Append a binary suffix while leaving the source tape intact. -/
def copy (i j : κ) : TM.Program κ (Option Bool) Unit := TM.Program.repeatUntil (copyBody i j)

/-- The complete tape configuration after appending `v` to target word `w`. -/
@[simps -fullyApplied]
def copied (c : TM.Cfg κ (Option Bool) Unit xs) (i j : κ) (w v : List Bool) :
    TM.Cfg κ (Option Bool) Unit xs :=
  { c with
    workTapes := Function.update c.workTapes i (tape (w ++ v))
    workPos := fun l ↦ if l = i ∨ l = j then c.workPos l + v.length else c.workPos l }

/-- The two final head positions lie in the chosen intervals; prior visits cover the starts. -/
def CopyFootprint (c : TM.Cfg κ (Option Bool) Unit xs) (i j : κ) (v : List Bool)
    (V : κ → NonemptyInterval ℤ) : Prop :=
  c.workPos i + (v.length : ℤ) ∈ V i ∧ c.workPos j + (v.length : ℤ) ∈ V j

private theorem copied_nil (c : TM.Cfg κ (Option Bool) Unit xs) (i j : κ) (w : List Bool)
    (h : c.workTapes i = tape w) : copied c i j w [] = c := by
  apply TM.Cfg.ext <;> try rfl
  · simp [← h, Function.update_eq_self]
  · funext l
    simp

private theorem copied_source (c : TM.Cfg κ (Option Bool) Unit xs) (i j : κ)
    (w v : List Bool) (h : i ≠ j) : (copied c i j w v).workTapes j = c.workTapes j := by
  simp [h.symm]

private theorem token_copied (c : TM.Cfg κ (Option Bool) Unit xs) (i j : κ)
    (w v : List Bool) (a : Bool) (hi : c.workPos i = w.length) :
    apply (copyToken i j (some a)) (copied c i j w v) =
      copied c i j w (v ++ [a]) := by
  apply TM.Cfg.ext
  · exact Subsingleton.elim _ _
  · exact TM.moveInputPos_zero _
  · funext l
    by_cases h : l = i
    · subst l
      simp only [apply_workTapes, copyToken, copied_workTapes, copied_workPos,
        Function.update_self, eq_self, true_or, ite_true, hi]
      have hp : (w.length : ℤ) + v.length = (w ++ v).length := by
        simp only [List.length_append]
        omega
      rw [hp, tape_append]
      simp only [List.append_assoc]
    · simp [copyToken, h]
  · funext l
    by_cases h : l = i ∨ l = j <;>
      simp [copyToken, h, List.length_append, add_assoc]
  · rfl

private theorem copied_read (c : TM.Cfg κ (Option Bool) Unit xs) (i j : κ)
    (w u v : List Bool) (hij : i ≠ j)
    (ht : c.workTapes j = tape (u ++ v))
    (hp : c.workPos j = u.length) (r : ℕ) (hr : r ≤ v.length) :
    (copied c i j w (v.take r)).workSymbols j =
      v[r]? := by
  unfold TM.Cfg.workSymbols
  rw [copied_source c i j w (v.take r) hij, ht]
  have he : (copied c i j w (v.take r)).workPos j =
      (((u.length + r : ℕ)) : ℤ) := by
    simp only [copied_workPos, or_true, ite_true, hp, List.length_take, Nat.min_eq_left hr]
    push_cast
    omega
  rw [he, tape_get]
  rw [List.getElem?_append_right (by omega : u.length ≤ u.length + r)]
  simp

private theorem copied_next (c : TM.Cfg κ (Option Bool) Unit xs) (i j : κ)
    (w v : List Bool) (hi : c.workPos i = w.length) (r : ℕ) (hr : r < v.length) :
    apply (copyToken i j (some v[r])) (copied c i j w
      (v.take r)) =
      copied c i j w (v.take (r + 1)) := by
  rw [token_copied c i j w (v.take r) v[r] hi, List.take_succ_eq_append_getElem hr]

/-- Complete configuration and footprint at the end of a copy. -/
def CopyPost (c : TM.Cfg κ (Option Bool) Unit xs) (i j : κ) (w v : List Bool)
    (V : κ → NonemptyInterval ℤ) (z : ℕ)
    (s : History (TM.Cfg κ (Option Bool) Unit xs) (TM.Action κ (Option Bool) Unit))
    (b : ℕ) : Prop :=
  s.last = copied c i j w v ∧ s.visited ≤ V ∧ b = z

/-- Copy an arbitrary suffix to a different tape's end, retaining all unused credits.

The full configuration equality preserves input, output, and every unrelated tape and head.
The footprint bound accounts for visited cells, including read and dispatch transitions. -/
@[spec]
theorem spec_copy (c : TM.Cfg κ (Option Bool) Unit xs) (i j : κ)
    (w u v : List Bool) (V : κ → NonemptyInterval ℤ) (z : ℕ) (hij : i ≠ j)
    (ht : c.workTapes j = tape (u ++ v))
    (hp : c.workPos j = u.length) (hw : c.workTapes i = tape w)
    (hi : c.workPos i = w.length) (hF : CopyFootprint c i j v V) :
    Triple ((copy i j).verify (TM.Program.semantics xs))
      (fun s b ↦ s.last = c ∧ s.visited ≤ V ∧ b = 3 * v.length + 2 + z)
      (fun _ s b ↦ CopyPost c i j w v V z s b) () := by
  let I := fun r (s : History (TM.Cfg κ (Option Bool) Unit xs) (TM.Action κ (Option Bool) Unit)) ↦
    s.last = copied c i j w (v.take r) ∧ s.visited ≤ V
  have hl : Triple ((copy i j).verify (TM.Program.semantics xs))
      (fun s b ↦ I 0 s ∧ b = 3 * v.length + 2 + z)
      (fun _ s b ↦ (s.last = copied c i j w v ∧ s.visited ≤ V) ∧ b = z) () := by
    apply Program.spec_repeatUntilWith_count TM.Program.idle (copyBody i j)
      (TM.Program.semantics xs) I _ v.length 2 1 z
    · intro r hr s hs
      simpa [I] using hs
    · intro r hr q
      have he : (copied c i j w (v.take r)).workSymbols j = some v[r] := by
        rw [copied_read c i j w u v hij ht hp r hr.le, List.getElem?_eq_getElem hr]
      have hn (s : History (TM.Cfg κ (Option Bool) Unit xs) (TM.Action κ (Option Bool) Unit))
      (hs : I r s) :
          I (r + 1) (apply (copyToken i j (some v[r])) s) := by
        have hc : (apply (copyToken i j (some v[r])) s).last =
            copied c i j w (v.take (r + 1)) := by
          rw [History.apply_last, hs.1, copied_next c i j w v hi r hr]
        refine ⟨hc, ?_⟩
        apply (s.apply_visited_le_iff _ V).mpr
        refine ⟨hs.2, ?_⟩
        intro l
        have hhead := s.head_mem_of_visited_le hs.2 l
        rw [← History.apply_last, hc]
        simp only [hs.1, copied_workPos, List.length_take, Nat.min_eq_left hr.le,
          Nat.min_eq_left hr, NonemptyInterval.mem_def] at hhead ⊢
        rcases hF with ⟨⟨_, hFi⟩, ⟨_, hFj⟩⟩
        split_ifs at hhead ⊢ with he
        · rcases he with rfl | rfl <;> omega
        · exact hhead
      unfold copyBody
      vcgen
      all_goals simp_all [I, copied_next]
      aesop
    · intro q
      have he : (copied c i j w (v.take v.length)).workSymbols j = none := by
        rw [copied_read c i j w u v hij ht hp v.length le_rfl]
        simp
      unfold copyBody
      vcgen
      all_goals simp_all [I]
  simpa only [I, CopyPost, List.take_zero, copied_nil c i j w hw, and_assoc] using hl

/-- The preserved footprint gives a space bound independently of the elapsed time. -/
theorem CopyPost.space_le [Fintype κ] {c : TM.Cfg κ (Option Bool) Unit xs} {i j : κ}
    {w v : List Bool} {V : κ → NonemptyInterval ℤ} {z b : ℕ}
    {s : History (TM.Cfg κ (Option Bool) Unit xs) (TM.Action κ (Option Bool) Unit)}
    (h : CopyPost c i j w v V z s b) :
    s.space ≤ ∑ l, ((V l).snd + 1 - (V l).fst).toNat :=
  s.space_le_of_visited_le V h.2.1

end Complexity.TM.Program.Word
