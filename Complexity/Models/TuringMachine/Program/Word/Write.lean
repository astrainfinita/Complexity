/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TuringMachine.Program.Word.Basic
public import Complexity.Models.TuringMachine.Program.Specification.Tracked
public import Complexity.Control.Program.Bound

/-! # Writing symbols and fixed binary words -/

@[expose] public section

set_option experimental.vcgen true

namespace Complexity.TM.Program.Word

open Std.WP

variable {κ : Type} [DecidableEq κ]

/-- Write and advance one work head in a single real transition. -/
def putAction (i : κ) (a : Option Bool) : TM.Action κ (Option Bool) Unit :=
  { TM.Program.idle (κ := κ) with
    work := fun j ↦ (if j = i then some a else none, if j = i then 1 else 0) }

/-- Write one symbol, leaving the head ready for the next symbol. -/
def put (i : κ) (a : Option Bool) : TM.Program κ (Option Bool) Unit :=
  TM.Program.act (putAction i a)

/-- Writing advances the selected head by one and leaves every other head fixed. -/
theorem workPos_putAction {xs : Array (Option Bool)}
    (c : Cfg κ (Option Bool) Unit xs) (i : κ) (a : Option Bool) (q : κ) :
    (apply (putAction i a) c).workPos q =
      if q = i then c.workPos q + 1 else c.workPos q := by
  by_cases h : q = i <;> simp [putAction, h]

/-- A write stays within the caller's footprint when its advancing head remains inside it. -/
theorem putAction_visited_le {xs : Array (Option Bool)}
    (s : TrackedCfg κ (Option Bool) Unit xs) (i : κ) (a : Option Bool) (V : κ → NonemptyInterval ℤ)
    (hs : s.visited ≤ V) (hi : s.cfg.workPos i + 1 ∈ V i) :
    (apply (putAction i a) s).visited ≤ V := by
  apply (s.apply_visited_le_iff _ V).mpr
  refine ⟨hs, ?_⟩
  intro q
  rw [workPos_putAction]
  by_cases h : q = i
  · subst q; simpa using hi
  · simpa only [ite_eq_right h] using s.head_mem_of_visited_le hs q

/-- Write a statically known word, advancing after each bit. -/
def putWords (j : κ) : List Bool → TM.Program κ (Option Bool) Unit
  | [] => pure ()
  | b :: bs => do
    put j (some b)
    putWords j bs

/-- A work tape containing the given word, with its head immediately after that word. -/
@[simps -fullyApplied]
def written {xs : Array (Option Bool)} (c : TM.Cfg κ (Option Bool) Unit xs)
    (j : κ) (bs : List Bool) : TM.Cfg κ (Option Bool) Unit xs :=
  { c with workTapes := Function.update c.workTapes j (tape bs)
           workPos := Function.update c.workPos j bs.length }

theorem written_written {xs : Array (Option Bool)}
    (c : TM.Cfg κ (Option Bool) Unit xs) (j : κ) (as bs : List Bool) :
    written (written c j as) j bs = written c j bs := by simp [written]

theorem written_put {xs : Array (Option Bool)}
    (c : TM.Cfg κ (Option Bool) Unit xs) (j : κ) (bs : List Bool) (b : Bool) :
    apply (putAction j (some b)) (written c j bs) = written c j
      (bs ++ [b]) := by
  apply TM.Cfg.ext
  · exact Subsingleton.elim _ _
  · rfl
  · funext l
    by_cases h : l = j
    · subst l
      simp only [putAction, apply_workTapes, written_workTapes, written_workPos,
        Function.update_self, ite_true]
      exact tape_append bs b
    · simp [putAction, h]
  · funext l
    by_cases h : l = j <;> simp [putAction, h]
  · rfl

/-- Appending a fixed word takes exactly one transition per bit. -/
theorem spec_putWords {xs : Array (Option Bool)}
    (c : TM.Cfg κ (Option Bool) Unit xs) (j : κ) (as bs : List Bool) (q : ℕ) :
    Triple ((putWords j bs).verify (cfgSemantics xs))
      (fun s b ↦ s = written c j as ∧ b = bs.length + q)
      (fun _ s b ↦ s = written c j (as ++ bs) ∧ b = q) () := by
  induction bs generalizing as q with
  | nil => simp only [putWords, List.length_nil, Nat.zero_add, List.append_nil]; vcgen
  | cons b bs ih =>
    have h := ih (as ++ [b]) q
    unfold putWords put
    vcgen [h]
    all_goals simp_all [written_put, List.append_assoc]

/-- Appending a fixed word preserves any additional continuation budget. -/
theorem spec_putWords_le {xs : Array (Option Bool)}
    (c : TM.Cfg κ (Option Bool) Unit xs) (j : κ) (as bs : List Bool) (q : ℕ) :
    Triple ((putWords j bs).verify (cfgSemantics xs))
      (fun s b ↦ s = written c j as ∧ bs.length + q ≤ b)
      (fun _ s b ↦ s = written c j (as ++ bs) ∧ q ≤ b) () :=
  Program.spec_exact_budget_le (fun q ↦ spec_putWords c j as bs q) le_rfl q

end Complexity.TM.Program.Word
