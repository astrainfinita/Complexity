/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TuringMachine.Program.Specification.Trace
public import Complexity.Models.TuringMachine.Program.Word.Append
public import Complexity.Control.Program.Bound

/-! # Word-program specifications without visitation assertions -/

@[expose] public section

set_option experimental.vcgen true

namespace Complexity.TM.Program.Word

open Std.WP

variable {κ : Type} [DecidableEq κ] {xs : Array (Option Bool)}

private def lower (c : Cfg κ (Option Bool) Unit xs) (i : κ) : ℤ := min (c.workPos i) (-1)

private def upper (c : Cfg κ (Option Bool) Unit xs) (h : ℕ) (i : κ) : ℤ :=
  max (c.workPos i) 0 + h

omit [DecidableEq κ] in
private theorem bounds_head (c : Cfg κ (Option Bool) Unit xs) (h : ℕ) (i : κ) :
    c.workPos i ∈ Set.Icc (lower c i) (upper c h i) := by
  simp only [lower, upper, Set.mem_Icc]
  omega

omit [DecidableEq κ] in
private theorem bounds_nat (c : Cfg κ (Option Bool) Unit xs) (h : ℕ) (i : κ)
    (m : ℕ) (hm : m ≤ h) : (m : ℤ) ∈ Set.Icc (lower c i) (upper c h i) := by
  simp only [lower, upper, Set.mem_Icc]
  omega

private theorem bounds_copy (c : Cfg κ (Option Bool) Unit xs) (i j : κ)
    (v : List Bool) (h : ℕ) (hv : v.length ≤ h) :
    CopyFootprint c i j v (lower c) (upper c h) := by
  intro l r hr
  simp only [lower, upper, Set.mem_Icc]
  split <;> constructor <;> omega

/-- Copy a suffix, keeping the complete configuration and remaining credits in the contract. -/
@[spec]
theorem spec_copy_cfg (c : Cfg κ (Option Bool) Unit xs) (i j : κ)
    (w u v : List Bool) (z : ℕ) (hij : i ≠ j)
    (ht : c.workTapes j = tape (u ++ v))
    (hp : c.workPos j = u.length) (hw : c.workTapes i = tape w)
    (hi : c.workPos i = w.length) :
    Triple ((copy i j).verify (cfgSemantics xs))
      (fun s b ↦ s = c ∧ b = 3 * v.length + 2 + z)
      (fun _ s b ↦ s = copied c i j w v ∧ b = z) () := by
  apply cfg_of_trace (spec_copy c i j w u v (lower c) (upper c v.length) z hij ht hp hw hi
    (bounds_copy c i j v v.length le_rfl))
  · rintro s b ⟨hs, hb⟩
    subst s
    exact ⟨rfl, bounds_head c v.length, hb⟩
  · intro a s b h
    exact ⟨h.1, h.2.2⟩

/-- Rewind to address zero while preserving every tape and input/output field. -/
@[spec]
theorem spec_rewind_cfg (c : Cfg κ (Option Bool) Unit xs) (j : κ) (bs : List Bool)
    (h z : ℕ) (hw : c.workTapes j = tape bs) (hp : c.workPos j = (h : ℤ))
    (hlen : h ≤ bs.length) :
    Triple ((rewind j).verify (cfgSemantics xs))
      (fun s b ↦ s = c ∧ b = 3 * h + 4 + z)
      (fun _ s b ↦ s = { c with workPos := Function.update c.workPos j 0 } ∧ b = z) () := by
  apply cfg_of_trace (spec_rewind_credit c j bs h z (lower c) (upper c h) hw hp hlen
    (bounds_nat c h j) (by simp [lower, upper, Set.mem_Icc]; omega))
  · rintro s b ⟨hs, hb⟩
    subst s
    exact ⟨rfl, bounds_head c h, hb⟩
  · intro a s b h
    exact ⟨h.1, h.2.2⟩

/-- Rewind with an upper-bound budget while preserving credits for the continuation. -/
@[spec]
theorem spec_rewind_cfg_le (c : Cfg κ (Option Bool) Unit xs) (j : κ) (bs : List Bool)
    (h z : ℕ) (hw : c.workTapes j = tape bs) (hp : c.workPos j = (h : ℤ))
    (hlen : h ≤ bs.length) :
    Triple ((rewind j).verify (cfgSemantics xs))
      (fun s b ↦ s = c ∧ 3 * h + 4 + z ≤ b)
      (fun _ s b ↦ s = c.setWorkPos j 0 ∧ z ≤ b) () :=
  Complexity.Program.spec_exact_budget_le
    (fun q ↦ spec_rewind_cfg c j bs h q hw hp hlen) le_rfl z

/-- Append a suffix and restore the source head, with no history obligations for the caller. -/
@[spec]
theorem spec_append_cfg (c : Cfg κ (Option Bool) Unit xs) (i j : κ)
    (w u v : List Bool) (z : ℕ) (hij : i ≠ j)
    (ht : c.workTapes j = tape (u ++ v))
    (hp : c.workPos j = u.length) (hw : c.workTapes i = tape w)
    (hi : c.workPos i = w.length) :
    Triple ((append i j).verify (cfgSemantics xs))
      (fun s b ↦ s = c ∧
        b = (3 * v.length + 2) + (3 * (u.length + v.length) + 4) + z)
      (fun _ s b ↦ s = appended c i j w v ∧ b = z) () := by
  apply cfg_of_trace (spec_append c i j w u v (lower c) (upper c (u.length + v.length)) z
    hij ht hp hw hi (bounds_copy c i j v _ (by omega))
    (bounds_nat c (u.length + v.length) j)
    (by simp [lower, upper, Set.mem_Icc]; omega))
  · rintro s b ⟨hs, hb⟩
    subst s
    exact ⟨rfl, bounds_head c (u.length + v.length), hb⟩
  · intro a s b h
    exact ⟨h.1, h.2.2⟩

/-- Append a source suffix and return both heads home, preserving every other field. -/
@[spec]
theorem spec_append_rewind_cfg (c : Cfg κ (Option Bool) Unit xs) (i j : κ)
    (w u v : List Bool) (z : ℕ) (hij : i ≠ j)
    (ht : c.workTapes j = tape (u ++ v))
    (hp : c.workPos j = u.length) (hw : c.workTapes i = tape w)
    (hi : c.workPos i = w.length) :
    Triple ((do append i j; rewind i).verify (cfgSemantics xs))
      (fun s b ↦ s = c ∧ b = 3 * w.length + 3 * u.length + 9 * v.length + 10 + z)
      (fun _ s b ↦ s =
        { c with workTapes := Function.update c.workTapes i (tape (w ++ v))
                 workPos := Function.update (Function.update c.workPos j 0) i 0 } ∧ b = z) () := by
  have ha := spec_append_cfg c i j w u v (3 * (w.length + v.length) + 4 + z)
    hij ht hp hw hi
  have hr := spec_rewind_cfg (appended c i j w v) i (w ++ v)
    (w.length + v.length) z
    (by simp [appended])
    (by simp [appended, hij, hi]) (by simp)
  have he := setWorkPos_appended c i j w v 0
  vcgen [ha, hr]
  case vc1 =>
    rename_i s b h
    exact ⟨h.1, by omega⟩
  case vc2 =>
    rename_i h
    exact ⟨h.1.trans he, h.2⟩

end Complexity.TM.Program.Word
