/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Simulation.Basic
public import Complexity.Models.TreeMachine.StackProgram
public import Complexity.Control.Program.Bound

/-! # Updating one tree register through an empty result stack -/

@[expose] public section

set_option experimental.vcgen true

namespace Complexity.TreeMachine.Simulation.Program

open StackMachine.Program Work Std.WP
open StackMachine.Program.Tree (project spec_project spec_pair projectTime_le)

variable {k : ℕ} {xs : Array Bool}

/-- Compute before overwriting the destination, including when it aliases a source. -/
def make : Op k → StackMachine.Program (Work k) Bool Unit
  | .nop => pure ()
  | .left _ j =>
      project (data j) (.scratch .result) (.scratch .saved) (.scratch .temp)
        (.scratch .counter) false
  | .right _ j =>
      project (data j) (.scratch .result) (.scratch .saved) (.scratch .temp)
        (.scratch .counter) true
  | .pair _ j l =>
      StackMachine.Program.Tree.pair (data j) (data l) (.scratch .result) (.scratch .temp)

/-- Replace only the selected register and restore the temporary stacks. -/
def build (o : Op k) : StackMachine.Program (Work k) Bool Unit := do
  match o.dst with
  | none => pure ()
  | some i =>
      make o
      Word.clear (data i)
      Word.move (.scratch .result) (data i) (.scratch .temp)

@[spec] theorem spec_make (c : StackMachine.Cfg (Work k) Bool Unit xs)
    (o : Op k) (i : Fin k) (ρ : Fin k → Complexity.Tree) (q : ℕ)
    (hw : c.stacks = contents ρ) (hd : o.dst = some i) :
    Triple ((make o).verify (semantics xs))
      (fun s t ↦ s = c ∧ 16 * o.sizeCost ρ + q ≤ t)
      (fun _ s t ↦ s = c.setStack (.scratch .result) (BitList.encodeTree (o.eval ρ i)) ∧
        q ≤ t) () := by
  have hproject (j : Fin k) (right : Bool) := Program.spec_exact_budget_le
    (fun z ↦ spec_project c (data j) (.scratch .result)
      (.scratch .saved) (.scratch .temp) (.scratch .counter) (ρ j) [] right z
      (by simp) (by simp [hw]) (by simp [hw]) (by simp [hw]) (by simp [hw]))
    (m := 16 * (ρ j).size)
    (by have := projectTime_le (ρ j) right; have := (ρ j).size_pos; omega) q
  cases o with
  | nop => simp at hd
  | left l j =>
    cases Option.some.inj hd
    simpa [make, hw, Op.sizeCost] using hproject j false
  | right l j =>
    cases Option.some.inj hd
    simpa [make, hw, Op.sizeCost] using hproject j true
  | pair l j m =>
    cases Option.some.inj hd
    have h := Program.spec_exact_budget_le (fun z ↦ spec_pair c (data j) (data m)
      (.scratch .result) (.scratch .temp) (BitList.encodeTree (ρ j)) (BitList.encodeTree (ρ m)) z
      (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp [hw]) (by simp [hw]) (by simp [hw]))
      (m := 16 * (Complexity.Tree.pair (ρ j) (ρ m)).size)
      (by simp only [BitList.length_encodeTree, Complexity.Tree.size_pair]; omega) q
    simpa [make, hw, Op.sizeCost, BitList.encodeTree] using h

/-- The three credits per live node pay for clearing it at its next overwrite. -/
@[spec] theorem spec_build (c : StackMachine.Cfg (Work k) Bool Unit xs)
    (o : Op k) (ρ : Fin k → Complexity.Tree) (q : ℕ) (hw : c.stacks = contents ρ) :
    Triple ((build o).verify (semantics xs))
      (fun s t ↦ s = c ∧ 38 * o.sizeCost ρ + 3 * (∑ i, (ρ i).size) + q ≤ t)
      (fun _ s t ↦ s = bank c (o.eval ρ) ∧ 3 * (∑ i, (o.eval ρ i).size) + q ≤ t) () := by
  cases hd : o.dst with
  | none =>
    have ho : o = .nop := by cases o <;> simp_all
    subst o
    simp only [build, Op.dst_nop, Op.eval_nop, bank_self c ρ hw]
    vcgen
    all_goals simp_all [Op.sizeCost]; omega
  | some i =>
    let w := BitList.encodeTree (o.eval ρ i)
    let d := c.setStack (.scratch .result) w
    let e := d.setStack (data i) []
    let z := 3 * (∑ j, (o.eval ρ j).size) + q
    have he : (e.setStack (.scratch .result) []).setStack (data i)
        (e.stacks (.scratch .result) ++ e.stacks (data i)) = bank c (o.eval ρ) := by
      ext j <;> try rfl
      rcases j with j | j
      · by_cases hji : j = i
        · simp [hji, e, d, w, hw, bank, contents]
        · have hn : o.dst ≠ some j := by simp [hd, Ne.symm hji]
          simp [e, d, w, hw, bank, contents, hji, o.eval_of_dst_ne ρ j hn]
      · cases j <;> simp [e, d, hw, bank, contents]
    have hmove := Program.spec_exact_budget_le
      (fun q ↦ Word.spec_move e (.scratch .result) (data i) (.scratch .temp) q
        (by simp) (by simp) (by simp) (by simp [e, d, hw])) le_rfl z
    rw [he] at hmove
    have hclear := Program.spec_exact_budget_le (fun q ↦ Word.spec_clear d (data i) q)
      le_rfl (6 * w.length + 4 + z)
    have hmake := spec_make c o i ρ
      (3 * (ρ i).size + 2 + (6 * w.length + 4 + z)) hw hd
    have hm := o.sum_size_eval_add ρ hd
    have hn := o.written_size_le (ρ := ρ) hd
    have hp := o.sizeCost_pos ρ
    simp only [build, hd]
    vcgen [hmake, hclear, hmove]
    all_goals simp_all [d, e, w, z] <;> omega

end Complexity.TreeMachine.Simulation.Program
