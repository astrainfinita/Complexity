/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Simulation.BitList.Encoding
public import Complexity.Models.StackMachine.Program.IO
public import Complexity.Control.Program.Bound

/-! # Preparing a tree-register input from an ordinary bit string -/

@[expose] public section

set_option experimental.vcgen true

namespace Complexity.TreeMachine.Simulation.BitList.Input

open StackMachine StackMachine.Program Std.WP

variable {κ : Type} [DecidableEq κ] {xs : List Bool}

/-- Begin a list-cell code while consuming its bit from the temporary stack. -/
def token (target temp : κ) : StackMachine.Action κ Bool Unit :=
  { idle (κ := κ) with work := fun i ↦
    if i = target then .push false else if i = temp then .pop else .nop }

/-- Prepend the next list-cell code, or finish when the temporary stack is empty. -/
def body (target temp : κ) : StackMachine.Program κ Bool Bool := do
  let b ← read temp
  if b = none then pure true
  else
    act (token target temp)
    if b.getD false then
      push target false
      push target true
      push target true
      pure false
    else
      push target true
      pure false

/-- Reverse the input, then prepend its cell codes and the terminal nil token. -/
def program (target temp : κ) : StackMachine.Program κ Bool Unit := do
  IO.loadReverse temp
  push target false
  repeatUntil (body target temp)

private theorem spec_body {zs : Array Bool} (c : StackMachine.Cfg κ Bool Unit zs)
    (target temp : κ) (b : Bool) (bs : List Bool) (q : ℕ)
    (_hne : target ≠ temp) (ht : c.stacks temp = b :: bs) :
    Triple ((body target temp).verify (semantics zs))
      (fun s n ↦ s = c ∧ 5 + q ≤ n)
      (fun r s n ↦ r = false ∧ s = (c.setStack temp bs).setStack target
        (chunk b ++ c.stacks target) ∧ q ≤ n) () := by
  have he : apply (token target temp) c =
      (c.setStack temp bs).setStack target (false :: c.stacks target) := by
    ext i <;> simp [token, idle, Function.update_apply]
    split_ifs <;> simp_all [StackMachine.Op.apply]
  cases b <;> unfold body <;> vcgen
  all_goals first | omega | (simp_all [chunk] <;> omega)

/-- The current code after consuming a reversed input prefix. -/
private def encoded {zs : Array Bool} (c : StackMachine.Cfg κ Bool Unit zs)
    (target temp : κ) (p r : List Bool) : StackMachine.Cfg κ Bool Unit zs :=
  (c.setStack target (p.reverse.flatMap chunk ++ c.stacks target)).setStack temp r

private theorem spec_loop {zs : Array Bool} (c : StackMachine.Cfg κ Bool Unit zs)
    (target temp : κ) (q : ℕ) (hne : target ≠ temp) :
    Triple ((repeatUntil (body target temp)).verify (semantics zs))
      (fun s n ↦ s = c ∧ 6 * (c.stacks temp).length + 2 + q ≤ n)
      (fun _ s n ↦ s = encoded c target temp (c.stacks temp) [] ∧ q ≤ n) () := by
  let w := c.stacks temp
  let cfgAt := fun j ↦ encoded c target temp (w.take j) (w.drop j)
  have h := Program.spec_repeatUntilWith_count_of_invariant idle (body target temp)
    (semantics zs) (fun j s n ↦ s = cfgAt j ∧ 6 * (w.length - j) + 2 + q ≤ n)
    (fun s n ↦ s = encoded c target temp w [] ∧ q ≤ n) w.length
    (by intro j hj s n hs; simpa only [semantics_act, idle_apply] using hs)
    (by rintro j hj s n ⟨hs, hn⟩; omega)
    (by
      intro j hj
      have ht : (cfgAt j).stacks temp = w[j] :: w.drop (j + 1) := by
        simp only [cfgAt, encoded, Cfg.setStack_stacks, Function.update_self]
        exact List.drop_eq_getElem_cons hj
      have he : ((cfgAt j).setStack temp (w.drop (j + 1))).setStack target
          (chunk w[j] ++ (cfgAt j).stacks target) = cfgAt (j + 1) := by
        dsimp only [cfgAt, encoded]
        rw [List.take_succ_eq_append_getElem hj]
        simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
          List.flatMap_cons, List.append_assoc, Cfg.setStack_stacks, Function.update_of_ne hne]
        simp only [Cfg.setStack_comm _ (Ne.symm hne), Cfg.setStack_setStack,
          Function.update_self]
      have hb := spec_body (cfgAt j) target temp w[j] (w.drop (j + 1))
        (6 * (w.length - (j + 1)) + 2 + q) hne ht
      rw [he] at hb
      constructor
      rintro s n ⟨hs, hn⟩
      exact hb.le_wp s n ⟨hs, by omega⟩)
    (by
      unfold body
      vcgen
      all_goals first | omega | (simp_all [cfgAt, encoded] <;> omega))
  simpa [repeatUntil, cfgAt, encoded, w] using h

/-- The encoded input is prepended to the target; scratch and external output are restored. -/
@[simps -fullyApplied]
def result (c : StackMachine.Cfg κ Bool Unit xs.toArray) (target : κ) :
    StackMachine.Cfg κ Bool Unit xs.toArray :=
  { c.setStack target (payload xs ++ c.stacks target) with
    inputPos := Fin.last (xs.toArray.size + 1) }

/-- Encode raw input in linear time, retaining the target suffix and all other storage. -/
@[spec] theorem spec_program (c : StackMachine.Cfg κ Bool Unit xs.toArray)
    (target temp : κ) (q : ℕ) (hne : target ≠ temp)
    (ht : c.stacks temp = []) (hi : c.inputPos.val = 1) :
    Triple ((program target temp).verify (semantics xs.toArray))
      (fun s n ↦ s = c ∧ 9 * xs.length + 5 + q ≤ n)
      (fun _ s n ↦ s = result c target ∧ q ≤ n) () := by
  let d := IO.loaded c temp xs
  let e := d.setStack target (false :: d.stacks target)
  have he : encoded e target temp (e.stacks temp) [] = result c target := by
    ext i <;> simp [encoded, e, d, payload, Function.update_apply]
    split_ifs <;> simp_all
  have h₁ := Program.spec_exact_budget_le
    (fun z ↦ IO.spec_loadReverse c temp z hi) le_rfl (6 * xs.length + 3 + q)
  have h₂ := spec_loop e target temp q hne
  rw [he] at h₂
  unfold program
  vcgen [h₁, h₂]
  all_goals simp_all [e, d, Ne.symm hne]
  all_goals omega

end Complexity.TreeMachine.Simulation.BitList.Input
