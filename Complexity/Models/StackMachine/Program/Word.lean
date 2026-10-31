/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.StackMachine.Program.Basic
public import Complexity.Control.Program.Traverse

/-! # Moving and copying stack words -/

@[expose] public section

set_option experimental.vcgen true

namespace Complexity.StackMachine.Program.Word

open Std.WP

variable {κ Γ : Type} [DecidableEq κ] [FinEnum Γ] {xs : Array Γ}

/-- Remove one source symbol and push it onto each selected destination. -/
def drainAction (i : κ) (targets : κ → Bool) (a : Γ) : Action κ Γ :=
  { idle (κ := κ) with work := fun j ↦ if j = i then .pop else if targets j then .push a else .nop }

/-- Transfer one symbol, or stop when the source is empty. -/
def drainBody (i : κ) (targets : κ → Bool) : StackMachine.Program κ Γ Bool := do
  let a ← read i
  if h : a.isSome then
    act (drainAction i targets (a.get h))
    pure false
  else pure true

/-- Empty a source stack, reversing its word onto each destination.
The source takes precedence if it also belongs to `targets`. -/
def drain (i : κ) (targets : κ → Bool) : StackMachine.Program κ Γ Unit :=
  repeatUntil (drainBody i targets)

/-- A complete configuration during a word transfer. -/
@[simps -fullyApplied]
def drained (c : Cfg κ Γ xs) (i : κ) (targets : κ → Bool)
    (p remaining : List Γ) : Cfg κ Γ xs :=
  { c with «stacks» := fun j ↦ if j = i then remaining
    else if targets j then p.reverse ++ c.stacks j else c.stacks j }

omit [FinEnum Γ] in
@[simp] theorem drained_start (c : Cfg κ Γ xs) (i : κ) (targets : κ → Bool) :
    drained c i targets [] (c.stacks i) = c := by
  apply Cfg.ext <;> simp [funext_iff]

omit [FinEnum Γ] in
private theorem drainAction_drained (c : Cfg κ Γ xs) (i : κ) (targets : κ → Bool)
    (p remaining : List Γ) (a : Γ) :
    apply (drainAction i targets a) (drained c i targets p (a :: remaining)) =
      drained c i targets (p ++ [a]) remaining := by
  ext j <;> simp [drainAction, idle, List.reverse_append, StackMachine.Op.apply]
  split_ifs <;> simp_all

/-- Moving a word takes exactly three transitions per symbol and two to stop. -/
@[spec] theorem spec_drain (c : Cfg κ Γ xs) (i : κ) (targets : κ → Bool) (q : ℕ) :
    Triple ((drain i targets).verify (semantics xs))
      (fun s b ↦ s = c ∧ b = 3 * (c.stacks i).length + 2 + q)
      (fun _ s b ↦ s = drained c i targets (c.stacks i) [] ∧ b = q) () := by
  have h := Program.spec_repeatUntilWith_count idle (drainBody i targets) (semantics xs)
    (fun j s ↦ s = drained c i targets ((c.stacks i).take j) ((c.stacks i).drop j))
    (fun s ↦ s = drained c i targets (c.stacks i) []) (c.stacks i).length 2 1 q
    (by intro j hj s hs; simpa only [semantics_act, idle_apply] using hs)
    (by
      intro j hj q
      have ha := drainAction_drained c i targets ((c.stacks i).take j)
        ((c.stacks i).drop (j + 1)) (c.stacks i)[j]
      rw [← List.drop_eq_getElem_cons hj, ← List.take_succ_eq_append_getElem hj] at ha
      have he : (drained c i targets ((c.stacks i).take j) ((c.stacks i).drop j)).stacks i =
          (c.stacks i)[j] :: (c.stacks i).drop (j + 1) := by
        simpa only [drained_stacks, ↓reduceIte] using List.drop_eq_getElem_cons hj
      unfold drainBody
      vcgen
      all_goals simp_all)
    (by
      intro q
      unfold drainBody
      vcgen
      all_goals simp_all <;> aesop)
  simpa only [drain, repeatUntil, List.take_zero, List.drop_zero, drained_start] using h

/-- Clearing is a transfer with no destinations. -/
def clear (i : κ) : StackMachine.Program κ Γ Unit := drain i (fun _ ↦ false)

/-- Copy a word while restoring the source. The temporary stack must start empty. -/
def copy (source target temp : κ) : StackMachine.Program κ Γ Unit := do
  drain source (fun i ↦ i == temp)
  drain temp (fun i ↦ i == source || i == target)

/-- Clearing preserves the external streams and every other stack. -/
@[spec] theorem spec_clear (c : Cfg κ Γ xs) (i : κ) (q : ℕ) :
    Triple ((clear i).verify (semantics xs))
      (fun s b ↦ s = c ∧ b = 3 * (c.stacks i).length + 2 + q)
      (fun _ s b ↦ s = c.setStack i [] ∧ b = q) () := by
  have he : drained c i (fun _ ↦ false) (c.stacks i) [] =
      c.setStack i [] := by
    ext j <;> simp [Function.update_apply]
  simpa only [clear, he] using spec_drain c i (fun _ ↦ false) q

/-- Copying prepends the source word to the target, restores the source, and empties scratch. -/
@[spec] theorem spec_copy (c : Cfg κ Γ xs) (source target temp : κ) (q : ℕ)
    (hst : source ≠ target) (hsp : source ≠ temp) (htp : target ≠ temp)
    (hp : c.stacks temp = []) :
    Triple ((copy source target temp).verify (semantics xs))
      (fun s b ↦ s = c ∧ b = 6 * (c.stacks source).length + 4 + q)
      (fun _ s b ↦ s = c.setStack target (c.stacks source ++ c.stacks target) ∧ b = q) () := by
  let d := drained c source (fun i ↦ i == temp) (c.stacks source) []
  have hd : d.stacks temp = (c.stacks source).reverse := by simp [d, Ne.symm hsp, hp]
  have he : drained d temp (fun i ↦ i == source || i == target) (d.stacks temp) [] =
      c.setStack target (c.stacks source ++ c.stacks target) := by
    ext i <;> simp [d, Function.update_apply, hp]
    split_ifs <;> simp_all
  have h₁ := spec_drain c source (fun i ↦ i == temp) (3 * (c.stacks source).length + 2 + q)
  have h₂ := spec_drain d temp (fun i ↦ i == source || i == target) q
  unfold copy
  vcgen [h₁, h₂]
  all_goals simp_all [d, Ne.symm hsp] <;> omega

/-- Move a word in its original order, emptying both the source and temporary stack. -/
def move (source target temp : κ) : StackMachine.Program κ Γ Unit := do
  drain source (fun i ↦ i == temp)
  drain temp (fun i ↦ i == target)

@[spec] theorem spec_move (c : Cfg κ Γ xs) (source target temp : κ) (q : ℕ)
    (hst : source ≠ target) (hsp : source ≠ temp) (htp : target ≠ temp)
    (hp : c.stacks temp = []) :
    Triple ((move source target temp).verify (semantics xs))
      (fun s b ↦ s = c ∧ b = 6 * (c.stacks source).length + 4 + q)
      (fun _ s b ↦ s = (c.setStack source []).setStack target
        (c.stacks source ++ c.stacks target) ∧ b = q) () := by
  let d := drained c source (fun i ↦ i == temp) (c.stacks source) []
  have he : drained d temp (fun i ↦ i == target) (d.stacks temp) [] =
      (c.setStack source []).setStack target (c.stacks source ++ c.stacks target) := by
    ext i <;> simp [d, Function.update_apply, hp]
    split_ifs <;> simp_all
  have h₁ := spec_drain c source (fun i ↦ i == temp) (3 * (c.stacks source).length + 2 + q)
  have h₂ := spec_drain d temp (fun i ↦ i == target) q
  unfold move
  vcgen [h₁, h₂]
  all_goals simp_all [d, Ne.symm hsp] <;> omega

end Complexity.StackMachine.Program.Word
