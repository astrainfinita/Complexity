/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.StackMachine.Program.Word
public import Complexity.Control.Program.Traverse

/-! # Loading input and emitting stack words -/

@[expose] public section

set_option experimental.vcgen true

namespace Complexity.StackMachine.Program.IO

open Std.WP

variable {κ Γ : Type} [DecidableEq κ] [FinEnum Γ]

/-- Push the current input symbol and advance the read-only input head together. -/
def loadAction (i : κ) (a : Γ) : Action κ Γ :=
  { idle (κ := κ) with
    inputMove := 1
    work := fun j ↦ if j = i then .push a else .nop }

/-- Read and push one input symbol, or stop at the input boundary. -/
def loadBody (i : κ) : StackMachine.Program Id κ Γ Bool := do
  let a ← readInput
  if h : a.isSome then
    act (loadAction i (a.get h))
    pure false
  else pure true

/-- Read through the input once, accumulating its reverse on a stack. -/
def loadReverse (i : κ) : StackMachine.Program Id κ Γ Unit := repeatUntil (loadBody i)

/-- Read the input into scratch, then restore its order while transferring to the target. -/
def load (target temp : κ) : StackMachine.Program Id κ Γ Unit := do
  loadReverse temp
  Word.drain temp (fun i ↦ i == target)

/-- The configuration after reading a prefix of the input. -/
@[simps -fullyApplied]
def loaded {xs : List Γ} (c : Cfg κ Γ xs.toArray) (i : κ) (p : List Γ) :
    Cfg κ Γ xs.toArray :=
  { c.setStack i (p.reverse ++ c.stacks i) with
    inputPos := ⟨min (p.length + 1) (xs.length + 1), by simp only [List.size_toArray]; omega⟩ }

omit [FinEnum Γ] in
@[simp] theorem loaded_start {xs : List Γ} (c : Cfg κ Γ xs.toArray) (i : κ)
    (h : c.inputPos.val = 1) : loaded c i [] = c := by
  ext j <;> simp [h]

omit [FinEnum Γ] in
private theorem observe_loaded {xs : List Γ} (c : Cfg κ Γ xs.toArray) (i : κ)
    (p r : List Γ) (h : p ++ r = xs) :
    (observe (loaded c i p) : Option Γ × (κ → Option Γ)).1 = r.head? := by
  have hp : p.length ≤ xs.length := by rw [← h, List.length_append]; omega
  change (match min (p.length + 1) (xs.length + 1) with
    | 0 => none | n + 1 => xs.toArray[n]?) = r.head?
  rw [Nat.min_eq_left (by omega)]
  simp only [List.getElem?_toArray, ← h, List.getElem?_append_right le_rfl, Nat.sub_self]
  cases r <;> rfl

omit [FinEnum Γ] in
private theorem loadAction_loaded {xs : List Γ} (c : Cfg κ Γ xs.toArray) (i : κ)
    (p r : List Γ) (a : Γ) (h : p ++ a :: r = xs) :
    apply (loadAction i a) (loaded c i p) = loaded c i (p ++ [a]) := by
  have hp : p.length < xs.length := by rw [← h, List.length_append, List.length_cons]; omega
  ext j <;> simp [loadAction, Input.movePos, idle, Function.update_apply, List.reverse_append]
  · omega
  · split_ifs <;> simp_all [StackMachine.Op.apply]

@[spec] theorem spec_loadReverse {xs : List Γ} (c : Cfg κ Γ xs.toArray) (i : κ)
    (q : ℕ) (hi : c.inputPos.val = 1) :
    Triple ((loadReverse i).verify (semantics xs.toArray))
      (fun s b ↦ s = c ∧ b = 3 * xs.length + 2 + q)
      (fun _ s b ↦ s = loaded c i xs ∧ b = q) () := by
  have h := Program.spec_repeatUntilWith_count idle (loadBody i) (semantics xs.toArray)
    (fun j s ↦ s = loaded c i (xs.take j)) (fun s ↦ s = loaded c i xs)
    xs.length 2 1 q
    (by intro j hj s hs; simpa only [semantics_act, idle_apply] using hs)
    (by
      intro j hj q
      have hp : xs.take j ++ xs[j] :: xs.drop (j + 1) = xs := by
        rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
      have he := observe_loaded c i (xs.take j) (xs[j] :: xs.drop (j + 1)) hp
      have ha := loadAction_loaded c i (xs.take j) (xs.drop (j + 1)) xs[j] hp
      rw [← List.take_succ_eq_append_getElem hj] at ha
      unfold loadBody
      vcgen
      all_goals simp_all)
    (by
      intro q
      have he := observe_loaded c i xs [] (by simp)
      unfold loadBody
      vcgen
      all_goals simp_all <;> aesop)
  simpa only [loadReverse, repeatUntil, List.take_zero, loaded_start c i hi] using h

/-- Load input onto the target, empty scratch, and finish at the right boundary. -/
@[spec] theorem spec_load {xs : List Γ} (c : Cfg κ Γ xs.toArray) (target temp : κ)
    (q : ℕ) (hne : target ≠ temp) (ht : c.stacks temp = []) (hi : c.inputPos.val = 1) :
    Triple ((load target temp).verify (semantics xs.toArray))
      (fun s b ↦ s = c ∧ b = 6 * xs.length + 4 + q)
      (fun _ s b ↦ s = { c.setStack target (xs ++ c.stacks target) with
        inputPos := ⟨xs.length + 1, by simp only [List.size_toArray]; omega⟩ } ∧ b = q) () := by
  let d := loaded c temp xs
  have hd : d.stacks temp = xs.reverse := by simp [d, ht]
  have he : Word.drained d temp (fun i ↦ i == target) (d.stacks temp) [] =
      { c.setStack target (xs ++ c.stacks target) with
        inputPos := ⟨xs.length + 1, by simp only [List.size_toArray]; omega⟩ } := by
    ext j <;> simp [d, Function.update_apply]
    split_ifs <;> simp_all
  have h₁ := spec_loadReverse c temp (3 * xs.length + 2 + q) hi
  have h₂ := Word.spec_drain d temp (fun i ↦ i == target) q
  unfold load
  dsimp only at he ⊢
  vcgen [h₁, h₂]
  all_goals simp_all [d] <;> omega

/-- Pop the observed source symbol and append it to output in the same transition. -/
def emitAction (i : κ) (a : Γ) : Action κ Γ :=
  { idle (κ := κ) (Γ := Γ) with
    work := fun j ↦ if j = i then .pop else .nop
    output := some a }

/-- Emit one stack symbol, or stop when the stack is empty. -/
def emitBody (i : κ) : StackMachine.Program Id κ Γ Bool := do
  let a ← read i
  if h : a.isSome then
    act (emitAction i (a.get h))
    pure false
  else pure true

/-- Emit a stack from top to bottom, consuming it while preserving every other stack. -/
def emitStack (i : κ) : StackMachine.Program Id κ Γ Unit := repeatUntil (emitBody i)

/-- The configuration after emitting a prefix, with the remaining source word. -/
@[simps -fullyApplied]
def emitted {xs : Array Γ} (c : Cfg κ Γ xs) (i : κ) (p r : List Γ) :
    Cfg κ Γ xs :=
  { c.setStack i r with output := c.output ++ p.toArray }

omit [FinEnum Γ] in
@[simp] theorem emitted_start {xs : Array Γ} (c : Cfg κ Γ xs) (i : κ) :
    emitted c i [] (c.stacks i) = c := by simp [emitted]

omit [FinEnum Γ] in
/-- Pop the selected stack and append the supplied symbol to output. -/
@[simp] theorem emitAction_apply {xs : Array Γ} (c : Cfg κ Γ xs) (i : κ) (a : Γ) :
    apply (emitAction i a) c = emitted c i [a] (c.stacks i).tail := by
  ext j <;> simp [emitAction, Function.update_apply, idle]
  split_ifs <;> simp_all [StackMachine.Op.apply]

/-- Writing a word uses three transitions per symbol, plus two to stop. -/
@[spec] theorem spec_emitStack {xs : Array Γ} (c : Cfg κ Γ xs) (i : κ) (q : ℕ) :
    Triple ((emitStack i).verify (semantics xs))
      (fun s b ↦ s = c ∧ b = 3 * (c.stacks i).length + 2 + q)
      (fun _ s b ↦ s = { c.setStack i [] with output := c.output ++ (c.stacks i).toArray }
        ∧ b = q) () := by
  have h := Program.spec_repeatUntilWith_count idle (emitBody i) (semantics xs)
    (fun j s ↦ s = emitted c i ((c.stacks i).take j) ((c.stacks i).drop j))
    (fun s ↦ s = emitted c i (c.stacks i) []) (c.stacks i).length 2 1 q
    (by intro j hj s hs; simpa only [semantics_act, idle_apply] using hs)
    (by
      intro j hj q
      have hp := List.take_succ_eq_append_getElem hj
      have he : (emitted c i ((c.stacks i).take j) ((c.stacks i).drop j)).stacks i =
          (c.stacks i)[j] :: (c.stacks i).drop (j + 1) := by
        simpa only [emitted_stacks, Cfg.setStack_stacks, Function.update_self] using
          List.drop_eq_getElem_cons hj
      unfold emitBody
      vcgen
      all_goals simp_all [Cfg.ext_iff])
    (by
      intro q
      unfold emitBody
      vcgen
      all_goals simp_all <;> aesop)
  simp only [List.take_zero, List.drop_zero, emitted_start] at h
  exact h

end Complexity.StackMachine.Program.IO
