/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.Program.Traverse
public import Complexity.Models.TuringMachine.Program.Word.Copy
public import Complexity.Models.TuringMachine.Program.Word.Rewind
public import Complexity.Models.TuringMachine.Program.Word.Configuration

/-! # Loading and emitting binary words -/

@[expose] public section

set_option experimental.vcgen true

namespace Complexity.TM.Program.Word

open Std.WP

variable {κ : Type} [DecidableEq κ] {xs : Array (Option Bool)}

/-- Emit the scanned symbol and advance its head in one transition. -/
def emitToken (i : κ) (a : (Option Bool)) : Action κ (Option Bool) Unit :=
  { Program.idle (κ := κ) (Γ := (Option Bool)) with
    work := fun j ↦ (none, if j = i then 1 else 0)
    output := some a }

/-- Emit one data symbol, or finish at the end of the word. -/
def emitBody (i : κ) : TM.Program κ (Option Bool) Bool := do
  let a ← Program.read i
  if a.isSome then
    Program.act (emitToken i a)
    pure false
  else pure true

/-- Append a work tape's binary word to the output. -/
def emit (i : κ) : TM.Program κ (Option Bool) Unit := Program.repeatUntil (emitBody i)

/-- Complete configuration after emitting a word. -/
@[simps -fullyApplied]
def emitted (c : Cfg κ (Option Bool) Unit xs) (i : κ) (w : List Bool) :
    Cfg κ (Option Bool) Unit xs :=
  { c with workPos := Function.update c.workPos i (c.workPos i + w.length)
           output := c.output ++ (w.map some).toArray }

private theorem emitted_nil (c : Cfg κ (Option Bool) Unit xs) (i : κ) : emitted c i [] = c := by
  simp [emitted]

private theorem emitted_read (c : Cfg κ (Option Bool) Unit xs) (i : κ) (w : List Bool)
    (hw : c.workTapes i = tape w) (hp : c.workPos i = 0) (r : ℕ) (hr : r ≤ w.length) :
    (emitted c i (w.take r)).workSymbols i = w[r]? := by
  unfold Cfg.workSymbols
  rw [emitted_workTapes, emitted_workPos, Function.update_self, hw]
  have he : c.workPos i + (w.take r).length = (r : ℤ) := by
    simp only [hp, List.length_take, Nat.min_eq_left hr]
    omega
  rw [he, tape_get]

private theorem emitted_next (c : Cfg κ (Option Bool) Unit xs) (i : κ) (w : List Bool)
    (r : ℕ) (hr : r < w.length) :
    apply (emitToken i (some w[r])) (emitted c i (w.take r)) =
      emitted c i (w.take (r + 1)) := by
  apply Cfg.ext
  · exact Subsingleton.elim _ _
  · rfl
  · rfl
  · funext j
    by_cases h : j = i
    · subst j
      simp only [apply_workPos, emitToken, emitted_workPos, Function.update_self, eq_self,
        ite_true, List.length_take, Nat.min_eq_left hr.le, Nat.min_eq_left hr]
      simp
      omega
    · simp [emitToken, h]
  · apply Array.toList_inj.mp
    change ((c.output ++ ((w.take r).map some).toArray).push (some w[r])).toList = _
    simp only [emitted_output, Array.toList_push, Array.toList_append,
      List.take_succ_eq_append_getElem hr, List.map_append, List.map_cons, List.map_nil,
      List.append_assoc]

/-- Emitting preserves all tapes, advances the selected head, and appends exactly the bits. -/
@[spec]
theorem spec_emit_cfg (c : Cfg κ (Option Bool) Unit xs) (i : κ)
    (w : List Bool) (z : ℕ) (hw : c.workTapes i = tape w) (hp : c.workPos i = 0) :
    Triple ((emit i).verify (Program.cfgSemantics xs))
      (fun s b ↦ s = c ∧ b = 3 * w.length + 2 + z)
      (fun _ s b ↦ s = emitted c i w ∧ b = z) () := by
  have h : Triple ((emit i).verify (Program.cfgSemantics xs))
      (fun s b ↦ s = emitted c i (w.take 0) ∧ b = 3 * w.length + 2 + z)
      (fun _ s b ↦ s = emitted c i w ∧ b = z) () := by
    apply Program.spec_repeatUntilWith_count Program.idle (emitBody i)
      (Program.cfgSemantics xs) (fun r s ↦ s = emitted c i (w.take r))
      (fun s ↦ s = emitted c i w) w.length 2 1 z
    · intro r hr s hs
      exact Program.idle_apply s
    · intro r hr q
      have he : (emitted c i (w.take r)).workSymbols i = some w[r] := by
        rw [emitted_read c i w hw hp r hr.le, List.getElem?_eq_getElem hr]
      unfold emitBody
      vcgen
      all_goals simp_all [emitted_next]
    · intro q
      have he : (emitted c i (w.take w.length)).workSymbols i = none := by
        rw [emitted_read c i w hw hp _ le_rfl]
        simp
      unfold emitBody
      vcgen
      all_goals simp_all
  simpa only [List.take_zero, emitted_nil] using h

/-- Copy one input symbol, advancing both the input and destination heads. -/
def loadToken (i : κ) (a : Option Bool) : Action κ (Option Bool) Unit :=
  { Program.idle (κ := κ) with
    inputMove := 1
    work := fun j ↦ (if j = i then some a else none, if j = i then 1 else 0) }

/-- Copy a bit or finish at the right input boundary. -/
def loadBody (i : κ) : TM.Program κ (Option Bool) Bool := do
  let a ← Program.readInput
  if a.isSome then
    Program.act (loadToken i a)
    pure false
  else pure true

/-- Copy the input word and return its work head to zero. -/
def load (i : κ) : TM.Program κ (Option Bool) Unit := do
  Program.repeatUntil (loadBody i)
  rewind i

/-- Loading changes only the input position and the destination tape. -/
@[simps -fullyApplied]
def loaded (c : Cfg κ (Option Bool) Unit xs) (i : κ) (w : List Bool)
    (p : Fin (xs.size + 2)) : Cfg κ (Option Bool) Unit xs :=
  { c with inputPos := p, workTapes := Function.update c.workTapes i (tape w) }

@[simps -fullyApplied state inputPos workTapes workPos output]
private def loadAt (c : Cfg κ (Option Bool) Unit xs) (i : κ) (w : List Bool)
    (r : ℕ) : Cfg κ (Option Bool) Unit xs :=
  { c with inputPos := ⟨min r xs.size + 1, by omega⟩
           workTapes := Function.update c.workTapes i (tape (w.take r))
           workPos := Function.update c.workPos i (r : ℤ) }

private theorem loadAt_zero (c : Cfg κ (Option Bool) Unit xs) (i : κ) (w : List Bool)
    (hi : c.inputPos.val = 1) (hw : c.workTapes i = tape []) (hp : c.workPos i = 0) :
    loadAt c i w 0 = c := by
  apply Cfg.ext
  · rfl
  · apply Fin.ext
    simpa using hi.symm
  · simp [← hw]
  · simp [← hp]
  · rfl

private theorem loadAt_next (c : Cfg κ (Option Bool) Unit xs) (i : κ) (w : List Bool)
    (hx : xs = w.toArray.map some) (r : ℕ) (hr : r < w.length) :
    apply (loadToken i (some w[r])) (loadAt c i w r) =
      loadAt c i w (r + 1) := by
  apply Cfg.ext
  · exact Subsingleton.elim _ _
  · apply Fin.ext
    simp only [apply_inputPos, loadToken, loadAt_inputPos, moveInputPos, hx, Array.size_map,
      List.size_toArray]
    omega
  · funext j
    by_cases h : j = i
    · subst j
      simp only [apply_workTapes, loadToken, loadAt_workTapes, loadAt_workPos,
        Function.update_self, eq_self, ite_true]
      rw [List.take_succ_eq_append_getElem hr, ← tape_append]
      congr 1
      simp [List.length_take, Nat.min_eq_left hr.le]
    · simp [loadToken, h]
  · funext j
    by_cases h : j = i <;> simp [loadToken, h]
  · rfl

private theorem loadAt_input (c : Cfg κ (Option Bool) Unit xs) (i : κ) (w : List Bool)
    (hx : xs = w.toArray.map some) (r : ℕ) (hr : r ≤ w.length) :
    (loadAt c i w r).inputSymbol = w[r]? := by
  have hlen : xs.size = w.length := by simp [hx]
  simp only [Cfg.inputSymbol, loadAt_inputPos, hlen, Nat.min_eq_left hr]
  change xs[r]?.getD default = w[r]?
  rw [hx]
  simp only [Array.getElem?_map, List.getElem?_toArray]
  cases w[r]? <;> rfl

private theorem load_loop_spec (c : Cfg κ (Option Bool) Unit xs) (i : κ)
    (w : List Bool) (z : ℕ) (hx : xs = w.toArray.map some) (hi : c.inputPos.val = 1)
    (hw : c.workTapes i = tape []) (hp : c.workPos i = 0) :
    Triple ((Program.repeatUntil (loadBody i)).verify (Program.cfgSemantics xs))
      (fun s b ↦ s = c ∧ b = 3 * w.length + 2 + z)
      (fun _ s b ↦ s = loadAt c i w w.length ∧ b = z) () := by
  have h : Triple ((Program.repeatUntil (loadBody i)).verify (Program.cfgSemantics xs))
      (fun s b ↦ s = loadAt c i w 0 ∧ b = 3 * w.length + 2 + z)
      (fun _ s b ↦ s = loadAt c i w w.length ∧ b = z) () := by
    apply Program.spec_repeatUntilWith_count Program.idle (loadBody i)
      (Program.cfgSemantics xs) (fun r s ↦ s = loadAt c i w r)
      (fun s ↦ s = loadAt c i w w.length) w.length 2 1 z
    · intro r hr s hs
      exact Program.idle_apply s
    · intro r hr q
      have he : (loadAt c i w r).inputSymbol = some w[r] := by
        rw [loadAt_input c i w hx r hr.le, List.getElem?_eq_getElem hr]
      unfold loadBody
      vcgen
      all_goals simp_all [loadAt_next]
    · intro q
      have he : (loadAt c i w w.length).inputSymbol = none := by
        rw [loadAt_input c i w hx _ le_rfl]
        simp
      unfold loadBody
      vcgen
      all_goals simp_all
  simpa only [loadAt_zero c i w hi hw hp] using h

/-- Load the entire raw input and restore its destination head, preserving all other fields. -/
@[spec]
theorem spec_load_cfg (c : Cfg κ (Option Bool) Unit xs) (i : κ)
    (w : List Bool) (z : ℕ) (hx : xs = w.toArray.map some) (hi : c.inputPos.val = 1)
    (hw : c.workTapes i = tape []) (hp : c.workPos i = 0) :
    Triple ((load i).verify (Program.cfgSemantics xs))
      (fun s b ↦ s = c ∧ b = 6 * w.length + 6 + z)
      (fun _ s b ↦ s = loaded c i w (Fin.last (xs.size + 1)) ∧ b = z) () := by
  have hl := load_loop_spec c i w (3 * w.length + 4 + z) hx hi hw hp
  have he : (loadAt c i w w.length).setWorkPos i 0 =
      loaded c i w (Fin.last (xs.size + 1)) := by
    apply Cfg.ext
    · rfl
    · apply Fin.ext
      simp [hx]
    · simp
    · simp [← hp]
    · rfl
  have hr : Triple ((rewind i).verify (Program.cfgSemantics xs)) _
      (fun _ s b ↦ s = loaded c i w (Fin.last (xs.size + 1)) ∧ b = z) () :=
    ⟨(spec_rewind_cfg (loadAt c i w w.length) i w w.length z
      (by simp) (by simp) le_rfl).entails_wp_of_post
      (by
        intro a s b h
        change s = (loadAt c i w w.length).setWorkPos i 0 ∧ b = z at h
        simpa only [he] using h)⟩
  unfold load
  vcgen [hl, hr]
  rename_i s b hs
  exact ⟨hs.1, by omega⟩

end Complexity.TM.Program.Word
