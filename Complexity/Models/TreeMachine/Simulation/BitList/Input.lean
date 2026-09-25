/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Simulation.BitList.Encoding
public import Complexity.Models.TuringMachine.Program.Word.Write
public import Complexity.Control.Program.Traverse

/-! # Preparing a tree simulator's input from an ordinary bit string -/

@[expose] public section

set_option experimental.vcgen true

namespace Complexity.TreeMachine.Simulation.BitList.Input

open TM TM.Program TM.Program.Word Std.WP

variable {κ : Type} [DecidableEq κ] {xs : List Bool}

/-- Ordinary binary input, with a separate blank symbol. -/
def input (bs : List Bool) : Array (Option Bool) := bs.toArray.map some

/-- Expand one source bit, or stop at the right input boundary. -/
def body (j : κ) : TM.Program κ (Option Bool) Bool := do
  let b ← readInput
  if b = none then pure true
  else
    putWords j (chunk (b.getD false))
    moveInput 1
    pure false

/-- Serialize the single list tree into a work buffer. -/
def program (j : κ) : TM.Program κ (Option Bool) Unit := do
  repeatUntil (body j)
  putWords j [false]

/-- Input position after consuming `r` bits, clamped at the right boundary. -/
def position (xs : List Bool) (r : ℕ) : Fin ((input xs).size + 2) :=
  ⟨min (r + 1) (xs.length + 1), by simp only [input, Array.size_map, List.size_toArray]; omega⟩

private def loadAt (c : TM.Cfg κ (Option Bool) Unit (input xs)) (j : κ)
    (r : ℕ) : TM.Cfg κ (Option Bool) Unit (input xs) :=
  { written c j ((xs.take r).flatMap chunk) with inputPos := position xs r }

private theorem at_zero (c : TM.Cfg κ (Option Bool) Unit (input xs))
    (j : κ) (hi : c.inputPos.val = 1) :
    loadAt c j 0 = written c j [] := by
  have h : position xs 0 = c.inputPos := by apply Fin.ext; simp [position, hi]
  simp [loadAt, h, written]

private theorem at_input (c : TM.Cfg κ (Option Bool) Unit (input xs))
    (j : κ) (r : ℕ) (hr : r ≤ xs.length) :
    (loadAt c j r).inputSymbol = xs[r]? := by
  have hp : (position xs r).val = r + 1 := by simp [position, Nat.min_eq_left (by omega)]
  simp only [TM.Cfg.inputSymbol, loadAt, hp, input, Array.getElem?_map, List.getElem?_toArray]
  cases xs[r]? <;> rfl

private theorem at_next (c : TM.Cfg κ (Option Bool) Unit (input xs))
    (j : κ) (r : ℕ) (hr : r < xs.length) :
    apply
      ({ idle (κ := κ) (Γ := Option Bool) with inputMove := 1 })
      (written (loadAt c j r) j ((xs.take r).flatMap chunk ++ chunk xs[r])) =
        loadAt c j (r + 1) := by
  simp only [loadAt, List.take_succ_eq_append_getElem hr,
    List.flatMap_append, List.flatMap_singleton]
  apply TM.Cfg.ext
  · exact Subsingleton.elim _ _
  · simp only [apply_inputPos, written_inputPos]
    apply Fin.ext
    simp [position, moveInputPos, input]
    omega
  · funext i; simp [idle]
  · funext i; simp [idle]
  · rfl

private theorem spec_body_next (c : TM.Cfg κ (Option Bool) Unit (input xs))
    (j : κ) (r : ℕ) (hr : r < xs.length) (q : ℕ) :
    Triple ((body j).verify (cfgSemantics (input xs)))
      (fun s b ↦ s = loadAt c j r ∧ b = (chunk xs[r]).length + 2 + q)
      (fun a s b ↦ (a = false ∧ s = loadAt c j (r + 1)) ∧ b = q) () := by
  have hb : written (loadAt c j r) j ((xs.take r).flatMap chunk) =
      loadAt c j r := by simp [written, loadAt]
  have hw (v : Option Bool) := spec_putWords (loadAt c j r) j
    ((xs.take r).flatMap chunk) (chunk (v.getD false)) (q + 1)
  simp only [hb] at hw
  have he : (loadAt c j r).inputSymbol = some xs[r] := by
    rw [at_input c j r hr.le, List.getElem?_eq_getElem hr]
  have hn := at_next c j r hr
  unfold body
  vcgen [hw]
  all_goals simp_all <;> omega

private theorem spec_body_done (c : TM.Cfg κ (Option Bool) Unit (input xs))
    (j : κ) (q : ℕ) :
    Triple ((body j).verify (cfgSemantics (input xs)))
      (fun s b ↦ s = loadAt c j xs.length ∧ b = 1 + q)
      (fun a s b ↦ (a = true ∧ s = loadAt c j xs.length) ∧ b = q) () := by
  have he : (loadAt c j xs.length).inputSymbol = none := by
    rw [at_input c j xs.length le_rfl]
    simp
  have hw (v : Option Bool) := spec_putWords (loadAt c j xs.length) j
    ((xs.take xs.length).flatMap chunk) (chunk (v.getD false)) q
  unfold body
  vcgen [hw]
  all_goals simp_all

private theorem spec_loop (c : TM.Cfg κ (Option Bool) Unit (input xs))
    (j : κ) (q : ℕ) :
    Triple ((repeatUntil (body j)).verify (cfgSemantics (input xs)))
      (fun s b ↦ s = loadAt c j 0 ∧ 7 * xs.length + 2 + q ≤ b)
      (fun _ s b ↦ s = loadAt c j xs.length ∧ q ≤ b) () := by
  apply Complexity.Program.spec_repeatUntil_count_of_invariant idle (body j)
    (cfgSemantics (input xs))
    (fun r s b ↦ s = loadAt c j r ∧ 7 * (xs.length - r) + 2 + q ≤ b) _ xs.length
  · intro r hr s b hs
    exact idle_apply s
  · rintro r hr s b ⟨hs, hb⟩
    omega
  · intro r hr
    constructor
    rintro s b ⟨rfl, hb⟩
    have hnext := Complexity.Program.spec_exact_budget_le (spec_body_next c j r hr)
      (m := 6) (by have := length_chunk_le xs[r]; omega)
      (7 * (xs.length - (r + 1)) + 2 + q)
    simpa only [and_assoc] using hnext.le_wp _ b ⟨rfl, by omega⟩
  · constructor
    rintro s b ⟨rfl, hb⟩
    have hstop := Complexity.Program.spec_exact_budget_le (spec_body_done c j) le_rfl q
    simpa only [and_assoc] using hstop.le_wp _ b ⟨rfl, by omega⟩

/-- Complete adapter configuration, leaving the buffer head at its right end. -/
def result (c : TM.Cfg κ (Option Bool) Unit (input xs)) (j : κ) :
    TM.Cfg κ (Option Bool) Unit (input xs) :=
  { c with inputPos := position xs xs.length
           workTapes := Function.update c.workTapes j
             (IntMemory.ofArray ((payload xs).toArray.map some))
           workPos := Function.update c.workPos j (payload xs).length }

/-- The adapter changes only its buffer and the input head, and leaves the
buffer ready to rewind. -/
@[spec]
theorem spec_program (c : TM.Cfg κ (Option Bool) Unit (input xs))
    (j : κ) (q : ℕ)
    (hi : c.inputPos.val = 1) (hw : c.workTapes j = ∅) (hp : c.workPos j = 0) :
    Triple ((program j).verify (cfgSemantics (input xs)))
      (fun s b ↦ s = c ∧ 7 * xs.length + 3 + q ≤ b)
      (fun _ s b ↦ s = result c j ∧ q ≤ b) () := by
  have he : written c j [] = c := by simp [written, ← hw, ← hp]
  have h₁ := spec_loop c j (1 + q)
  rw [at_zero c j hi, he] at h₁
  have h₂ := spec_putWords_le (loadAt c j xs.length) j
    (xs.flatMap chunk) [false] q
  have he' : written (loadAt c j xs.length) j (xs.flatMap chunk) =
      loadAt c j xs.length := by simp [written, loadAt]
  rw [he'] at h₂
  have hf : written (loadAt c j xs.length) j (xs.flatMap chunk ++ [false]) =
      result c j := by
    simp [written, loadAt, result, payload, tape, IntMemory.ofList]
  rw [hf] at h₂
  unfold program
  vcgen [h₁, h₂]
  all_goals simp_all <;> omega

end Complexity.TreeMachine.Simulation.BitList.Input
