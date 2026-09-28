/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Simulation.BitList.Encoding
public import Complexity.Control.Program.Bound
public import Complexity.Models.TuringMachine.Program.Specification.Configuration
public import Complexity.Models.TuringMachine.Program.Move

/-! # Decoding a serialized Boolean list from a work buffer -/

@[expose] public section

set_option experimental.vcgen true

namespace Complexity.TreeMachine.Simulation.BitList

open TM TM.Program Std.WP

variable {κ : Type} [DecidableEq κ] {xs : Array (Option Bool)}

private def placed (c : Cfg κ (Option Bool) Unit xs) (j : κ) (n : ℕ)
    (bs : List Bool) : Cfg κ (Option Bool) Unit xs :=
  { c with workPos := Function.update c.workPos j (c.workPos j + n)
           output := c.output ++ (bs.toArray.map some) }

private theorem at_zero (c : Cfg κ (Option Bool) Unit xs) (j : κ) :
    placed c j 0 [] = c := by
  simp [placed]

private theorem at_at (c : Cfg κ (Option Bool) Unit xs) (j : κ)
    (n m : ℕ) (bs cs : List Bool) :
    placed (placed c j n bs) j m cs = placed c j (n + m) (bs ++ cs) := by
  simp [placed, add_assoc, Array.append_assoc]

private theorem move_at (c : Cfg κ (Option Bool) Unit xs) (j : κ) :
    apply
      ({ idle (κ := κ) (Γ := Option Bool) with
      work := fun i ↦ (none, if i = j then 1 else 0) }) c = placed c j 1 [] := by
  simpa [moveAction, Cfg.setWorkPos, placed, SignType.cast] using
    moveAction_apply (Γ := Option Bool) j .pos c

private theorem emit_at (c : Cfg κ (Option Bool) Unit xs) (j : κ) (b : Bool) :
    apply
      ({ idle (κ := κ) (Γ := Option Bool) with output := some (some b) }) c =
      placed c j 0 [b] := by
  ext <;> simp [idle, placed]

/-- A list node contains either a nil tree or a pair of nil trees encoding its bit. -/
def outputBody (j : κ) : TM.Program κ (Option Bool) Bool := do
  let a ← read j
  if a = some true then
    advance j 1
    let b ← read j
    if b = some true then
      emit (some true)
      advance j 3
      pure false
    else
      emit (some false)
      advance j 1
      pure false
  else pure true

/-- Decode the simulator's serialization of a Boolean list, appending its raw bits. -/
def output (j : κ) : TM.Program κ (Option Bool) Unit := repeatUntil (outputBody j)

/-- The decoder preserves storage and the input head, and stops on the final nil token. -/
def outputCfg (c : Cfg κ (Option Bool) Unit xs) (j : κ) (bs : List Bool) :
    Cfg κ (Option Bool) Unit xs :=
  { c with workPos := Function.update c.workPos j (c.workPos j + (bs.flatMap chunk).length)
           output := c.output ++ bs.toArray.map some }

private def Reads (c : Cfg κ (Option Bool) Unit xs) (j : κ) (bs : List Bool) : Prop :=
  ∀ n, (h : n < (payload bs).length) →
    (c.workTapes j)[c.workPos j + n] = some (payload bs)[n]

omit [DecidableEq κ] in
private theorem reads_root (c : Cfg κ (Option Bool) Unit xs) (j : κ)
    (bs : List Bool) (h : Reads c j bs) :
    c.workSymbols j = some (!bs.isEmpty) := by
  have ht := h 0 (by simp only [payload, List.length_append, List.length_cons,
    List.length_nil]; omega)
  cases bs with
  | nil => simpa [Cfg.workSymbols, payload] using ht
  | cons b bs => cases b <;> simpa [Cfg.workSymbols, payload, chunk] using ht

private theorem reads_bit (c : Cfg κ (Option Bool) Unit xs) (j : κ)
    (b : Bool) (bs : List Bool) (h : Reads c j (b :: bs)) :
    (placed c j 1 []).workSymbols j = some b := by
  have ht := h 1 (by cases b <;> simp [payload, chunk])
  cases b <;> simpa [placed, Cfg.workSymbols, payload, chunk] using ht

private theorem reads_tail (c : Cfg κ (Option Bool) Unit xs) (j : κ)
    (b : Bool) (bs : List Bool) (h : Reads c j (b :: bs)) :
    Reads (placed c j (chunk b).length [b]) j bs := by
  intro n hn
  have he : payload (b :: bs) = chunk b ++ payload bs := by simp [payload]
  have ht := h ((chunk b).length + n) (by rw [he]; simp only [List.length_append]; omega)
  simp only [he, List.getElem_append_right (Nat.le_add_right (chunk b).length n),
    Nat.add_sub_cancel_left] at ht
  simpa [placed, Nat.cast_add, add_assoc] using ht

private theorem spec_outputBody_cons (c : Cfg κ (Option Bool) Unit xs) (j : κ)
    (b : Bool) (bs : List Bool) (q : ℕ) (h : Reads c j (b :: bs)) :
    Triple ((outputBody j).verify (cfgSemantics xs))
      (fun s n ↦ s = c ∧ n = (chunk b).length + 3 + q)
      (fun r s n ↦ r = false ∧ s = placed c j (chunk b).length [b] ∧ n = q) () := by
  have hr := reads_root c j (b :: bs) h
  have hb := reads_bit c j b bs h
  cases b <;> simp only [outputBody, advance] <;> vcgen
  all_goals simp_all [chunk, emit_at (j := j), move_at, at_at]

private theorem spec_outputBody_nil (c : Cfg κ (Option Bool) Unit xs) (j : κ)
    (q : ℕ) (h : Reads c j []) :
    Triple ((outputBody j).verify (cfgSemantics xs))
      (fun s n ↦ s = c ∧ n = 1 + q)
      (fun r s n ↦ r = true ∧ s = c ∧ n = q) () := by
  have hr := reads_root c j [] h
  simp only [outputBody, advance]
  vcgen
  all_goals simp_all

private def cost (bs : List Bool) : ℕ := (bs.flatMap chunk).length + 4 * bs.length + 2

private theorem outputCfg_cons (c : Cfg κ (Option Bool) Unit xs) (j : κ)
    (b : Bool) (bs : List Bool) :
    outputCfg (placed c j (chunk b).length [b]) j bs = outputCfg c j (b :: bs) := by
  change placed (placed c j (chunk b).length [b]) j (bs.flatMap chunk).length bs =
    placed c j ((b :: bs).flatMap chunk).length (b :: bs)
  simp [at_at]

private theorem spec_output_exact (c : Cfg κ (Option Bool) Unit xs) (j : κ)
    (bs : List Bool) (q : ℕ) (hw : Reads c j bs) :
    Triple ((output j).verify (cfgSemantics xs))
      (fun s n ↦ s = c ∧ n = cost bs + q)
      (fun _ s n ↦ s = outputCfg c j bs ∧ n = q) () := by
  let I : Cfg κ (Option Bool) Unit xs → ℕ → Prop := fun s n ↦
    ∃ cs, Reads s j cs ∧ outputCfg s j cs = outputCfg c j bs ∧ n = cost cs + q
  have h : Triple ((output j).verify (cfgSemantics xs)) (fun s n ↦ I s n)
      (fun _ s n ↦ s = outputCfg c j bs ∧ n = q) () := by
    apply cfg_spec_repeatUntil (outputBody j) I
    · rintro s n ⟨cs, _, _, hn⟩
      simp only [cost] at hn
      omega
    · constructor
      rintro s n ⟨cs, hr, he, hn⟩
      cases cs with
      | nil =>
        apply (Triple.entails_wp_of_post (spec_outputBody_nil s j q hr) ?_) s n
          ⟨rfl, by simp only [cost, List.flatMap_nil, List.length_nil] at hn; omega⟩
        rintro r t z ⟨rfl, rfl, rfl⟩
        exact ⟨(at_zero t j).symm.trans he, rfl⟩
      | cons b cs =>
        apply (Triple.entails_wp_of_post
          (spec_outputBody_cons s j b cs (cost cs + q) hr) ?_) s n
          ⟨rfl, by simp only [cost, List.flatMap_cons, List.length_append,
            List.length_cons] at *; omega⟩
        rintro r t z ⟨rfl, rfl, rfl⟩
        exact ⟨cs, reads_tail s j b cs hr, (outputCfg_cons s j b cs).trans he, rfl⟩
  constructor
  rintro s n ⟨hs, hn⟩
  subst s n
  exact h.le_wp c (cost bs + q) ⟨bs, hw, rfl, rfl⟩

/-- Decode a well-formed serialized list in linear time, preserving all work storage.
The selected head starts at zero and ends on the root token of the terminal nil. -/
@[spec]
theorem spec_output (c : Cfg κ (Option Bool) Unit xs) (j : κ)
    (bs : List Bool) (q : ℕ)
    (hw : c.workTapes j = IntMemory.ofArray ((payload bs).toArray.map some))
    (hp : c.workPos j = 0) :
    Triple ((output j).verify (cfgSemantics xs))
      (fun s n ↦ s = c ∧ 12 * bs.length + 2 + q ≤ n)
      (fun _ s n ↦ s = outputCfg c j bs ∧ q ≤ n) () := by
  have hr : Reads c j bs := by
    intro n hn
    simp [hw, hp, hn]
  have hc : cost bs ≤ 12 * bs.length + 2 := by
    have h := length_payload_le bs
    simp only [payload, List.length_append, List.length_cons, List.length_nil] at h
    unfold cost
    omega
  exact Program.spec_exact_budget_le
    (fun q ↦ spec_output_exact c j bs q hr) hc q

end Complexity.TreeMachine.Simulation.BitList
