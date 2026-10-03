/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Simulation.BitList.Encoding
public import Complexity.Models.StackMachine.Program.IO

/-! # Decoding a serialized Boolean list from a stack -/

@[expose] public section

set_option experimental.vcgen true

namespace Complexity.TreeMachine.Simulation.BitList

open StackMachine StackMachine.Program Std.WP

variable {κ : Type} [DecidableEq κ] {xs : Array Bool}

/-- A list node contains either a nil tree or a pair of nil trees encoding its bit. -/
def outputBody (j : κ) : StackMachine.Program κ Bool Bool := do
  let a ← read j
  if a = some true then
    pop j
    let b ← read j
    if b = some true then
      act (IO.emitAction j true)
      pop j
      pop j
      pure false
    else
      act (IO.emitAction j false)
      pure false
  else pure true

/-- Decode a list tree, consuming its cells and leaving the terminal nil token. -/
def output (j : κ) : StackMachine.Program κ Bool Unit := repeatUntil (outputBody j)

/-- Decoding preserves the input head and other stacks, and appends the decoded bits. -/
@[simps -fullyApplied]
def outputCfg (c : Cfg κ Bool Unit xs) (j : κ) (bs suffix : List Bool) :
    Cfg κ Bool Unit xs :=
  { c.setStack j (false :: suffix) with output := c.output ++ bs.toArray }

private theorem spec_outputBody_cons (c : Cfg κ Bool Unit xs) (j : κ)
    (b : Bool) (bs suffix : List Bool) (q : ℕ)
    (hw : c.stacks j = payload (b :: bs) ++ suffix) :
    Triple ((outputBody j).verify (semantics xs))
      (fun s n ↦ s = c ∧ 6 + q ≤ n)
      (fun r s n ↦ r = false ∧ s = IO.emitted c j [b] (payload bs ++ suffix) ∧ q ≤ n) () := by
  cases b <;> simp only [outputBody] <;> vcgen
  all_goals first | omega |
    (simp_all [payload_cons, chunk, Cfg.ext_iff] <;> omega)

/-- Decode a serialized list in linear time, leaving its terminal nil and stack suffix. -/
@[spec]
theorem spec_output (c : Cfg κ Bool Unit xs) (j : κ)
    (bs suffix : List Bool) (q : ℕ) (hw : c.stacks j = payload bs ++ suffix) :
    Triple ((output j).verify (semantics xs))
      (fun s n ↦ s = c ∧ 7 * bs.length + 2 + q ≤ n)
      (fun _ s n ↦ s = outputCfg c j bs suffix ∧ q ≤ n) () := by
  let cfgAt := fun k ↦ IO.emitted c j (bs.take k) (payload (bs.drop k) ++ suffix)
  have h := Program.spec_repeatUntilWith_count_of_invariant idle (outputBody j)
    (semantics xs) (fun k s n ↦ s = cfgAt k ∧ 7 * (bs.length - k) + 2 + q ≤ n)
    (fun s n ↦ s = outputCfg c j bs suffix ∧ q ≤ n) bs.length
    (by intro k hk s n hs; simpa only [semantics_act, idle_apply] using hs)
    (by rintro k hk s n ⟨hs, hn⟩; omega)
    (by
      intro k hk
      have hr : (cfgAt k).stacks j = payload (bs[k] :: bs.drop (k + 1)) ++ suffix := by
        simp only [cfgAt, IO.emitted_stacks, Cfg.setStack_stacks, Function.update_self,
          List.drop_eq_getElem_cons hk]
      have he : IO.emitted (cfgAt k) j [bs[k]] (payload (bs.drop (k + 1)) ++ suffix) =
          cfgAt (k + 1) := by
        dsimp only [cfgAt]
        rw [List.take_succ_eq_append_getElem hk]
        ext i <;> simp
      have hb := spec_outputBody_cons (cfgAt k) j bs[k] (bs.drop (k + 1)) suffix
        (7 * (bs.length - (k + 1)) + 2 + q) hr
      rw [he] at hb
      constructor
      rintro s n ⟨hs, hn⟩
      exact hb.le_wp s n ⟨hs, by omega⟩)
    (by
      unfold outputBody
      vcgen
      all_goals first | omega | (simp_all [cfgAt, Cfg.ext_iff] <;> omega))
  simpa [output, repeatUntil, cfgAt, ← hw] using h

end Complexity.TreeMachine.Simulation.BitList
