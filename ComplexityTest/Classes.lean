/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Classes.Nondeterministic.Deterministic
import Complexity.Classes.TreeTuringSimulation

open Complexity

namespace Complexity.ClassesTest

-- A fixed one-step finite machine copies its input bit to the Boolean output.
private def bit : TM Id (Fin 0) (Option Bool) Bool where
  q₀ := false
  halt := id
  transition := fun _ (a, _) ↦ pure <|
    { inputMove := 0, work := Fin.elim0, output := some a, state := true }

private theorem bit_spec : TM.Computes bit (id : Bool → Bool) (fun _ => 1) (fun _ => 0) := by
  apply TM.computes_iff.mpr
  apply Computes.iff_of_uniqueEncoding.mpr
  intro b
  apply Controller.computes_unit_iff.mpr
  refine ⟨rfl, ?_, ?_⟩
  · change #[((encode (List Bool) b).map some).toArray[0]?.getD none] = _
    simp
  · simp [Controller.History.space]

private theorem bit_fp : (id : Bool → Bool) ∈ FP TM.timeSpaceModel :=
  FP.of_time_le bit_spec.computableInTimeAndSpace.computableInTime
    1 0 (by intro n; simp)

-- The same function covers both acceptance and rejection, with no work tapes.
example : (fun b : Bool => b = true) ∈ P TM.timeSpaceModel := by
  apply P.of_decides bit_fp
  intro b
  rfl

-- Increasing the time budget does not change output or invent extra space.
example : TM.Computes bit (id : Bool → Bool) (fun _ => 5) (fun _ => 0) :=
  bit_spec.mono (fun _ => by decide) (fun _ => le_rfl)

-- The exact proof supplies a single machine for both asymptotic bounds.
example : (fun b : Bool => b = true) ∈ DTISP TM.timeSpaceModel (fun _ => 1) (fun _ => 0) :=
  DTISP.of_decides bit_spec.computableInTimeAndSpace.mem_ftisp
    (fun _ => Iff.rfl)

-- A halted tree machine already has the Boolean result in its input/output register.
private def tree : TreeMachine Id 1 Unit where
  q₀ := ()
  halt _ := true
  transition _ _ := pure <| TreeMachine.Action.keep ()

private theorem tree_spec :
    TreeMachine.Computes tree (id : Bool → Bool) (fun _ => 0) id := by
  apply Computes.iff_of_uniqueEncoding.mpr
  intro b
  refine ⟨0, rfl, ?_, le_rfl, ?_⟩
  · exact TreeMachine.input_get (0 : Fin 1) _
  · simp [TreeMachine.Cfg.mass]

private theorem tree_fp : (id : Bool → Bool) ∈ FP TreeMachine.timeSpaceModel :=
  FP.of_time_le tree_spec.computableInTimeAndSpace.computableInTime
    0 0 (by intro n; simp)

example : (fun b : Bool => b = true) ∈ P TreeMachine.timeSpaceModel := by
  apply P.of_decides tree_fp
  intro b
  rfl

example : (fun b : Bool => b = true) ∈ DTISP TreeMachine.timeSpaceModel (fun _ => 0) id :=
  DTISP.of_decides tree_spec.computableInTimeAndSpace.mem_ftisp
    (fun _ => Iff.rfl)

-- Tree input storage counts toward space even when no transition is executed.
example : ¬TreeMachine.Computes tree (id : Bool → Bool) (fun _ => 0) (fun _ => 0) := by
  intro h
  have hh := (Computes.iff_of_uniqueEncoding.mp h) false
  have hm := hh.mass_le 0
  change (TreeMachine.Cfg.mk () (TreeMachine.input (0 : Fin 1) Tree.nil)).mass ≤ 0 at hm
  simp [ TreeMachine.Cfg.mass] at hm

-- The abstract interface stays in Type, without storing a type of machine witnesses.
example : Type := TimeSpaceModel Id (List Bool)

-- Constants and finite initial exceptions are absorbed by O(n) for any model.
example {Data α : Type*} [Encoding Data α] [Encoding Data Bool]
    (model : TimeSpaceModel Id Data) :
    DTIME model (α := α) (fun n => 5 * n + 17) ⊆ DTIME model id :=
  DTIME.mono (IsBigO.iff_exists_nat.2 ⟨22, 1, fun n hn => by dsimp; omega⟩)

-- The simultaneous class projects to the two separate classes.
example {Data α : Type*} [Encoding Data α] [Encoding Data Bool]
    (model : TimeSpaceModel Id Data) {p : α → Prop} {T S : ℕ → ℕ}
    (h : p ∈ DTISP model T S) : p ∈ DTIME model T ∧ p ∈ DSPACE model S :=
  DTISP.subset_inter h

end Complexity.ClassesTest
