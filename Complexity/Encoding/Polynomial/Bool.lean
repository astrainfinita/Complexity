/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Encoding.Bool
public import Complexity.Encoding.Polynomial.Basic

/-! # Polynomial compatibility of Boolean encodings

The two representations differ by one list constructor. Projection removes it;
pairing with an empty register inserts it. Both conversions take one transition.
-/

@[expose] public section

namespace Complexity.Encoding

open TreeMachine

private def convert (o : Op 2) : TreeMachine Id 2 Bool where
  q₀ := false
  halt := id
  transition _ _ := pure <| .assign true o

private theorem convert_left (a : Tree) :
    (convert (.left 0 0)).ComputesInTimeAndSpace
      a a.left a.size (2 * a.size + 2) := by
  refine ComputesInTimeAndSpace.of_run (n := 1) rfl ?_ ?_ (by omega)
  · simp [Controller.run, Controller.runFrom_succ, step_eq, convert,
      initInput_tree, Op.eval]
  · simpa [Controller.runHistory, Controller.actionSum_runHistoryFrom_one,
      Action.timeCost, convert, initInput_tree, Op.timeCost, Action.assign, Op.dst, Op.eval,
      input_get] using Tree.size_left_le a

private theorem convert_pair (a : Tree) :
    (convert (.pair 0 0 1)).ComputesInTimeAndSpace
      a (.pair a .nil) (a.size + 2) (2 * a.size + 4) := by
  refine ComputesInTimeAndSpace.of_run (n := 1) rfl ?_ ?_ (by omega)
  · simp [Controller.run, Controller.runFrom_succ, step_eq, convert,
      initInput_tree, Op.eval]
  · simp [Controller.runHistory, Controller.actionSum_runHistoryFrom_one,
      Action.timeCost, convert, initInput_tree, Op.timeCost,
      Action.assign, Op.dst, Op.eval, input_get, input_get_of_ne, Tree.size]
    omega

private theorem left_mem_fp : (fun a : Tree => a.left) ∈ FP timeSpaceModel := by
  apply FP.of_time_le (t := fun n => n) ?_ 1 1 (by simp)
  refine ⟨fun n => 2 * n + 2,
    Computes.computableInTimeAndSpace (M := convert (.left 0 0)) ?_⟩
  exact Computes.iff_of_uniqueEncoding.mpr convert_left

private theorem pair_mem_fp : (fun a => Tree.pair a Tree.nil) ∈ FP timeSpaceModel := by
  apply FP.of_time_le (t := fun n => n + 2) ?_ 2 1 (by intro n; simp; omega)
  refine ⟨fun n => 2 * n + 4,
    Computes.computableInTimeAndSpace (M := convert (.pair 0 0 1)) ?_⟩
  exact Computes.iff_of_uniqueEncoding.mpr convert_pair

/-- Singleton bit strings and the leaf/pair encoding of Booleans admit
polynomial-time conversions in both directions. -/
instance : PolytimeCompatible Bool :=
  PolytimeCompatible.ofEncode left_mem_fp pair_mem_fp (fun _ => rfl) (fun _ => rfl)

end Complexity.Encoding
