/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Data.Tree.BitList
public import Complexity.Data.Tree.Encoding

/-! # Prefix codes for lists represented by trees -/

@[expose] public section

namespace Complexity.TreeMachine.Simulation.BitList

/-- A list cell's prefix code, excluding its tail. -/
def chunk : Bool → List Bool
  | false => [true, false]
  | true => [true, true, false, false]

/-- The ordinary prefix code of a list tree, shared by input and output. -/
def payload (bs : List Bool) : List Bool := bs.flatMap chunk ++ [false]

@[simp] theorem payload_nil : payload [] = [false] := rfl

@[simp] theorem payload_cons (b : Bool) (bs : List Bool) :
    payload (b :: bs) = chunk b ++ payload bs := by simp [payload, List.append_assoc]

theorem payload_eq_encodeTree (bs : List Bool) :
    payload bs = BitList.encodeTree (Tree.encodeBitList bs) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b <;>
      simpa [payload, chunk, BitList.encodeTree, Tree.encodeBitList, Tree.encodeBool,
        List.append_assoc] using ih

theorem length_chunk_le (b : Bool) : (chunk b).length ≤ 4 := by cases b <;> decide

theorem length_payload_le (bs : List Bool) : (payload bs).length ≤ 4 * bs.length + 1 := by
  rw [payload_eq_encodeTree]
  simpa only [BitList.length_encodeTree] using Tree.size_encodeBitList_le bs

end Complexity.TreeMachine.Simulation.BitList
