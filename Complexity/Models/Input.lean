/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.Basic.Sign.Defs
public import Mathlib.Data.Fin.Basic

/-! # Bounded read-only input head movement -/

@[expose] public section

namespace Complexity.Input

/-- Move an input head, leaving outward moves at a boundary in place. -/
def movePos {n : ℕ} (p : Fin (n + 2)) : SignType → Fin (n + 2)
  | .neg => ⟨p.val - 1, by have := p.isLt; omega⟩
  | .zero => p
  | .pos => ⟨min (p.val + 1) (n + 1), by omega⟩

@[simp]
theorem movePos_zero {n : ℕ} (p : Fin (n + 2)) : movePos p 0 = p := rfl

@[simp]
theorem movePos_left_boundary {n : ℕ} :
    movePos (0 : Fin (n + 2)) (-1) = 0 := by
  apply Fin.ext
  rfl

@[simp]
theorem movePos_right_boundary {n : ℕ} :
    movePos (⟨n + 1, by omega⟩ : Fin (n + 2)) 1 = ⟨n + 1, by omega⟩ := by
  apply Fin.ext
  simp [movePos]

end Complexity.Input
