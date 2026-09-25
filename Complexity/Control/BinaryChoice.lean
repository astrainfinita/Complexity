/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.Control.Monad.Basic
public import Mathlib.Data.Multiset.Functor

/-!
# Binary choices and their multiset interpretation
-/

@[expose] public section

namespace Complexity

/-- Two labelled alternatives for one machine step; their results may coincide. -/
abbrev BinaryChoice (α : Type*) := Fin 2 → α

namespace BinaryChoice

/-- Enumerate both alternatives without ordering them, retaining their multiplicities. -/
instance : MonadLift BinaryChoice Multiset where
  monadLift f := ↑[f 0, f 1]

@[simp] theorem monadLift_multiset {α : Type*} (f : BinaryChoice α) :
    (monadLift f : Multiset α) = ↑[f 0, f 1] := rfl

end BinaryChoice
end Complexity
