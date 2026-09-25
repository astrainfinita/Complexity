/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Classes.Basic
public import Complexity.Classes.Functions
public import Complexity.Encoding.Bool

/-! # Deterministic time classes

`DTIME T` uses an asymptotic time bound and the fixed one-bit decision output.
The input encoding may be partial or redundant; all its valid codes are covered.
-/

@[expose] public section

namespace Complexity

variable {α : Type*} [Encoding (List Bool) α]

/-- Predicates decidable by a fixed finite Turing machine in time `O(T(n))`. -/
def DTIME (T : ℕ → ℕ) : Set (α → Prop) :=
  DecisionClass (FTIME T)

namespace DTIME

theorem of_decides {f : α → Bool} {p : α → Prop} {T : ℕ → ℕ}
    (hf : f ∈ FTIME T) (hp : Decides f p) : p ∈ DTIME T :=
  DecisionClass.of_decides hf hp

theorem mono {T T' : ℕ → ℕ} (h : IsBigO T T') : DTIME (α := α) T ⊆ DTIME T' :=
  DecisionClass.mono (FTIME.mono h)

end DTIME

end Complexity
