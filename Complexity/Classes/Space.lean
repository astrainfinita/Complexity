/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Classes.Basic
public import Complexity.Classes.Functions
public import Complexity.Encoding.Bool

/-! # Deterministic space classes

`DSPACE S` bounds visited work cells asymptotically. A decider still terminates on
every valid input; the read-only input and append-only output are excluded from space.
-/

@[expose] public section

namespace Complexity

variable {α : Type*} [Encoding (List Bool) α]

/-- Predicates decidable by a fixed finite Turing machine in work space `O(S(n))`. -/
def DSPACE (S : ℕ → ℕ) : Set (α → Prop) :=
  DecisionClass (FSPACE S)

namespace DSPACE

theorem of_decides {f : α → Bool} {p : α → Prop} {S : ℕ → ℕ}
    (hf : f ∈ FSPACE S) (hp : Decides f p) : p ∈ DSPACE S :=
  DecisionClass.of_decides hf hp

theorem mono {S S' : ℕ → ℕ} (h : IsBigO S S') : DSPACE (α := α) S ⊆ DSPACE S' :=
  DecisionClass.mono (FSPACE.mono h)

end DSPACE

end Complexity
