/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Classes.Time
public import Complexity.Classes.Space

/-! # Simultaneous deterministic time and space

`DTISP T S` requires one machine to meet both asymptotic bounds. Projecting a
witness gives membership in `DTIME T` and `DSPACE S`; separate witnesses for
those classes do not provide a simultaneous witness.
-/

@[expose] public section

namespace Complexity

variable {α : Type*} [Encoding (List Bool) α]

/-- Predicates decidable by one finite Turing machine in time `O(T(n))` and
work space `O(S(n))` simultaneously. -/
def DTISP (T S : ℕ → ℕ) : Set (α → Prop) :=
  DecisionClass (FTISP T S)

namespace DTISP

theorem of_decides {f : α → Bool} {p : α → Prop} {T S : ℕ → ℕ}
    (hf : f ∈ FTISP T S) (hp : Decides f p) : p ∈ DTISP T S :=
  DecisionClass.of_decides hf hp

theorem mono {T S T' S' : ℕ → ℕ} (hT : IsBigO T T') (hS : IsBigO S S') :
    DTISP (α := α) T S ⊆ DTISP T' S' :=
  DecisionClass.mono (FTISP.mono hT hS)

theorem subset_time {T S : ℕ → ℕ} : DTISP (α := α) T S ⊆ DTIME T :=
  DecisionClass.mono FTISP.subset_time

theorem subset_space {T S : ℕ → ℕ} : DTISP (α := α) T S ⊆ DSPACE S :=
  DecisionClass.mono FTISP.subset_space

theorem subset_inter {T S : ℕ → ℕ} :
    DTISP (α := α) T S ⊆ DTIME T ∩ DSPACE S :=
  fun _ h => ⟨subset_time h, subset_space h⟩

end DTISP

end Complexity
