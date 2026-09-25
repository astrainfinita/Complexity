/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Classes.Basic
public import Complexity.Classes.TreeFunctions
public import Complexity.Encoding.Bool

/-!
# Deterministic tree-machine complexity classes

The classes use the size of each actual input tree and the fixed Boolean output
encoding. `TreeDTISP` requires a single machine satisfying both resource bounds;
membership in the separate time and space classes can use different machines.
-/

@[expose] public section

namespace Complexity

variable {α : Type*} [Encoding Tree α]

/-- Predicates decided by a tree machine with cumulative destination-size cost in `O(T)`. -/
def TreeDTIME (T : ℕ → ℕ) : Set (α → Prop) :=
  DecisionClass (TreeFTIME T)

/-- Predicates decided by a tree machine with expanded-tree space in `O(S)`. -/
def TreeDSPACE (S : ℕ → ℕ) : Set (α → Prop) :=
  DecisionClass (TreeFSPACE S)

/-- Predicates decided by one tree machine with time in `O(T)` and space in `O(S)`. -/
def TreeDTISP (T S : ℕ → ℕ) : Set (α → Prop) :=
  DecisionClass (TreeFTISP T S)

variable {f : α → Bool} {p : α → Prop} {T S T' S' : ℕ → ℕ}

theorem TreeDTIME.of_decides (hf : f ∈ TreeFTIME T)
    (hp : Decides f p) : p ∈ TreeDTIME T :=
  DecisionClass.of_decides hf hp

theorem TreeDSPACE.of_decides (hf : f ∈ TreeFSPACE S)
    (hp : Decides f p) : p ∈ TreeDSPACE S :=
  DecisionClass.of_decides hf hp

theorem TreeDTISP.of_decides (hf : f ∈ TreeFTISP T S)
    (hp : Decides f p) : p ∈ TreeDTISP T S :=
  DecisionClass.of_decides hf hp

theorem TreeDTIME.mono (hT : IsBigO T T') : TreeDTIME T ⊆ TreeDTIME (α := α) T' :=
  DecisionClass.mono (TreeFTIME.mono hT)

theorem TreeDSPACE.mono (hS : IsBigO S S') : TreeDSPACE S ⊆ TreeDSPACE (α := α) S' :=
  DecisionClass.mono (TreeFSPACE.mono hS)

theorem TreeDTISP.mono (hT : IsBigO T T') (hS : IsBigO S S') :
    TreeDTISP T S ⊆ TreeDTISP (α := α) T' S' :=
  DecisionClass.mono (TreeFTISP.mono hT hS)

theorem TreeDTISP.subset_time : TreeDTISP T S ⊆ TreeDTIME (α := α) T :=
  DecisionClass.mono TreeFTISP.subset_time

theorem TreeDTISP.subset_space : TreeDTISP T S ⊆ TreeDSPACE (α := α) S :=
  DecisionClass.mono TreeFTISP.subset_space

theorem TreeDTISP.subset_inter :
    TreeDTISP T S ⊆ TreeDTIME (α := α) T ∩ TreeDSPACE S :=
  fun _ h => ⟨subset_time h, subset_space h⟩

end Complexity
