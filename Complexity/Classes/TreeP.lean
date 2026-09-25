/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Classes.TreeBounds

/-!
# Polynomial-time decision problems on tree machines

`TreeP` uses the same function and Boolean-decision specifications as `P`, but
measures input tree size and cumulative destination-size cost. All other registers start
empty. Boolean results use `Tree.encodeBool` in the fixed output register.

This class is relative to an `Encoding Tree α`. Comparing it with the bit-string
class requires compatible encodings and an actual machine conversion theorem.
-/

@[expose] public section

namespace Complexity

variable {α : Type*} [Encoding Tree α]

/-- Predicates decidable by a single finite-control tree machine with polynomial
cumulative destination-size cost, measured on each valid input tree. -/
def TreeP : Set (α → Prop) :=
  DecisionClass TreeFP

namespace TreeP

theorem of_decides {f : α → Bool} {p : α → Prop}
    (hf : f ∈ TreeFP) (hp : Decides f p) : p ∈ TreeP :=
  DecisionClass.of_decides hf hp

theorem congr {p q : α → Prop} (hp : p ∈ TreeP) (h : ∀ a, p a ↔ q a) : q ∈ TreeP :=
  DecisionClass.congr hp h

theorem eq_iUnion_treeDTIME :
    TreeP (α := α) = ⋃ d : ℕ, TreeDTIME (fun n => n ^ d) :=
  DecisionClass.iUnion _

theorem mem_iff_exists_treeDTIME {p : α → Prop} :
    p ∈ TreeP ↔ ∃ d : ℕ, p ∈ TreeDTIME (fun n => n ^ d) := by
  rw [eq_iUnion_treeDTIME, Set.mem_iUnion]

end TreeP

end Complexity
