/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Classes.Basic
public import Complexity.Classes.Functions.Basic

/-! # Deterministic complexity classes

The chosen encodings may be partial or redundant; every valid input code is
covered. `DTIME` and `DSPACE` impose asymptotic resource bounds, and `DTISP`
requires one behavior to meet both bounds. `P` is the polynomial-time class.
A decider terminates on every valid input; the model determines which storage
contributes to space. No decision procedure for the predicate is required.
-/

@[expose] public section

namespace Complexity

variable {Data α : Type*} [Encoding Data α] [Encoding Data Bool]

/-- Predicates decidable in the given model in time `O(T(n))`. -/
def DTIME (model : TimeSpaceModel Id Data) (T : ℕ → ℕ) : Set (α → Prop) :=
  DecisionClass (FTIME model T)

namespace DTIME

variable {model : TimeSpaceModel Id Data}

theorem of_decides {f : α → Bool} {p : α → Prop} {T : ℕ → ℕ}
    (hf : f ∈ FTIME model T) (hp : Decides f p) : p ∈ DTIME model T :=
  DecisionClass.of_decides hf hp

theorem mono {T T' : ℕ → ℕ} (h : DominatedAtTop T T') :
    DTIME (α := α) model T ⊆ DTIME model T' :=
  DecisionClass.mono (FTIME.mono h)

end DTIME

/-- Predicates decidable in the given model in space `O(S(n))`. -/
def DSPACE (model : TimeSpaceModel Id Data) (S : ℕ → ℕ) : Set (α → Prop) :=
  DecisionClass (FSPACE model S)

namespace DSPACE

variable {model : TimeSpaceModel Id Data}

theorem of_decides {f : α → Bool} {p : α → Prop} {S : ℕ → ℕ}
    (hf : f ∈ FSPACE model S) (hp : Decides f p) : p ∈ DSPACE model S :=
  DecisionClass.of_decides hf hp

theorem mono {S S' : ℕ → ℕ} (h : DominatedAtTop S S') :
    DSPACE (α := α) model S ⊆ DSPACE model S' :=
  DecisionClass.mono (FSPACE.mono h)

end DSPACE

/-- Predicates decidable by one behavior in time `O(T(n))` and space `O(S(n))`. -/
def DTISP (model : TimeSpaceModel Id Data) (T S : ℕ → ℕ) : Set (α → Prop) :=
  DecisionClass (FTISP model T S)

namespace DTISP

variable {model : TimeSpaceModel Id Data}

theorem of_decides {f : α → Bool} {p : α → Prop} {T S : ℕ → ℕ}
    (hf : f ∈ FTISP model T S) (hp : Decides f p) : p ∈ DTISP model T S :=
  DecisionClass.of_decides hf hp

theorem mono {T S T' S' : ℕ → ℕ} (hT : DominatedAtTop T T') (hS : DominatedAtTop S S') :
    DTISP (α := α) model T S ⊆ DTISP model T' S' :=
  DecisionClass.mono (FTISP.mono hT hS)

theorem subset_time {T S : ℕ → ℕ} :
    DTISP (α := α) model T S ⊆ DTIME model T :=
  DecisionClass.mono FTISP.subset_time

theorem subset_space {T S : ℕ → ℕ} :
    DTISP (α := α) model T S ⊆ DSPACE model S :=
  DecisionClass.mono FTISP.subset_space

theorem subset_inter {T S : ℕ → ℕ} :
    DTISP (α := α) model T S ⊆ DTIME model T ∩ DSPACE model S :=
  fun _ h => ⟨subset_time h, subset_space h⟩

end DTISP

/-- Predicates decidable in polynomial time in the given model. -/
def P (model : TimeSpaceModel Id Data) : Set (α → Prop) :=
  DecisionClass (FP model)

namespace P

variable {model : TimeSpaceModel Id Data}

theorem of_decides {f : α → Bool} {p : α → Prop}
    (hf : f ∈ FP model) (hp : Decides f p) : p ∈ P model :=
  DecisionClass.of_decides hf hp

theorem congr {p q : α → Prop} (hp : p ∈ P model) (h : ∀ a, p a ↔ q a) :
    q ∈ P model :=
  DecisionClass.congr hp h

/-- The polynomial decision class is induced by the union of power-time function classes. -/
theorem eq_iUnion_dtime :
    P (α := α) model = ⋃ d : ℕ, DTIME model (fun n => n ^ d) :=
  DecisionClass.iUnion (fun d => FTIME model (fun n => n ^ d))

/-- Polynomial time is the union of the parameterized power-time classes. -/
theorem mem_iff_exists_dtime {p : α → Prop} :
    p ∈ P model ↔ ∃ d : ℕ, p ∈ DTIME model (fun n => n ^ d) := by
  rw [eq_iUnion_dtime, Set.mem_iUnion]

end P

end Complexity
