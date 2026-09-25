/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Resources.TreeMachine.Asymptotics
public import Complexity.Asymptotics.Polynomial

/-!
# Function complexity classes on tree machines

The classes measure each actual input tree by its size. Time is cumulative destination-size
cost and space is expanded-tree size. `TreeFTISP` requires one machine satisfying
both bounds. Input and output encodings need not be unique.
-/

@[expose] public section

namespace Complexity

variable {α β : Type*} [Encoding Tree α] [Encoding Tree β]

/-- Functions computable by a tree machine with cumulative destination-size cost in `O(T)`. -/
def TreeFTIME (T : ℕ → ℕ) : Set (α → β) :=
  {f | TreeMachine.ComputableInTimeO f T}

/-- Functions computable by a tree machine with expanded-tree space in `O(S)`. -/
def TreeFSPACE (S : ℕ → ℕ) : Set (α → β) :=
  {f | TreeMachine.ComputableInSpaceO f S}

/-- Functions computable by one tree machine with time in `O(T)` and space in `O(S)`. -/
def TreeFTISP (T S : ℕ → ℕ) : Set (α → β) :=
  {f | TreeMachine.ComputableInTimeAndSpaceO f T S}

/-- Functions computable by a tree machine with polynomial cumulative destination-size cost. -/
def TreeFP : Set (α → β) :=
  ⋃ d : ℕ, TreeFTIME (fun n => n ^ d)

variable {f : α → β} {T S T' S' : ℕ → ℕ}

theorem TreeFTIME.mono (hT : IsBigO T T') :
    TreeFTIME T ⊆ TreeFTIME (α := α) (β := β) T' :=
  fun _ h => TreeMachine.ComputableInTimeO.mono h hT

theorem TreeFSPACE.mono (hS : IsBigO S S') :
    TreeFSPACE S ⊆ TreeFSPACE (α := α) (β := β) S' :=
  fun _ h => TreeMachine.ComputableInSpaceO.mono h hS

theorem TreeFTISP.mono (hT : IsBigO T T') (hS : IsBigO S S') :
    TreeFTISP T S ⊆ TreeFTISP (α := α) (β := β) T' S' :=
  fun _ h => TreeMachine.ComputableInTimeAndSpaceO.mono h hT hS

theorem TreeFTISP.subset_time :
    TreeFTISP T S ⊆ TreeFTIME (α := α) (β := β) T :=
  fun _ h => h.computableInTimeO

theorem TreeFTISP.subset_space :
    TreeFTISP T S ⊆ TreeFSPACE (α := α) (β := β) S :=
  fun _ h => h.computableInSpaceO

theorem TreeFTISP.subset_inter :
    TreeFTISP T S ⊆ TreeFTIME (α := α) (β := β) T ∩ TreeFSPACE S :=
  fun _ h => ⟨subset_time h, subset_space h⟩

namespace TreeFP

theorem mem_iff_exists_ftime :
    f ∈ TreeFP ↔ ∃ d : ℕ, f ∈ TreeFTIME (fun n => n ^ d) :=
  Set.mem_iUnion

/-- A pointwise bound by `c * (n + 1) ^ d` establishes polynomial time. -/
theorem of_time_le {t : ℕ → ℕ} (h : TreeMachine.ComputableInTime f t)
    (c d : ℕ) (ht : ∀ n, t n ≤ c * (n + 1) ^ d) : f ∈ TreeFP :=
  mem_iff_exists_ftime.mpr ⟨d, t, h, IsBigO.of_le_mul_add_one_pow c d ht⟩

theorem ftime_subset (d : ℕ) :
    TreeFTIME (fun n => n ^ d) ⊆ TreeFP (α := α) (β := β) :=
  fun _ h => mem_iff_exists_ftime.mpr ⟨d, h⟩

end TreeFP

end Complexity
