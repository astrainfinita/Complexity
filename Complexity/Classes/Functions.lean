/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Resources.TuringMachine.Asymptotics
public import Complexity.Asymptotics.Polynomial

/-! # Deterministic function complexity classes

These classes apply to arbitrary encoded input and output types. The resource
semantics come from the existing Turing-machine specifications. Decision classes
specialize the output to `Bool` and then interpret it as a predicate.
-/

@[expose] public section

namespace Complexity

variable {α β : Type*} [Encoding (List Bool) α] [Encoding (List Bool) β]

/-- Functions computable by a finite Turing machine in time `O(T(n))`. -/
def FTIME (T : ℕ → ℕ) : Set (α → β) :=
  {f | TM.ComputableInTimeO f T}

/-- Functions computable by a finite Turing machine in work space `O(S(n))`. -/
def FSPACE (S : ℕ → ℕ) : Set (α → β) :=
  {f | TM.ComputableInSpaceO f S}

/-- Functions computable by one finite Turing machine within both asymptotic bounds. -/
def FTISP (T S : ℕ → ℕ) : Set (α → β) :=
  {f | TM.ComputableInTimeAndSpaceO f T S}

/-- Polynomial-time functions between the chosen encoded types. -/
def FP : Set (α → β) :=
  ⋃ d : ℕ, FTIME (fun n => n ^ d)

variable {T S T' S' : ℕ → ℕ}

theorem FTIME.mono (h : IsBigO T T') : FTIME (α := α) (β := β) T ⊆ FTIME T' :=
  fun _ hf => TM.ComputableInTimeO.mono hf h

theorem FSPACE.mono (h : IsBigO S S') : FSPACE (α := α) (β := β) S ⊆ FSPACE S' :=
  fun _ hf => TM.ComputableInSpaceO.mono hf h

theorem FTISP.mono (ht : IsBigO T T') (hs : IsBigO S S') :
    FTISP (α := α) (β := β) T S ⊆ FTISP T' S' :=
  fun _ hf => TM.ComputableInTimeAndSpaceO.mono hf ht hs

theorem FTISP.subset_time : FTISP (α := α) (β := β) T S ⊆ FTIME T :=
  fun _ hf => TM.ComputableInTimeAndSpaceO.computableInTimeO hf

theorem FTISP.subset_space : FTISP (α := α) (β := β) T S ⊆ FSPACE S :=
  fun _ hf => TM.ComputableInTimeAndSpaceO.computableInSpaceO hf

theorem FTISP.subset_inter : FTISP (α := α) (β := β) T S ⊆ FTIME T ∩ FSPACE S :=
  fun _ hf => ⟨subset_time hf, subset_space hf⟩

namespace FP

variable {f : α → β}

theorem mem_iff_exists_ftime : f ∈ FP ↔ ∃ d : ℕ, f ∈ FTIME (fun n => n ^ d) :=
  Set.mem_iUnion

/-- A pointwise bound by `c * (n + 1) ^ d` establishes polynomial time. -/
theorem of_time_le {t : ℕ → ℕ} (h : TM.ComputableInTime f t)
    (c d : ℕ) (ht : ∀ n, t n ≤ c * (n + 1) ^ d) : f ∈ FP :=
  mem_iff_exists_ftime.mpr ⟨d, t, h, IsBigO.of_le_mul_add_one_pow c d ht⟩

theorem ftime_subset (d : ℕ) : FTIME (α := α) (β := β) (fun n => n ^ d) ⊆ FP :=
  fun _ hf => mem_iff_exists_ftime.mpr ⟨d, hf⟩

end FP

end Complexity
