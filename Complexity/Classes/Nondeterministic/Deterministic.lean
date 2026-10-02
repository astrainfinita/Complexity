/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Resources.Nondeterministic.Deterministic
public import Complexity.Classes.Deterministic
public import Complexity.Classes.Nondeterministic

/-! # Deterministic classes are contained in nondeterministic classes

The inclusion duplicates each deterministic action, preserving the exact time
and work-space bounds before taking asymptotic or polynomial classes.
-/

@[expose] public section

namespace Complexity.TM

variable {α : Type*} [Encoding (List Bool) α]

theorem dtime_subset_ntime {T : ℕ → ℕ} : DTIME timeSpaceModel (α := α) T ⊆ NTIME T := by
  rintro p ⟨f, ⟨t, h, ht⟩, hp⟩
  exact ⟨t, decidableInTime_of_computable h hp, ht⟩

theorem dspace_subset_nspace {S : ℕ → ℕ} : DSPACE timeSpaceModel (α := α) S ⊆ NSPACE S := by
  rintro p ⟨f, ⟨s, h, hs⟩, hp⟩
  exact ⟨s, decidableInSpace_of_computable h hp, hs⟩

theorem dtisp_subset_ntisp {T S : ℕ → ℕ} : DTISP timeSpaceModel (α := α) T S ⊆ NTISP T S := by
  rintro p ⟨f, ⟨t, s, h, ht, hs⟩, hp⟩
  exact ⟨t, s, decidableInTimeAndSpace_of_computable h hp, ht, hs⟩

theorem p_subset_np : P timeSpaceModel (α := α) ⊆ NP := by
  intro p hp
  obtain ⟨d, hd⟩ := P.mem_iff_exists_dtime.mp hp
  exact NP.mem_iff_exists_ntime.mpr ⟨d, dtime_subset_ntime hd⟩

end Complexity.TM
