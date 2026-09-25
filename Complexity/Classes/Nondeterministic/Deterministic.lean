/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Resources.Nondeterministic.Deterministic
public import Complexity.Classes.DTISP
public import Complexity.Classes.P
public import Complexity.Classes.NP

/-! # Deterministic classes are contained in nondeterministic classes

The inclusion duplicates each deterministic action, preserving the exact time
and work-space bounds before taking asymptotic or polynomial classes.
-/

@[expose] public section

namespace Complexity

variable {α : Type*} [Encoding (List Bool) α]

theorem DTIME.subset_ntime {T : ℕ → ℕ} : DTIME (α := α) T ⊆ NTIME T := by
  rintro p ⟨f, ⟨t, h, ht⟩, hp⟩
  exact ⟨t, h.decidableInTime hp, ht⟩

theorem DSPACE.subset_nspace {S : ℕ → ℕ} : DSPACE (α := α) S ⊆ NSPACE S := by
  rintro p ⟨f, ⟨s, h, hs⟩, hp⟩
  exact ⟨s, h.decidableInSpace hp, hs⟩

theorem DTISP.subset_ntisp {T S : ℕ → ℕ} : DTISP (α := α) T S ⊆ NTISP T S := by
  rintro p ⟨f, ⟨t, s, h, ht, hs⟩, hp⟩
  exact ⟨t, s, h.decidableInTimeAndSpace hp, ht, hs⟩

theorem P.subset_np : P (α := α) ⊆ NP := by
  intro p hp
  obtain ⟨d, hd⟩ := P.mem_iff_exists_dtime.mp hp
  exact NP.mem_iff_exists_ntime.mpr ⟨d, DTIME.subset_ntime hd⟩

end Complexity
