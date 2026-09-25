/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Classes.TreeFunctions

/-! # Lifting computations on trees through unique encodings -/

@[expose] public section

namespace Complexity.TreeFP

/-- A polynomial-time function on raw trees computes a function on uniquely
encoded values when it sends each input encoding to the required output encoding. -/
theorem of_encode {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {f : Tree → Tree} {g : α → β} (hf : f ∈ TreeFP)
    (h : ∀ a, f (encode Tree a) = encode Tree (g a)) : g ∈ TreeFP := by
  obtain ⟨d, t, ⟨s, k, hk, Q, hQ, M, hm⟩, ht⟩ := mem_iff_exists_ftime.mp hf
  apply mem_iff_exists_ftime.mpr
  refine ⟨d, t, ⟨s, k, hk, Q, hQ, M, ?_⟩, ht⟩
  apply Computes.iff_of_uniqueEncoding.mpr
  intro a
  have hh := Computes.iff_of_uniqueEncoding.mp hm (encode Tree a)
  simpa only [Tree.encode_self, h] using hh

end Complexity.TreeFP
