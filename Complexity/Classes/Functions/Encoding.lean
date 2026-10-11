/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Classes.Functions.Basic

/-! # Lifting computations through unique encodings -/

@[expose] public section

namespace Complexity

/-- Equal output codes preserve simultaneous asymptotic bounds in the same model. -/
theorem FTISP.of_encode {Data α β γ : Type*} [Encoding Data α]
    [UniqueEncoding Data β] [UniqueEncoding Data γ]
    {model : TimeSpaceModel Id Data} {f : α → β} {g : α → γ} {T S : ℕ → ℕ}
    (hg : g ∈ FTISP model T S)
    (hfg : ∀ x, encode Data (f x) = encode Data (g x)) : f ∈ FTISP model T S := by
  obtain ⟨t, s, h, ht, hs⟩ := hg
  exact ⟨t, s, h.of_encode hfg, ht, hs⟩

namespace FP

attribute [local instance] UniqueEncoding.refl

/-- A polynomial-time function on raw data computes a function on uniquely
encoded values when it sends each input encoding to the required output encoding.
Raw data uses the identity encoding. -/
theorem of_encode {Data α β : Type*} [UniqueEncoding Data α] [UniqueEncoding Data β]
    {model : TimeSpaceModel Id Data} {f : Data → Data} {g : α → β} (hf : f ∈ FP model)
    (h : ∀ a, f (encode Data a) = encode Data (g a)) : g ∈ FP model := by
  obtain ⟨d, t, ⟨s, R, hR, hm⟩, ht⟩ := mem_iff_exists_ftime.mp hf
  apply mem_iff_exists_ftime.mpr
  refine ⟨d, t, ⟨s, R, hR, ?_⟩, ht⟩
  apply Encoding.Computes.iff_of_uniqueEncoding.mpr
  intro a
  have hh := Encoding.Computes.iff_of_uniqueEncoding.mp hm (encode Data a)
  simpa only [UniqueEncoding.refl_encode, id_eq, h] using hh

end FP

end Complexity
