/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Classes.Functions.Basic

/-! # Polynomial-time many-one reductions

The reduction uses the chosen model and encodings. Identity and composition laws
require the corresponding closure properties of that model's polynomial-time functions.
-/

@[expose] public section

namespace Complexity

/-- A polynomial-time function preserves membership in the two decision problems. -/
def PolytimeManyOneReducible {Data α β : Type*} [Encoding Data α] [Encoding Data β]
    (model : TimeSpaceModel Id Data) (p : α → Prop) (q : β → Prop) : Prop :=
  ∃ f ∈ FP model, ∀ x, p x ↔ q (f x)

end Complexity
