/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Problems.CircuitSAT.CookLevin

open Complexity

namespace CookLevinTest

-- Guards `NP.manyOneReducible_circuitSAT` instantiated with polynomial-size circuit maps via
-- `StackMachine.isPoly_size_runCircuit`.
example {α : Type*} [UniqueEncoding (RawWord Bool) α] {p : α → Prop} (hp : p ∈ NP .ntm) :
    ManyOneReducible
      {f : α → Σ n, Circuit .booleanAlgebra n 1 |
        IsPoly (fun a ↦ ⌜a⌝₂.length) fun a ↦ (f a).2.size}
      p CircuitSAT :=
  NP.manyOneReducible_circuitSAT (fun _ _ _ _ M c d ↦
    (M.isPoly_size_runCircuit ⌜true⌝₂.toList
      ((IsPoly.const c).mul ((IsPoly.refl.add (.const 1)).pow d))).comp
      (h := fun a : α ↦ ⌜a⌝₂.toList) IsPoly.refl) hp

end CookLevinTest
