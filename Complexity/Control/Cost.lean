/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.Data.Nat.Basic

/-!
# Local time and space costs

An action cost depends on the action selected and the data state before it is
executed. It is external to the controller and does not change the action's semantics.
`CostModel` pairs this time charge with the space occupied by a data state.
Running time adds action charges; running space takes the maximum state size,
including the initial and final states. Input encodings, program types, and bounds
on complete runs belong to other layers.
-/

@[expose] public section

namespace Complexity

/-- Local costs, with actions and stored data supplied as type parameters. -/
@[ext]
structure CostModel (Action Config : Type*) where
  /-- Charge for an action, measured on the data before execution. -/
  time : Action → Config → ℕ
  /-- Space occupied by the current data, maximized over a complete run. -/
  space : Config → ℕ

end Complexity
