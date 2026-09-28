/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.Controller.History

/-!
# Resource measurements of execution histories

Time and space are interpreted from the same history, so the measurements retain
all configurations and actions of one execution branch.
-/

@[expose] public section

namespace Complexity

/-- Time and space measurements of a complete execution history. -/
@[ext]
structure CostModel (Action Config : Type*) where
  /-- Time used by the recorded execution. -/
  time : Controller.History Config Action → ℕ
  /-- Space used by the recorded execution. -/
  space : Controller.History Config Action → ℕ

end Complexity
