/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.Controller.RunHistory

/-! # Continuing execution with its existing history -/

@[expose] public section

universe u

namespace Complexity.Controller

variable {F : Type u → Type*} {Observation Q : Type*} {Action Config : Type u}
  [HasState Config Q] [Observe Config Observation] [Apply Config Action]

omit [Observe Config Observation] in
@[simp] theorem halted_history (M : Controller F Observation Action Q)
    (p : History Config Action) : M.Halted p ↔ M.Halted p.last := Iff.rfl

section Deterministic

variable (M : Controller Id Observation Action Q)

@[simp] theorem last_runFrom (p : History Config Action) (n : ℕ) :
    (M.runFrom p n).last = M.runFrom p.last n :=
  congrArg Id.run (M.last_runFromWith Id p n)

end Deterministic
end Complexity.Controller
