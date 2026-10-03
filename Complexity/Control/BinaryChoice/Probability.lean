/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.BinaryChoice.Basic
public import Mathlib.Probability.Distributions.Uniform

/-!
# Fair probabilistic interpretation of binary choices
-/

@[expose] public section

namespace Complexity.BinaryChoice

/-- Interpret each choice by independently sampling a uniform branch index. -/
noncomputable instance : MonadLift BinaryChoice PMF where
  monadLift f := (PMF.uniformOfFintype (Fin 2)).map f

@[simp] theorem monadLift_pmf {α : Type*} (f : BinaryChoice α) :
    (monadLift f : PMF α) = (PMF.uniformOfFintype (Fin 2)).map f := rfl

end Complexity.BinaryChoice
