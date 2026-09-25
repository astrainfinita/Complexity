/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.Choice
public import Mathlib.Probability.Distributions.Uniform

/-!
# Fair probabilistic interpretation of binary choices

Each call samples a uniform branch index before applying the branch function. Composing
calls with `PMF.bind` therefore samples afresh and adds the probabilities of coincident
results.
-/

@[expose] public section

namespace Complexity.Choice

/-- Interpret one binary choice as a fair coin, including when its results coincide. -/
noncomputable def binaryPMF : Interpretation Binary PMF :=
  fun f => (PMF.uniformOfFintype (Fin 2)).map f

end Complexity.Choice
