/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Classes.Nondeterministic.Verifier
import Complexity.Tactic.TreeProgram.Library

open Complexity

namespace Complexity.BitsVerifierTest

-- Guards the use of the entry `nstack_of_bits_verifier`: the memberships of the verifier, a guess
-- containing `true`, and of the fuel, one unit per element, in `FP` are proved by `model_fun_prop`,
-- and the predicate, nonempty lists, is given through a guess no longer than the fuel.
example : (fun xs : List Bool ↦ xs ≠ []) ∈ NP .nstack := by
  refine nstack_of_bits_verifier (fun x : List Bool × List Bool ↦ x.2.or) (by model_fun_prop)
    (fun xs ↦ xs.map fun _ ↦ ()) (by model_fun_prop) fun xs ↦ ⟨fun h ↦ ⟨[true], ?_, rfl⟩, ?_⟩
  · obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil h
    simp
  · rintro ⟨_ | ⟨b, bs⟩, hl, hb⟩
    · simp at hb
    · rintro rfl
      simp at hl

end Complexity.BitsVerifierTest
