/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Data.Embedding
import Mathlib.Data.Fintype.Fin

namespace TapeEmbeddingTest

-- Reverse the source order and leave gaps on both sides of its tapes.
def permuted : Fin 2 ↪ Fin 5 where
  toFun i := if i = 0 then 3 else 1
  inj' := by decide

-- Moving the entire five-tape bank one position right supplies a second layout.
def shifted : Fin 5 ↪ Fin 6 where
  toFun i := ⟨i.val + 1, by omega⟩
  inj' := by decide

def composed : Fin 2 ↪ Fin 6 := permuted.trans shifted

example : composed 0 = 4 ∧ composed 1 = 2 := by decide
example : 0 ∉ Set.range composed ∧ 1 ∉ Set.range composed := by decide

-- Replacement composition retains data outside both the source bank and the outer bank.
example (source : Fin 2 → ℕ) (target : Fin 6 → ℕ) :
    shifted.replace (permuted.replace source (target ∘ shifted)) target =
      composed.replace source target := permuted.replace_comp shifted source target

end TapeEmbeddingTest
