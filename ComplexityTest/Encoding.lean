/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Encoding

open Complexity

namespace Complexity.EncodingTest

-- The second component is irrelevant: each Boolean has infinitely many codes.
@[instance_reducible]
private def redundant : Encoding (Bool × ℕ) Bool :=
  (UniqueEncoding.refl (Bool × ℕ)).toEncoding.map Prod.fst
    fun b => ⟨(b, 0), rfl⟩

example (b : Bool) (n : ℕ) : b ∈ redundant.decode (b, n) :=
  Part.mem_some b

-- A decoder accepting redundant codes cannot be promoted to a unique encoding.
example : ¬ ∃ c : UniqueEncoding (Bool × ℕ) Bool, c.toEncoding = redundant := by
  rintro ⟨c, h⟩
  have h₀ : false ∈ c.decode (false, 0) := by rw [h]; exact Part.mem_some false
  have h₁ : false ∈ c.decode (false, 1) := by rw [h]; exact Part.mem_some false
  have := (c.mem_decode_iff.mp h₀).symm.trans (c.mem_decode_iff.mp h₁)
  cases this

-- Generic code needs only the weaker class, even when an encoder is available.
example {R α : Type*} [UniqueEncoding R α] (a : α) : ∃ r : R, a ∈ decode α r :=
  Encoding.exists_code a

section Subtype

variable (p : ℕ → Prop)

local instance : UniqueEncoding ℕ {n // p n} := (UniqueEncoding.refl ℕ).subtype p

-- No DecidablePred instance is needed for this promise on the input.
example (n : ℕ) (h : p n) : decode {n // p n} n = Part.some (⟨n, h⟩ : {n // p n}) :=
  UniqueEncoding.decode_encode (R := ℕ) (⟨n, h⟩ : {n // p n})

example (n : ℕ) (h : ¬p n) : ¬(decode {n // p n} n).Dom := by
  rw [UniqueEncoding.dom_decode_iff]
  rintro ⟨a, rfl⟩
  exact h a.property

end Subtype

-- Both instances reuse the exact encoders used by the tree-machine simulation.
example (xs : List Bool) : encode Tree xs = Tree.encodeBitList xs := rfl
example (a : Tree) : encode (List Bool) a = BitList.encodeTree a := rfl

example : encode (List Bool) (encode Tree [false, true]) =
    [true, false, true, true, false, false, false] := rfl

-- Tree parsing rejects surplus input instead of accepting extra representations.
example : decode Tree [false, false] = Part.none := rfl

-- A tree in the wrong list format does not denote a bit string.
example : decode (List Bool)
    (Tree.pair (Tree.pair Tree.nil (Tree.pair Tree.nil Tree.nil)) Tree.nil) = Part.none := rfl

end Complexity.EncodingTest
