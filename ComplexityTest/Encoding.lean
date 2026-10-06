/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Encoding.Polynomial.Bool
import Complexity.Encoding.Fin
import Complexity.Encoding.Nat
import Mathlib.Logic.Equiv.Bool

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

section Pullback

@[instance_reducible]
noncomputable def successor : UniqueEncoding ℕ ℕ :=
  (UniqueEncoding.refl ℕ).ofInjective Nat.succ Nat.succ_injective

example (n : ℕ) : successor.encode n = n + 1 := rfl

example (n : ℕ) : n ∈ successor.decode (n + 1) := successor.mem_decode_iff.mpr rfl

example : successor.decode 0 = Part.none := by
  apply Part.eq_none_iff.mpr
  intro n hn
  exact Nat.succ_ne_zero n (successor.mem_decode_iff.mp hn)

example {R α β : Type*} (c : UniqueEncoding R α) (e : β ≃ α) :
    (c.ofEquiv e).toEncoding = (c.ofInjective e e.injective).toEncoding := by
  apply Encoding.ext
  intro r
  apply Part.ext
  intro b
  exact (c.ofEquiv e).mem_decode_iff.trans (c.ofInjective e e.injective).mem_decode_iff.symm

@[instance_reducible]
def negated : UniqueEncoding Bool Bool := (UniqueEncoding.refl Bool).ofEquiv Equiv.boolNot

example : negated.decode false = Part.some true :=
  Part.eq_some_iff.mpr (negated.mem_decode_iff.mpr rfl)

end Pullback

section FiniteFunctions

example (f : Fin 3 → Fin 2) : encode Tree f = encode Tree (List.ofFn f) := rfl

example (f : Fin 3 → Fin 2) : decode (Fin 3 → Fin 2) (encode Tree f) = Part.some f :=
  UniqueEncoding.decode_encode f

example : encode Tree (![1, 0, 1] : Fin 3 → Fin 2) = encode Tree ([1, 0, 1] : List ℕ) := rfl

example : encode Tree (Fin.elim0 : Fin 0 → Fin 0) = Tree.nil := rfl

example : List.decodeFinFunction 2 ([false] : List Bool) = none := rfl

example : List.decodeFinFunction 2 ([false, true, false] : List Bool) = none := rfl

example : (List.decodeFinFunction 2 [false, true]).map (fun f => f 1) = some true := rfl

example : decode (Fin 0) (encode Tree (0 : ℕ)) = Part.none := by
  apply Part.eq_none_iff.mpr
  intro i
  exact Fin.elim0 i

example : decode (Fin 2) (encode Tree (2 : ℕ)) = Part.none := by
  apply Part.eq_none_iff.mpr
  intro i hi
  have hcode := UniqueEncoding.mem_decode_iff.mp hi
  have heq : i.val = 2 := by
    simpa only [encode_fin, UniqueEncoding.encode_inj] using hcode
  exact (Nat.ne_of_lt i.isLt) heq

example : decode (Fin 3 → Bool) (encode Tree [false, true]) = Part.none := by
  apply Part.eq_none_iff.mpr
  intro f hf
  have heq : List.ofFn f = [false, true] := by
    simpa using UniqueEncoding.mem_decode_iff.mp hf
  have := congrArg List.length heq
  simp at this

end FiniteFunctions

-- Both instances reuse the exact encoders used by the tree-machine simulation.
example (xs : List Bool) : encode Tree xs = Tree.encodeBitList xs := rfl
example (a : Tree) : encode (List Bool) a = BitList.encodeTree a := rfl

example : encode (List Bool) (encode Tree [false, true]) =
    [true, false, true, true, false, false, false] := rfl

-- Tree parsing rejects surplus input instead of accepting extra representations.
example : decode Tree [false, false] = Part.none := rfl

-- A tree in the wrong list format does not denote a bit string.
example : decode (List Bool)
    (Tree.pair (Tree.pair Tree.nil (Tree.pair Tree.nil Tree.nil)) Tree.nil) = Part.none := by
  apply Part.eq_none_iff.mpr
  rintro (_ | ⟨(_ | _), bs⟩) <;> simp [UniqueEncoding.mem_decode_iff]

end Complexity.EncodingTest
