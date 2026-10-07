/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.Data.List.Basic

/-! # Raw encoding carriers

`RawWord Γ` marks symbols at an encoding boundary. Machines and algorithms use
ordinary lists or arrays; the wrapper does not supply another container API.
-/

@[expose] public section

namespace Complexity

/-- An uninterpreted code over an arbitrary alphabet. -/
@[ext]
structure RawWord (Γ : Type*) where
  /-- Regard a list as raw symbols, without encoding its list structure. -/
  ofList ::
  /-- The underlying symbols, in order. -/
  toList : List Γ
  deriving DecidableEq, Repr, Inhabited

namespace RawWord

variable {Γ : Type*}

@[simp] theorem toList_ofList (xs : List Γ) : (ofList xs).toList = xs := rfl

@[simp] theorem ofList_toList (w : RawWord Γ) : ofList w.toList = w := rfl

@[simp] theorem toList_inj {v w : RawWord Γ} : v.toList = w.toList ↔ v = w :=
  ⟨RawWord.ext, congrArg toList⟩

/-- The size of a code is its number of symbols. -/
def length (w : RawWord Γ) : ℕ := w.toList.length

@[simp] theorem length_toList (w : RawWord Γ) : w.toList.length = w.length := rfl
@[simp] theorem length_ofList (xs : List Γ) : (ofList xs).length = xs.length := rfl

end RawWord
end Complexity
