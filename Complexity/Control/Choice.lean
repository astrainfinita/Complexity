/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.Control.Monad.Basic
public import Mathlib.Data.Multiset.Functor

/-!
# Single-step choices and their interpretations

A choice shape describes the alternatives available in one machine step. It need not be a
monad: sequencing belongs to the target of an interpretation. In particular, interpreting
`Binary` repeatedly makes a fresh choice each time; the Reader monad on `Fin 2 → α` would
instead reuse the same branch index throughout a computation.
-/

@[expose] public section

universe u

namespace Complexity.Choice

/-- Interpret the alternatives of one step in a semantic effect. -/
abbrev Interpretation (F : Type u → Type*) (m : Type u → Type*) :=
  ∀ {α : Type u}, F α → m α

/-- Two labelled alternatives. The two results are allowed to coincide. -/
abbrev Binary (α : Type*) := Fin 2 → α

namespace Interpretation

/-- Leave an already interpreted effect unchanged. -/
def id (F : Type* → Type*) : Interpretation F F := fun a => a

/-- Embed a deterministic step in a semantic monad. -/
def pure (m : Type* → Type*) [Monad m] : Interpretation Id m :=
  fun a => Pure.pure a.run

end Interpretation

/-- Collect both alternatives without ordering them, retaining their multiplicities. -/
def binaryMultiset : Interpretation Binary Multiset := fun f => ↑[f 0, f 1]

end Complexity.Choice
