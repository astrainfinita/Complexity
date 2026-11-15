/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Resources.TimeSpaceModel.Basic
public import Complexity.Encoding.RawWord
public import Complexity.Models.TuringMachine.Deterministic

/-!
# Time and space complexity on multi-tape Turing machines

Functions use bit-string encodings. External bits occupy `some b` cells and
`none` is blank. Time counts transitions; space counts visited work cells and
excludes the read-only input and append-only output.

`TimeSpaceModel.tm.ComputableWithin` uses input-dependent budgets for all
legal representations. Complexity classes measure actual code length at their boundary.
Specifications require one fixed finite machine on all valid inputs. Time-only and
space-only variants omit one bound, but still require termination.
-/

@[expose] public section

namespace Complexity.TM

variable {α β : Type*} [Encoding (RawWord Bool) α] [Encoding (RawWord Bool) β]

/-- Finite Turing machines on bit strings, with transition time and visited
work-cell space. Each behavior is realized by one machine for all inputs. -/
def _root_.Complexity.TimeSpaceModel.tm : TimeSpaceModel Id (RawWord Bool) where
  inputSize := RawWord.length
  behaviors := {R | ∃ (κ : Type) (_ : Fintype κ) (Q : Type) (_ : Finite Q)
      (M : TM Id κ (Option Bool) Q),
      R = fun xs result =>
        M.ComputesWithin (xs.toList.map some) (result.run.toList.map some)}
  budget_mono := by
    rintro R ⟨κ, hκ, Q, hQ, M, rfl⟩ x y t s t' s' h ht hs
    exact h.mono ht hs

section InputBudgets

variable {α β : Type*} [Encoding (RawWord Bool) α] [Encoding (RawWord Bool) β]

/-- One machine, with both budgets indexed by the input value. -/
def Computes {κ : Type} [Fintype κ] {Q : Type} (M : TM Id κ (Option Bool) Q)
    (f : α → β) (t s : α → ℕ) : Prop :=
  Encoding.Computes f fun value (input output : RawWord Bool) =>
    M.ComputesWithin (input.toList.map some) (output.toList.map some)
      (t value) (s value)

theorem computableWithin_iff {f : α → β} {t s : α → ℕ} :
    TimeSpaceModel.tm.ComputableWithin f t s ↔
      ∃ (κ : Type) (_ : Fintype κ) (Q : Type) (_ : Finite Q)
        (M : TM Id κ (Option Bool) Q), Computes M f t s := by
  constructor
  · rintro ⟨R, ⟨κ, hκ, Q, hQ, M, rfl⟩, h⟩
    exact ⟨κ, hκ, Q, hQ, M, h⟩
  · rintro ⟨κ, hκ, Q, hQ, M, h⟩
    exact ⟨_, ⟨κ, hκ, Q, hQ, M, rfl⟩, h⟩

theorem Computes.mono {κ : Type} [Fintype κ] {Q : Type} {M : TM Id κ (Option Bool) Q}
    {f : α → β} {t s t' s' : α → ℕ} (h : Computes M f t s)
    (ht : ∀ a, t a ≤ t' a) (hs : ∀ a, s a ≤ s' a) : Computes M f t' s' :=
  Encoding.Computes.mono h (fun hc => hc.mono (ht _) (hs _))

theorem Computes.computableWithin {κ : Type} [Fintype κ] {Q : Type} [Finite Q]
    {M : TM Id κ (Option Bool) Q} {f : α → β} {t s : α → ℕ}
    (h : Computes M f t s) : TimeSpaceModel.tm.ComputableWithin f t s :=
  computableWithin_iff.mpr ⟨κ, inferInstance, Q, inferInstance, M, h⟩

end InputBudgets

end Complexity.TM
