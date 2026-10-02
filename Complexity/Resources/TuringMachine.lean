/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Resources.TimeSpaceModel
public import Complexity.Encoding.Bool
public import Complexity.Models.TuringMachine.Deterministic

/-!
# Time and space complexity on multi-tape Turing machines

Functions use bit-string encodings. External bits occupy `some b` cells and
`none` is blank. Time counts transitions; space counts visited work cells and
excludes the read-only input and append-only output.

`timeSpaceModel.ComputableInTimeAndSpace` requires one fixed machine with finite control for
all valid inputs. Its bounds are pointwise functions of the actual input length.
The time-only and space-only variants omit one bound, but still require termination.
-/

@[expose] public section

namespace Complexity.TM

theorem ComputesInTimeAndSpace.mono {κ : Type*} [Fintype κ] {Γ Q : Type*} [Inhabited Γ]
    {M : TM Id κ Γ Q} {xs ys : List Γ} {t s t' s' : ℕ}
    (h : M.ComputesInTimeAndSpace xs ys t s) (ht : t ≤ t') (hs : s ≤ s') :
    M.ComputesInTimeAndSpace xs ys t' s' :=
  Controller.computes_mono h ht hs

variable {α β : Type*} [Encoding (List Bool) α] [Encoding (List Bool) β]

/-- A bit-alphabet machine computes a function on all valid input encodings. -/
def Computes {κ : Type*} [Fintype κ] {Q : Type*} (M : TM Id κ (Option Bool) Q)
    (f : α → β) (t s : ℕ → ℕ) : Prop :=
  Complexity.Computes
    (fun xs ys time space =>
      M.computes (Output := List Bool)
        (Config := Cfg κ (Option Bool) Q ((xs.map some).toArray))
        Controller.History.length Controller.History.space xs ys time space)
    List.length f t s

/-- The common bit-string execution recovers the original encoded machine specification. -/
theorem computes_iff {κ : Type*} [Fintype κ] {Q : Type*} {M : TM Id κ (Option Bool) Q}
    {f : α → β} {t s : ℕ → ℕ} :
    Computes M f t s ↔
      Complexity.Computes
        (fun xs ys => M.ComputesInTimeAndSpace (xs.map some) (ys.map some))
        List.length f t s := Iff.rfl

/-- Finite Turing machines on bit strings, with transition time and visited
work-cell space. Each behavior is realized by one machine for all inputs. -/
def timeSpaceModel : TimeSpaceModel Id (List Bool) where
  inputSize := List.length
  behaviors := {R | ∃ (κ : Type) (_ : Fintype κ) (Q : Type) (_ : Finite Q)
      (M : TM Id κ (Option Bool) Q),
      R = fun xs result => M.ComputesInTimeAndSpace (xs.map some) (result.run.map some)}
  budget_mono := by
    rintro R ⟨κ, hκ, Q, hQ, M, rfl⟩ x y t s t' s' h ht hs
    exact h.mono ht hs

/-- Recover the single finite machine realizing the abstract resource behavior. -/
theorem computableInTimeAndSpace_iff {f : α → β} {t s : ℕ → ℕ} :
    timeSpaceModel.ComputableInTimeAndSpace f t s ↔
      ∃ (κ : Type) (_ : Fintype κ) (Q : Type) (_ : Finite Q)
        (M : TM Id κ (Option Bool) Q), Computes M f t s := by
  constructor
  · rintro ⟨R, ⟨κ, hκ, Q, hQ, M, rfl⟩, h⟩
    exact ⟨κ, hκ, Q, hQ, M, h⟩
  · rintro ⟨κ, hκ, Q, hQ, M, h⟩
    exact ⟨_, ⟨κ, hκ, Q, hQ, M, rfl⟩, h⟩

namespace Computes

theorem mono {κ : Type*} [Fintype κ] {Q : Type*} {M : TM Id κ (Option Bool) Q}
    {f : α → β} {t s t' s' : ℕ → ℕ} (h : Computes M f t s)
    (ht : ∀ n, t n ≤ t' n) (hs : ∀ n, s n ≤ s' n) : Computes M f t' s' :=
  Complexity.Computes.mono h
    (fun h ht hs => Controller.computes_mono (Output := List Bool) h ht hs) ht hs

theorem computableInTimeAndSpace {κ : Type} [Fintype κ] {Q : Type} [Finite Q]
    {M : TM Id κ (Option Bool) Q} {f : α → β} {t s : ℕ → ℕ}
    (h : Computes M f t s) : timeSpaceModel.ComputableInTimeAndSpace f t s :=
  computableInTimeAndSpace_iff.mpr ⟨κ, inferInstance, Q, inferInstance, M, h⟩

end Computes

end Complexity.TM
