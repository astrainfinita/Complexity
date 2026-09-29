/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Resources.Basic
public import Complexity.Encoding.BitList
public import Complexity.Models.TuringMachine.Deterministic

/-!
# Time and space complexity on multi-tape Turing machines

Functions use bit-string encodings. External bits occupy `some b` cells and
`none` is blank. Time counts transitions; space counts visited work cells and
excludes the read-only input and append-only output.

`ComputableInTimeAndSpace` requires one fixed machine with finite control for
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

/-- A single finite-control machine computes the function within both pointwise
bounds. The number of work tapes and the machine do not depend on the input. -/
def ComputableInTimeAndSpace (f : α → β) (t s : ℕ → ℕ) : Prop :=
  ∃ (κ : Type) (_ : Fintype κ) (Q : Type) (_ : Finite Q) (M : TM Id κ (Option Bool) Q),
    Computes M f t s

/-- Compute a function within a pointwise time bound, without a space restriction. -/
def ComputableInTime (f : α → β) (t : ℕ → ℕ) : Prop :=
  ∃ s, ComputableInTimeAndSpace f t s

/-- Compute a function within a pointwise work-space bound, while still terminating
on every valid input. -/
def ComputableInSpace (f : α → β) (s : ℕ → ℕ) : Prop :=
  ∃ t, ComputableInTimeAndSpace f t s

namespace Computes

theorem mono {κ : Type*} [Fintype κ] {Q : Type*} {M : TM Id κ (Option Bool) Q}
    {f : α → β} {t s t' s' : ℕ → ℕ} (h : Computes M f t s)
    (ht : ∀ n, t n ≤ t' n) (hs : ∀ n, s n ≤ s' n) : Computes M f t' s' :=
  Complexity.Computes.mono h
    (fun h ht hs => Controller.computes_mono (Output := List Bool) h ht hs) ht hs

theorem computableInTimeAndSpace {κ : Type} [Fintype κ] {Q : Type} [Finite Q]
    {M : TM Id κ (Option Bool) Q} {f : α → β} {t s : ℕ → ℕ}
    (h : Computes M f t s) : ComputableInTimeAndSpace f t s :=
  ⟨κ, inferInstance, Q, inferInstance, M, h⟩

end Computes

namespace ComputableInTimeAndSpace

theorem mono {f : α → β} {t s t' s' : ℕ → ℕ}
    (h : ComputableInTimeAndSpace f t s) (ht : ∀ n, t n ≤ t' n)
    (hs : ∀ n, s n ≤ s' n) : ComputableInTimeAndSpace f t' s' := by
  obtain ⟨κ, hκ, Q, hQ, M, hM⟩ := h
  exact ⟨κ, hκ, Q, hQ, M, hM.mono ht hs⟩

theorem computableInTime {f : α → β} {t s : ℕ → ℕ}
    (h : ComputableInTimeAndSpace f t s) :
    ComputableInTime f t := ⟨s, h⟩

theorem computableInSpace {f : α → β} {t s : ℕ → ℕ}
    (h : ComputableInTimeAndSpace f t s) :
    ComputableInSpace f s := ⟨t, h⟩

end ComputableInTimeAndSpace

namespace ComputableInTime

theorem mono {f : α → β} {t t' : ℕ → ℕ} (h : ComputableInTime f t)
    (ht : ∀ n, t n ≤ t' n) : ComputableInTime f t' := by
  obtain ⟨s, hs⟩ := h
  exact ⟨s, hs.mono ht (fun _ => le_rfl)⟩

end ComputableInTime

namespace ComputableInSpace

theorem mono {f : α → β} {s s' : ℕ → ℕ} (h : ComputableInSpace f s)
    (hs : ∀ n, s n ≤ s' n) : ComputableInSpace f s' := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t, ht.mono (fun _ => le_rfl) hs⟩

end ComputableInSpace

end Complexity.TM
