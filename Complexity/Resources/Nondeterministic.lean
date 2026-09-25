/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Encoding.BitList
public import Complexity.Models.TuringMachine.Nondeterministic

/-!
# Resource bounds for nondeterministic decisions

A single binary-choice machine handles every valid input code. Every branch must
halt with exactly one Boolean output; a predicate holds exactly when some branch
outputs `true`. Time and work-space bounds apply to every branch, not merely to
an accepting witness. The space-only specification still requires termination.

Raw bit strings occupy `some b` input cells, and `none` is blank. Bounds use the
length of the actual input code; invalid codes impose no obligations.
-/

@[expose] public section

namespace Complexity.NTM

variable {α : Type*} [Encoding (List Bool) α]
variable {κ : Type*} {Q : Type*} {M : NTM κ (Option Bool) Q}
variable {p q : α → Prop} {t s t' s' : ℕ → ℕ}

/-- Decide a predicate by existential acceptance, with Boolean output and
termination on every branch of every valid input. -/
def Decides (M : NTM κ (Option Bool) Q) (p : α → Prop) : Prop :=
  ∀ (xs : List Bool) (a : α), a ∈ decode α xs →
    M.Terminates (xs.map some) ∧
    M.BooleanOutput (xs.map some) ∧
    (M.Accepts (xs.map some) ↔ p a)

/-- Decide a predicate within a pointwise bound on every branch's running time. -/
def DecidesInTime (M : NTM κ (Option Bool) Q) (p : α → Prop) (t : ℕ → ℕ) : Prop :=
  Decides M p ∧ ∀ (xs : List Bool) (a : α), a ∈ decode α xs →
    M.UsesTime (xs.map some) (t xs.length)

/-- Decide a predicate within a pointwise work-space bound, halting on every branch. -/
def DecidesInSpace [Fintype κ] (M : NTM κ (Option Bool) Q) (p : α → Prop) (s : ℕ → ℕ) : Prop :=
  Decides M p ∧ ∀ (xs : List Bool) (a : α), a ∈ decode α xs →
    M.UsesSpace (xs.map some) (s xs.length)

/-- One machine decides the predicate within both pointwise resource bounds. -/
def DecidesInTimeAndSpace [Fintype κ] (M : NTM κ (Option Bool) Q) (p : α → Prop)
    (t s : ℕ → ℕ) : Prop :=
  DecidesInTime M p t ∧
    ∀ (xs : List Bool) (a : α), a ∈ decode α xs →
      M.UsesSpace (xs.map some) (s xs.length)

/-- A fixed finite-control binary-choice machine decides the predicate in the
given time, on every valid input encoding. -/
def DecidableInTime (p : α → Prop) (t : ℕ → ℕ) : Prop :=
  ∃ (κ : Type) (_ : Fintype κ) (Q : Type) (_ : Finite Q) (M : NTM κ (Option Bool) Q),
    DecidesInTime M p t

/-- Some fixed finite-control binary-choice machine decides the predicate in
the given work space, with every branch terminating. -/
def DecidableInSpace (p : α → Prop) (s : ℕ → ℕ) : Prop :=
  ∃ (κ : Type) (_ : Fintype κ) (Q : Type) (_ : Finite Q) (M : NTM κ (Option Bool) Q),
    DecidesInSpace M p s

/-- One fixed finite-control binary-choice machine meets both resource bounds. -/
def DecidableInTimeAndSpace (p : α → Prop) (t s : ℕ → ℕ) : Prop :=
  ∃ (κ : Type) (_ : Fintype κ) (Q : Type) (_ : Finite Q) (M : NTM κ (Option Bool) Q),
    DecidesInTimeAndSpace M p t s

theorem Decides.congr (h : Decides M p) (hp : ∀ a, p a ↔ q a) : Decides M q := by
  intro xs a ha
  obtain ⟨ht, hb, h⟩ := h xs a ha
  exact ⟨ht, hb, h.trans (hp a)⟩

namespace DecidesInTime

theorem decides (h : DecidesInTime M p t) : Decides M p := h.1

theorem mono (h : DecidesInTime M p t) (ht : ∀ n, t n ≤ t' n) :
    DecidesInTime M p t' :=
  ⟨h.1, fun xs a ha => (h.2 xs a ha).mono (ht xs.length)⟩

theorem congr (h : DecidesInTime M p t) (hp : ∀ a, p a ↔ q a) :
    DecidesInTime M q t := ⟨h.1.congr hp, h.2⟩

theorem decidableInTime {κ : Type} [Finite κ] {Q : Type} [Finite Q] {M : NTM κ (Option Bool) Q}
    (h : DecidesInTime M p t) : DecidableInTime p t := by
  let := Fintype.ofFinite κ
  exact ⟨κ, inferInstance, Q, inferInstance, M, h⟩

end DecidesInTime

namespace DecidesInSpace

variable [Fintype κ]

theorem decides (h : DecidesInSpace M p s) : Decides M p := h.1

theorem mono (h : DecidesInSpace M p s) (hs : ∀ n, s n ≤ s' n) :
    DecidesInSpace M p s' :=
  ⟨h.1, fun xs a ha => (h.2 xs a ha).mono (hs xs.length)⟩

theorem congr (h : DecidesInSpace M p s) (hp : ∀ a, p a ↔ q a) :
    DecidesInSpace M q s := ⟨h.1.congr hp, h.2⟩

theorem decidableInSpace {κ : Type} [Fintype κ] {Q : Type} [Finite Q] {M : NTM κ (Option Bool) Q}
    (h : DecidesInSpace M p s) : DecidableInSpace p s :=
  ⟨κ, inferInstance, Q, inferInstance, M, h⟩

end DecidesInSpace

namespace DecidesInTimeAndSpace

variable [Fintype κ]

theorem decidesInTime (h : DecidesInTimeAndSpace M p t s) : DecidesInTime M p t := h.1

theorem decidesInSpace (h : DecidesInTimeAndSpace M p t s) : DecidesInSpace M p s :=
  ⟨h.1.1, h.2⟩

theorem decides (h : DecidesInTimeAndSpace M p t s) : Decides M p := h.1.1

theorem mono (h : DecidesInTimeAndSpace M p t s)
    (ht : ∀ n, t n ≤ t' n) (hs : ∀ n, s n ≤ s' n) :
    DecidesInTimeAndSpace M p t' s' :=
  ⟨h.1.mono ht, fun xs a ha => (h.2 xs a ha).mono (hs xs.length)⟩

theorem congr (h : DecidesInTimeAndSpace M p t s) (hp : ∀ a, p a ↔ q a) :
    DecidesInTimeAndSpace M q t s := ⟨h.1.congr hp, h.2⟩

theorem decidableInTimeAndSpace {κ : Type} [Fintype κ] {Q : Type} [Finite Q]
    {M : NTM κ (Option Bool) Q}
    (h : DecidesInTimeAndSpace M p t s) : DecidableInTimeAndSpace p t s :=
  ⟨κ, inferInstance, Q, inferInstance, M, h⟩

end DecidesInTimeAndSpace

namespace DecidableInTime

theorem mono (h : DecidableInTime p t) (ht : ∀ n, t n ≤ t' n) :
    DecidableInTime p t' := by
  obtain ⟨κ, hκ, Q, hQ, M, h⟩ := h
  exact ⟨κ, hκ, Q, hQ, M, h.mono ht⟩

theorem congr (h : DecidableInTime p t) (hp : ∀ a, p a ↔ q a) :
    DecidableInTime q t := by
  obtain ⟨κ, hκ, Q, hQ, M, h⟩ := h
  exact ⟨κ, hκ, Q, hQ, M, h.congr hp⟩

end DecidableInTime

namespace DecidableInSpace

theorem mono (h : DecidableInSpace p s) (hs : ∀ n, s n ≤ s' n) :
    DecidableInSpace p s' := by
  obtain ⟨κ, hκ, Q, hQ, M, h⟩ := h
  exact ⟨κ, hκ, Q, hQ, M, h.mono hs⟩

theorem congr (h : DecidableInSpace p s) (hp : ∀ a, p a ↔ q a) :
    DecidableInSpace q s := by
  obtain ⟨κ, hκ, Q, hQ, M, h⟩ := h
  exact ⟨κ, hκ, Q, hQ, M, h.congr hp⟩

end DecidableInSpace

namespace DecidableInTimeAndSpace

theorem mono (h : DecidableInTimeAndSpace p t s)
    (ht : ∀ n, t n ≤ t' n) (hs : ∀ n, s n ≤ s' n) :
    DecidableInTimeAndSpace p t' s' := by
  obtain ⟨κ, hκ, Q, hQ, M, h⟩ := h
  exact ⟨κ, hκ, Q, hQ, M, h.mono ht hs⟩

theorem congr (h : DecidableInTimeAndSpace p t s) (hp : ∀ a, p a ↔ q a) :
    DecidableInTimeAndSpace q t s := by
  obtain ⟨κ, hκ, Q, hQ, M, h⟩ := h
  exact ⟨κ, hκ, Q, hQ, M, h.congr hp⟩

theorem decidableInTime (h : DecidableInTimeAndSpace p t s) : DecidableInTime p t := by
  obtain ⟨κ, hκ, Q, hQ, M, h⟩ := h
  exact ⟨κ, hκ, Q, hQ, M, h.decidesInTime⟩

theorem decidableInSpace (h : DecidableInTimeAndSpace p t s) : DecidableInSpace p s := by
  obtain ⟨κ, hκ, Q, hQ, M, h⟩ := h
  exact ⟨κ, hκ, Q, hQ, M, h.decidesInSpace⟩

end DecidableInTimeAndSpace

end Complexity.NTM
