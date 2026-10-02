/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Resources.TimeSpaceModel.Nondeterministic
public import Complexity.Encoding.BitList
public import Complexity.Encoding.Bool
public import Mathlib.Data.Set.Finite.List
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
  ∀ (xs : List Bool) (a : α), a ∈ decode α xs →
    M.UsesTime (xs.map some) (t xs.length) ∧ M.BooleanOutput (xs.map some) ∧
      (M.Accepts (xs.map some) ↔ p a)

/-- Decide a predicate within a pointwise work-space bound, halting on every branch. -/
def DecidesInSpace [Fintype κ] (M : NTM κ (Option Bool) Q) (p : α → Prop) (s : ℕ → ℕ) : Prop :=
  Decides M p ∧ ∀ (xs : List Bool) (a : α), a ∈ decode α xs →
    M.UsesSpace (xs.map some) (s xs.length)

/-- One machine decides the predicate within both pointwise resource bounds. -/
def DecidesInTimeAndSpace [Fintype κ] (M : NTM κ (Option Bool) Q) (p : α → Prop)
    (t s : ℕ → ℕ) : Prop :=
  ∀ (xs : List Bool) (a : α), a ∈ decode α xs →
    M.UsesTime (xs.map some) (t xs.length) ∧ M.UsesSpace (xs.map some) (s xs.length) ∧
      M.BooleanOutput (xs.map some) ∧ (M.Accepts (xs.map some) ↔ p a)

theorem Decides.congr (h : Decides M p) (hp : ∀ a, p a ↔ q a) : Decides M q :=
  funext (fun a => propext (hp a)) ▸ h

namespace DecidesInTime

theorem decides (h : DecidesInTime M p t) : Decides M p :=
  fun xs a ha => ⟨(h xs a ha).1.terminates, (h xs a ha).2⟩

theorem mono (h : DecidesInTime M p t) (ht : ∀ n, t n ≤ t' n) :
    DecidesInTime M p t' :=
  fun xs a ha => ⟨(h xs a ha).1.mono (ht xs.length), (h xs a ha).2⟩

theorem congr (h : DecidesInTime M p t) (hp : ∀ a, p a ↔ q a) :
    DecidesInTime M q t :=
  funext (fun a => propext (hp a)) ▸ h

end DecidesInTime

namespace DecidesInSpace

variable [Fintype κ]

theorem decides (h : DecidesInSpace M p s) : Decides M p := h.1

theorem mono (h : DecidesInSpace M p s) (hs : ∀ n, s n ≤ s' n) :
    DecidesInSpace M p s' :=
  ⟨h.1, fun xs a ha => (h.2 xs a ha).mono (hs xs.length)⟩

theorem congr (h : DecidesInSpace M p s) (hp : ∀ a, p a ↔ q a) :
    DecidesInSpace M q s := ⟨h.1.congr hp, h.2⟩

end DecidesInSpace

namespace DecidesInTimeAndSpace

variable [Fintype κ]

theorem decidesInTime (h : DecidesInTimeAndSpace M p t s) : DecidesInTime M p t :=
  fun xs a ha => ⟨(h xs a ha).1, (h xs a ha).2.2⟩

theorem decidesInSpace (h : DecidesInTimeAndSpace M p t s) : DecidesInSpace M p s :=
  ⟨h.decidesInTime.decides, fun xs a ha => (h xs a ha).2.1⟩

theorem decides (h : DecidesInTimeAndSpace M p t s) : Decides M p := h.decidesInTime.decides

theorem mono (h : DecidesInTimeAndSpace M p t s)
    (ht : ∀ n, t n ≤ t' n) (hs : ∀ n, s n ≤ s' n) :
    DecidesInTimeAndSpace M p t' s' :=
  fun xs a ha => ⟨(h xs a ha).1.mono (ht xs.length),
    (h xs a ha).2.1.mono (hs xs.length), (h xs a ha).2.2⟩

theorem congr (h : DecidesInTimeAndSpace M p t s) (hp : ∀ a, p a ↔ q a) :
    DecidesInTimeAndSpace M q t s :=
  funext (fun a => propext (hp a)) ▸ h

end DecidesInTimeAndSpace

private theorem outputs_iff {C : Type*} (cs : Multiset C) (output : C → Array (Option Bool))
    (p : Prop) :
    (∃ ys : Multiset (List Bool),
      ys.map (fun y => (y.map some).toArray) = cs.map output ∧
      (∀ y ∈ ys, (decode Bool y).Dom) ∧
      ((∃ y ∈ ys, true ∈ decode Bool y) ↔ p)) ↔
    (∀ c ∈ cs, ∃ b : Bool, output c = #[some b]) ∧
      ((∃ c ∈ cs, output c = #[some true]) ↔ p) := by
  have hmem {ys : Multiset (List Bool)}
      (he : ys.map (fun y => (y.map some).toArray) = cs.map output) :
      (∃ y ∈ ys, true ∈ decode Bool y) ↔ ∃ c ∈ cs, output c = #[some true] := by
    simpa [mem_decode_bool_bits] using congrArg (#[some true] ∈ ·) he
  constructor
  · rintro ⟨ys, he, hv, ha⟩
    have hv' : ∀ z ∈ ys.map (fun y => (y.map some).toArray),
        ∃ b : Bool, z = #[some b] := by
      simpa [Part.dom_iff_mem] using hv
    rw [he] at hv'
    exact ⟨by simpa using hv', (hmem he).symm.trans ha⟩
  · rintro ⟨hv, ha⟩
    let : CanLift (Array (Option Bool)) Bool (fun b => #[some b])
        (fun y => ∃ b, y = #[some b]) := ⟨fun _ ⟨b, h⟩ => ⟨b, h.symm⟩⟩
    obtain ⟨bs, he⟩ := CanLift.prf (β := Multiset Bool) (x := cs.map output) (by simpa using hv)
    have he' : (bs.map (fun b => [b])).map (fun y => (y.map some).toArray) =
        cs.map output := by simpa using he
    refine ⟨_, he', ?_, (hmem he').trans ha⟩
    simp only [Multiset.forall_mem_map_iff]
    simp [Part.dom_iff_mem]

/-- Finite binary-choice Turing machines, retaining all branch outputs and their
multiplicities. Resource bounds cover every branch, including rejecting branches. -/
def timeSpaceModel : TimeSpaceModel Multiset (List Bool) where
  inputSize := List.length
  behaviors := {R | ∃ (κ : Type) (_ : Fintype κ) (Q : Type) (_ : Finite Q)
      (M : NTM κ (Option Bool) Q), R = fun xs ys t s =>
        M.UsesTime (xs.map some) t ∧ M.UsesSpace (xs.map some) s ∧
        ys.map (fun y => (y.map some).toArray) =
          (M.runWith (TM.Cfg κ (Option Bool) Q (xs.map some).toArray)
            Multiset (xs.map some) t).map (·.output)}
  budget_mono := by
    rintro R ⟨κ, hκ, Q, hQ, M, rfl⟩ xs ys t s t' s' ⟨ht, hs, ho⟩ htt hss
    exact ⟨ht.mono htt, hs.mono hss, by rw [runWith_eq_of_usesTime ht htt]; exact ho⟩

/-- The abstract specification is exactly the original finite-machine decision
specification, with no branches discarded or extra output codes accepted. -/
theorem ndecidableInTimeAndSpace_iff :
    timeSpaceModel.NDecidableInTimeAndSpace p t s ↔
      ∃ (κ : Type) (_ : Fintype κ) (Q : Type) (_ : Finite Q)
        (M : NTM κ (Option Bool) Q), DecidesInTimeAndSpace M p t s := by
  constructor
  · rintro ⟨R, ⟨κ, hκ, Q, hQ, M, rfl⟩, h⟩
    simp only [and_assoc, exists_and_left, outputs_iff] at h
    refine ⟨κ, hκ, Q, hQ, M, fun xs a ha => ?_⟩
    obtain ⟨ht, hs, hb, hp⟩ := h xs a ha
    exact ⟨ht, hs, (booleanOutput_iff_of_usesTime ht).mpr hb,
      (accepts_iff_of_usesTime ht).trans hp⟩
  · rintro ⟨κ, hκ, Q, hQ, M, h⟩
    refine ⟨_, ⟨κ, hκ, Q, hQ, M, rfl⟩, fun xs a ha => ?_⟩
    simp only [and_assoc, exists_and_left, outputs_iff]
    obtain ⟨ht, hs, hb, hp⟩ := h xs a ha
    exact ⟨ht, hs, (booleanOutput_iff_of_usesTime ht).mp hb,
      (accepts_iff_of_usesTime ht).symm.trans hp⟩

/-- A time bound also bounds the visited work cells on every branch. -/
theorem DecidesInTime.exists_space [Fintype κ] (h : DecidesInTime M p t) :
    ∃ s, DecidesInTimeAndSpace M p t s :=
  ⟨fun n => Fintype.card κ * (t n + 1),
    fun xs a ha => ⟨(h xs a ha).1, (h xs a ha).1.usesSpace, (h xs a ha).2⟩⟩

/-- Finitely many bit strings have a given length, so per-input termination
admits a time bound depending only on input length. -/
theorem DecidesInSpace.exists_time [Fintype κ] (h : DecidesInSpace M p s) :
    ∃ t, DecidesInTimeAndSpace M p t s := by
  classical
  have ht : ∀ xs : List Bool, (decode α xs).Dom → ∃ n, M.UsesTime (xs.map some) n :=
    fun xs hd => (h.decides xs _ (Part.get_mem hd)).1
  choose! f hf using ht
  refine ⟨fun n => (List.finite_length_eq Bool n).toFinset.sup f, fun xs a ha => ?_⟩
  exact ⟨(hf xs ha.fst).mono (Finset.le_sup (by simp)), h.2 xs a ha, (h.decides xs a ha).2⟩

theorem ndecidableInTime_iff :
    timeSpaceModel.NDecidableInTime p t ↔
      ∃ (κ : Type) (_ : Fintype κ) (Q : Type) (_ : Finite Q)
        (M : NTM κ (Option Bool) Q), DecidesInTime M p t := by
  constructor
  · rintro ⟨s, h⟩
    obtain ⟨κ, hκ, Q, hQ, M, h⟩ := ndecidableInTimeAndSpace_iff.mp h
    exact ⟨κ, hκ, Q, hQ, M, h.decidesInTime⟩
  · rintro ⟨κ, hκ, Q, hQ, M, h⟩
    obtain ⟨s, hs⟩ := h.exists_space
    exact ⟨s, ndecidableInTimeAndSpace_iff.mpr ⟨κ, hκ, Q, hQ, M, hs⟩⟩

theorem ndecidableInSpace_iff :
    timeSpaceModel.NDecidableInSpace p s ↔
      ∃ (κ : Type) (_ : Fintype κ) (Q : Type) (_ : Finite Q)
        (M : NTM κ (Option Bool) Q), DecidesInSpace M p s := by
  constructor
  · rintro ⟨t, h⟩
    obtain ⟨κ, hκ, Q, hQ, M, h⟩ := ndecidableInTimeAndSpace_iff.mp h
    exact ⟨κ, hκ, Q, hQ, M, h.decidesInSpace⟩
  · rintro ⟨κ, hκ, Q, hQ, M, h⟩
    obtain ⟨t, ht⟩ := h.exists_time
    exact ⟨t, ndecidableInTimeAndSpace_iff.mpr ⟨κ, hκ, Q, hQ, M, ht⟩⟩

theorem DecidesInTime.decidableInTime {κ : Type} [Finite κ] {Q : Type} [Finite Q]
    {M : NTM κ (Option Bool) Q} (h : DecidesInTime M p t) :
    timeSpaceModel.NDecidableInTime p t := by
  let := Fintype.ofFinite κ
  exact ndecidableInTime_iff.mpr ⟨κ, inferInstance, Q, inferInstance, M, h⟩

theorem DecidesInSpace.decidableInSpace {κ : Type} [Fintype κ] {Q : Type} [Finite Q]
    {M : NTM κ (Option Bool) Q} (h : DecidesInSpace M p s) :
    timeSpaceModel.NDecidableInSpace p s :=
  ndecidableInSpace_iff.mpr ⟨κ, inferInstance, Q, inferInstance, M, h⟩

theorem DecidesInTimeAndSpace.decidableInTimeAndSpace {κ : Type} [Fintype κ]
    {Q : Type} [Finite Q] {M : NTM κ (Option Bool) Q}
    (h : DecidesInTimeAndSpace M p t s) : timeSpaceModel.NDecidableInTimeAndSpace p t s :=
  ndecidableInTimeAndSpace_iff.mpr ⟨κ, inferInstance, Q, inferInstance, M, h⟩

end Complexity.NTM
