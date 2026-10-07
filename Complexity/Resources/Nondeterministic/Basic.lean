/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Resources.TimeSpaceModel.Nondeterministic
public import Complexity.Encoding.RawWord
public import Mathlib.Data.Set.Finite.List
public import Complexity.Models.TuringMachine.Nondeterministic.Basic

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

section Boolean

variable {κ Q : Type*} {M : NTM κ (Option Bool) Q} {xs : RawWord Bool}

/-- Every halted branch returns exactly one encoded Boolean, including rejecting branches. -/
def BooleanOutput (M : NTM κ (Option Bool) Q) (xs : RawWord Bool) : Prop :=
  ∀ ys, M.Produces (xs.toList.map some) ys → ∃ b : Bool, ys = ⌜b⌝₂.toList.map some

/-- An input is accepted when some finite branch halts with the encoded value `true`. -/
def Accepts (M : NTM κ (Option Bool) Q) (xs : RawWord Bool) : Prop :=
  M.Produces (xs.toList.map some) (⌜true⌝₂.toList.map some)

theorem accepts_iff_of_usesTime {t : ℕ} (h : M.UsesTime (xs.toList.map some) t) :
    M.Accepts xs ↔ ∃ c ∈ M.runWith
      (TM.Cfg κ (Option Bool) Q (xs.toList.map some).toArray) Multiset (xs.toList.map some) t,
        c.output = (⌜true⌝₂.toList.map some).toArray :=
  produces_iff_of_usesTime h

theorem booleanOutput_iff_of_usesTime {t : ℕ} (h : M.UsesTime (xs.toList.map some) t) :
    M.BooleanOutput xs ↔ ∀ c ∈ M.runWith
      (TM.Cfg κ (Option Bool) Q (xs.toList.map some).toArray) Multiset (xs.toList.map some) t,
        ∃ b : Bool, c.output = (⌜b⌝₂.toList.map some).toArray := by
  simp only [BooleanOutput, produces_iff_of_usesTime h, ← Array.toList_inj,
    forall_exists_index, and_imp]
  rw [forall_comm]
  simp only [forall_comm (α := List (Option Bool)), forall_eq']

end Boolean

variable {α : Type*} [Encoding (RawWord Bool) α]
variable {κ : Type*} {Q : Type*} {M : NTM κ (Option Bool) Q}
variable {p q : α → Prop} {t s t' s' : ℕ → ℕ}

/-- Decide a predicate by existential acceptance, with Boolean output and
termination on every branch of every valid input. -/
def Decides (M : NTM κ (Option Bool) Q) (p : α → Prop) : Prop :=
  ∀ (xs : RawWord Bool) (a : α), a ∈ decode α xs →
    M.Terminates (xs.toList.map some) ∧ M.BooleanOutput xs ∧ (M.Accepts xs ↔ p a)

/-- Decide a predicate within a pointwise bound on every branch's running time. -/
def DecidesInTime (M : NTM κ (Option Bool) Q) (p : α → Prop) (t : ℕ → ℕ) : Prop :=
  ∀ (xs : RawWord Bool) (a : α), a ∈ decode α xs →
    M.UsesTime (xs.toList.map some) (t xs.length) ∧ M.BooleanOutput xs ∧ (M.Accepts xs ↔ p a)

/-- Decide a predicate within a pointwise work-space bound, halting on every branch. -/
def DecidesInSpace [Fintype κ] (M : NTM κ (Option Bool) Q) (p : α → Prop) (s : ℕ → ℕ) : Prop :=
  Decides M p ∧ ∀ (xs : RawWord Bool) (a : α), a ∈ decode α xs →
    M.UsesSpace (xs.toList.map some) (s xs.length)

/-- One machine decides the predicate within both pointwise resource bounds. -/
def DecidesInTimeAndSpace [Fintype κ] (M : NTM κ (Option Bool) Q) (p : α → Prop)
    (t s : ℕ → ℕ) : Prop :=
  ∀ (xs : RawWord Bool) (a : α), a ∈ decode α xs →
    M.UsesTime (xs.toList.map some) (t xs.length) ∧ M.UsesSpace (xs.toList.map some) (s xs.length) ∧
      M.BooleanOutput xs ∧ (M.Accepts xs ↔ p a)

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
    (∃ ys : Multiset (RawWord Bool),
      ys.map (fun y => (y.toList.map some).toArray) = cs.map output ∧
      (∀ y ∈ ys, (decode Bool y).Dom) ∧
      ((∃ y ∈ ys, true ∈ decode Bool y) ↔ p)) ↔
    (∀ c ∈ cs, ∃ b : Bool, output c = (⌜b⌝₂.toList.map some).toArray) ∧
      ((∃ c ∈ cs, output c = (⌜true⌝₂.toList.map some).toArray) ↔ p) := by
  have hinj : Function.Injective (fun y : RawWord Bool ↦ (y.toList.map some).toArray) :=
    fun _ _ h ↦ RawWord.ext <| (List.map_injective_iff.2 (Option.some_injective _)) (Array.mk.inj h)
  rw [← Multiset.forall_mem_map_iff (f := output) (p := fun z =>
    ∃ b : Bool, z = (⌜b⌝₂.toList.map some).toArray)]
  simp_rw [← Multiset.mem_map (f := output), UniqueEncoding.dom_decode_iff,
    UniqueEncoding.mem_decode_iff]
  constructor
  · rintro ⟨ys, he, hv, ha⟩
    rw [← he]
    simpa only [Multiset.forall_mem_map_iff, hinj.eq_iff,
      Multiset.mem_map_of_injective hinj, exists_eq_right, eq_comm] using And.intro hv ha
  · rintro ⟨hv, ha⟩
    let : CanLift (Array (Option Bool)) (RawWord Bool)
        (fun y => (y.toList.map some).toArray)
        (fun z => ∃ b : Bool, z = (⌜b⌝₂.toList.map some).toArray) :=
      ⟨fun _ ⟨b, h⟩ => ⟨⌜b⌝₂, h.symm⟩⟩
    obtain ⟨ys, he⟩ := CanLift.prf (β := Multiset (RawWord Bool)) (x := cs.map output) hv
    refine ⟨ys, he, ?_⟩
    rw [← he] at hv ha
    simpa only [Multiset.forall_mem_map_iff, hinj.eq_iff,
      Multiset.mem_map_of_injective hinj, exists_eq_right, eq_comm] using And.intro hv ha

/-- Finite binary-choice Turing machines, retaining all branch outputs and their
multiplicities. Resource bounds cover every branch, including rejecting branches. -/
def _root_.Complexity.TimeSpaceModel.ntm : TimeSpaceModel Multiset (RawWord Bool) where
  inputSize := RawWord.length
  behaviors := {R | ∃ (κ : Type) (_ : Fintype κ) (Q : Type) (_ : Finite Q)
      (M : NTM κ (Option Bool) Q), R = fun xs ys t s =>
        M.UsesTime (xs.toList.map some) t ∧ M.UsesSpace (xs.toList.map some) s ∧
        ys.map (fun y => (y.toList.map some).toArray) =
          (M.runWith (TM.Cfg κ (Option Bool) Q (xs.toList.map some).toArray)
            Multiset (xs.toList.map some) t).map (·.output)}
  budget_mono := by
    rintro R ⟨κ, hκ, Q, hQ, M, rfl⟩ xs ys t s t' s' ⟨ht, hs, ho⟩ htt hss
    exact ⟨ht.mono htt, hs.mono hss, by rw [runWith_eq_of_usesTime ht htt]; exact ho⟩

/-- The abstract specification is exactly the finite-machine decision
specification, with no branches discarded or extra output codes accepted. -/
theorem nDecidableInTimeAndSpace_iff :
    TimeSpaceModel.ntm.NDecidableInTimeAndSpace p t s ↔
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
  have ht : ∀ xs : List Bool, (decode α (RawWord.ofList xs)).Dom →
      ∃ n, M.UsesTime (xs.map some) n :=
    fun xs hd => (h.decides (RawWord.ofList xs) _ (Part.get_mem hd)).1
  choose! f hf using ht
  refine ⟨fun n => (List.finite_length_eq Bool n).toFinset.sup f, fun xs a ha => ?_⟩
  exact ⟨(hf xs.toList ha.fst).mono (Finset.le_sup (by simp)), h.2 xs a ha, (h.decides xs a ha).2⟩

theorem nDecidableInTime_iff :
    TimeSpaceModel.ntm.NDecidableInTime p t ↔
      ∃ (κ : Type) (_ : Fintype κ) (Q : Type) (_ : Finite Q)
        (M : NTM κ (Option Bool) Q), DecidesInTime M p t := by
  constructor
  · rintro ⟨s, h⟩
    obtain ⟨κ, hκ, Q, hQ, M, h⟩ := nDecidableInTimeAndSpace_iff.mp h
    exact ⟨κ, hκ, Q, hQ, M, h.decidesInTime⟩
  · rintro ⟨κ, hκ, Q, hQ, M, h⟩
    obtain ⟨s, hs⟩ := h.exists_space
    exact ⟨s, nDecidableInTimeAndSpace_iff.mpr ⟨κ, hκ, Q, hQ, M, hs⟩⟩

theorem nDecidableInSpace_iff :
    TimeSpaceModel.ntm.NDecidableInSpace p s ↔
      ∃ (κ : Type) (_ : Fintype κ) (Q : Type) (_ : Finite Q)
        (M : NTM κ (Option Bool) Q), DecidesInSpace M p s := by
  constructor
  · rintro ⟨t, h⟩
    obtain ⟨κ, hκ, Q, hQ, M, h⟩ := nDecidableInTimeAndSpace_iff.mp h
    exact ⟨κ, hκ, Q, hQ, M, h.decidesInSpace⟩
  · rintro ⟨κ, hκ, Q, hQ, M, h⟩
    obtain ⟨t, ht⟩ := h.exists_time
    exact ⟨t, nDecidableInTimeAndSpace_iff.mpr ⟨κ, hκ, Q, hQ, M, ht⟩⟩

theorem DecidesInTime.decidableInTime {κ : Type} [Finite κ] {Q : Type} [Finite Q]
    {M : NTM κ (Option Bool) Q} (h : DecidesInTime M p t) :
    TimeSpaceModel.ntm.NDecidableInTime p t := by
  let := Fintype.ofFinite κ
  exact nDecidableInTime_iff.mpr ⟨κ, inferInstance, Q, inferInstance, M, h⟩

theorem DecidesInSpace.decidableInSpace {κ : Type} [Fintype κ] {Q : Type} [Finite Q]
    {M : NTM κ (Option Bool) Q} (h : DecidesInSpace M p s) :
    TimeSpaceModel.ntm.NDecidableInSpace p s :=
  nDecidableInSpace_iff.mpr ⟨κ, inferInstance, Q, inferInstance, M, h⟩

theorem DecidesInTimeAndSpace.decidableInTimeAndSpace {κ : Type} [Fintype κ]
    {Q : Type} [Finite Q] {M : NTM κ (Option Bool) Q}
    (h : DecidesInTimeAndSpace M p t s) : TimeSpaceModel.ntm.NDecidableInTimeAndSpace p t s :=
  nDecidableInTimeAndSpace_iff.mpr ⟨κ, inferInstance, Q, inferInstance, M, h⟩

end Complexity.NTM
