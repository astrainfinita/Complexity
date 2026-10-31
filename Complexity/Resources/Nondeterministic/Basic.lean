/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Resources.TimeSpaceModel.Nondeterministic
public import Complexity.Encoding.RawWord
public import Complexity.Models.TuringMachine.Nondeterministic.Basic

/-!
# Resource bounds for nondeterministic decisions

A single binary-choice machine handles every valid input code. Every branch must
halt with exactly one Boolean output; a predicate holds exactly when some branch
outputs `true`. Time and work-space bounds apply to every branch, not merely to
an accepting witness. The space-only specification still requires termination.

Raw bit strings occupy `some b` input cells, and `none` is blank. Resource budgets depend
on the decoded value and uniformly cover every representation of that value.
Invalid codes impose no obligations.
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
    M.Accepts xs ↔ ∃ c ∈ M.runWith Multiset (xs.toList.map some) t,
        c.2.output = (⌜true⌝₂.toList.map some).toArray :=
  produces_iff_of_usesTime h

theorem booleanOutput_iff_of_usesTime {t : ℕ} (h : M.UsesTime (xs.toList.map some) t) :
    M.BooleanOutput xs ↔ ∀ c ∈ M.runWith Multiset (xs.toList.map some) t,
        ∃ b : Bool, c.2.output = (⌜b⌝₂.toList.map some).toArray := by
  simp only [BooleanOutput, produces_iff_of_usesTime h, ← Array.toList_inj,
    forall_exists_index, and_imp]
  rw [forall_comm]
  simp only [forall_comm (α := List (Option Bool)), forall_eq']

end Boolean

theorem exists_boolean_outputs_iff {C : Type*} (cs : Multiset C) (output : C → Array (Option Bool))
    (p : Prop) :
    (∃ ys : Multiset (RawWord Bool),
      ys.map (fun y => (y.toList.map some).toArray) = cs.map output ∧
      (∀ y ∈ ys, (decode Bool y).Dom) ∧
      ((∃ y ∈ ys, true ∈ decode Bool y) ↔ p)) ↔
    (∀ c ∈ cs, ∃ b : Bool, output c = (⌜b⌝₂.toList.map some).toArray) ∧
      ((∃ c ∈ cs, output c = (⌜true⌝₂.toList.map some).toArray) ↔ p) := by
  have hinj : Function.Injective (fun y : RawWord Bool ↦ (y.toList.map some).toArray) :=
    fun _ _ h ↦ RawWord.ext <| (List.map_injective_iff.2 (Option.some_injective _)) (Array.mk.inj h)
  rw [← Multiset.forall_mem_map_iff (p := fun z =>
    ∃ b : Bool, z = (⌜b⌝₂.toList.map some).toArray)]
  simp_rw [← Multiset.mem_map, UniqueEncoding.dom_decode_iff,
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
    obtain ⟨ys, he⟩ := CanLift.prf (β := Multiset (RawWord Bool)) (cs.map output) hv
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
          (M.runWith Multiset (xs.toList.map some) t).map (·.2.output)}
  budget_mono := by
    rintro R ⟨κ, hκ, Q, hQ, M, rfl⟩ xs ys t s t' s' ⟨ht, hs, ho⟩ htt hss
    exact ⟨ht.mono htt, hs.mono hss, by rw [runWith_eq_of_usesTime ht htt]; exact ho⟩

section InputBudgets

variable {α : Type*} [Encoding (RawWord Bool) α]
  {κ Q : Type*} {M : NTM κ (Option Bool) Q} {p : α → Prop} {t s : α → ℕ}

/-- Every branch obeys the same value-indexed budgets on every legal input code. -/
def DecidesWithin [Fintype κ] (M : NTM κ (Option Bool) Q) (p : α → Prop)
    (t s : α → ℕ) : Prop :=
  ∀ r a, a ∈ decode α r → M.UsesTime (r.toList.map some) (t a) ∧
    M.UsesSpace (r.toList.map some) (s a) ∧
    M.BooleanOutput r ∧ (M.Accepts r ↔ p a)

theorem DecidesWithin.mono [Fintype κ]
    (h : DecidesWithin M p t s) {t' s' : α → ℕ}
    (ht : ∀ a, t a ≤ t' a) (hs : ∀ a, s a ≤ s' a) :
    DecidesWithin M p t' s' :=
  fun r a ha => ⟨(h r a ha).1.mono (ht a), (h r a ha).2.1.mono (hs a), (h r a ha).2.2⟩

theorem nDecidableWithin_iff :
    TimeSpaceModel.ntm.NDecidableWithin p t s ↔
      ∃ (κ : Type) (_ : Fintype κ) (Q : Type) (_ : Finite Q)
        (M : NTM κ (Option Bool) Q), DecidesWithin M p t s := by
  constructor
  · rintro ⟨R, ⟨κ, hκ, Q, hQ, M, rfl⟩, h⟩
    simp only [Encoding.NDecides, and_assoc, exists_and_left, exists_boolean_outputs_iff] at h
    refine ⟨κ, hκ, Q, hQ, M, fun r a ha => ?_⟩
    obtain ⟨ht, hs, hb, hp⟩ := h a r ha
    exact ⟨ht, hs, (booleanOutput_iff_of_usesTime ht).mpr hb,
      (accepts_iff_of_usesTime ht).trans hp⟩
  · rintro ⟨κ, hκ, Q, hQ, M, h⟩
    refine ⟨_, ⟨κ, hκ, Q, hQ, M, rfl⟩, fun a r ha => ?_⟩
    simp only [and_assoc, exists_and_left, exists_boolean_outputs_iff]
    obtain ⟨ht, hs, hb, hp⟩ := h r a ha
    exact ⟨ht, hs, (booleanOutput_iff_of_usesTime ht).mp hb,
      (accepts_iff_of_usesTime ht).symm.trans hp⟩

theorem DecidesWithin.nDecidableWithin {κ : Type} [Fintype κ]
    {Q : Type} [Finite Q] {M : NTM κ (Option Bool) Q}
    (h : DecidesWithin M p t s) : TimeSpaceModel.ntm.NDecidableWithin p t s :=
  nDecidableWithin_iff.mpr ⟨κ, inferInstance, Q, inferInstance, M, h⟩

end InputBudgets

end Complexity.NTM
