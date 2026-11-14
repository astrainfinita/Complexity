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

theorem accepts_iff_of_forall_halted {t : ℕ}
    (h : ∀ c ∈ M.runWith Multiset (xs.toList.map some) t, M.Halted c) :
    M.Accepts xs ↔ ∃ c ∈ M.runWith Multiset (xs.toList.map some) t,
        c.2.output = (⌜true⌝₂.toList.map some).toArray :=
  produces_iff_of_forall_halted h

theorem booleanOutput_iff_of_forall_halted {t : ℕ}
    (h : ∀ c ∈ M.runWith Multiset (xs.toList.map some) t, M.Halted c) :
    M.BooleanOutput xs ↔ ∀ c ∈ M.runWith Multiset (xs.toList.map some) t,
        ∃ b : Bool, c.2.output = (⌜b⌝₂.toList.map some).toArray := by
  simp only [BooleanOutput, produces_iff_of_forall_halted h, ← Array.toList_inj,
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
multiplicities. Resource bounds cover every branch, including rejecting branches. The outputs are
read at any step by which every branch has halted. -/
def _root_.Complexity.TimeSpaceModel.ntm : TimeSpaceModel Multiset (RawWord Bool) where
  inputSize := RawWord.length
  behaviors := {R | ∃ (κ : Type) (_ : Fintype κ) (Q : Type) (_ : Finite Q)
      (M : NTM κ (Option Bool) Q), R = fun (xs : RawWord Bool) ys t s =>
        (∀ h ∈ M.histories Multiset (xs.toList.map some), h.length ≤ t ∧ h.snd.space ≤ s) ∧
        ∃ n, (∀ c ∈ M.runWith Multiset (xs.toList.map some) n, M.Halted c) ∧
          ys.map (fun y => (y.toList.map some).toArray) =
            (M.runWith Multiset (xs.toList.map some) n).map (·.2.output)}
  budget_mono := by
    rintro R ⟨κ, hκ, Q, hQ, M, rfl⟩ xs ys t s t' s' ⟨hb, ho⟩ htt hss
    exact ⟨fun h hh ↦ (hb h hh).imp (·.trans htt) (·.trans hss), ho⟩

section InputBudgets

variable {α : Type*} [Encoding (RawWord Bool) α]
  {κ Q : Type*} {M : NTM κ (Option Bool) Q} {p : α → Prop} {t s : α → ℕ}

/-- Every branch obeys the same value-indexed budgets on every legal input code. -/
def DecidesWithin [Fintype κ] (M : NTM κ (Option Bool) Q) (p : α → Prop)
    (t s : α → ℕ) : Prop :=
  ∀ (r : RawWord Bool) a, a ∈ decode α r →
    (∀ h ∈ M.histories Multiset (r.toList.map some), h.length ≤ t a ∧ h.snd.space ≤ s a) ∧
    M.BooleanOutput r ∧ (M.Accepts r ↔ p a)

theorem DecidesWithin.mono [Fintype κ]
    (h : DecidesWithin M p t s) {t' s' : α → ℕ}
    (ht : ∀ a, t a ≤ t' a) (hs : ∀ a, s a ≤ s' a) :
    DecidesWithin M p t' s' :=
  fun r a ha => ⟨fun c hc ↦ ((h r a ha).1 c hc).imp (·.trans (ht a)) (·.trans (hs a)),
    (h r a ha).2⟩

theorem nDecidableWithin_iff :
    TimeSpaceModel.ntm.NDecidableWithin p t s ↔
      ∃ (κ : Type) (_ : Fintype κ) (Q : Type) (_ : Finite Q)
        (M : NTM κ (Option Bool) Q), DecidesWithin M p t s := by
  constructor
  · rintro ⟨R, ⟨κ, hκ, Q, hQ, M, rfl⟩, h⟩
    refine ⟨κ, hκ, Q, hQ, M, fun r a ha => ?_⟩
    obtain ⟨ys, ⟨hb, n, hn, he⟩, hv, hp⟩ := h a r ha
    obtain ⟨hv, hp⟩ := (exists_boolean_outputs_iff _ _ _).mp ⟨ys, he, hv, hp⟩
    exact ⟨hb, (booleanOutput_iff_of_forall_halted hn).mpr hv,
      (accepts_iff_of_forall_halted hn).trans hp⟩
  · rintro ⟨κ, hκ, Q, hQ, M, h⟩
    refine ⟨_, ⟨κ, hκ, Q, hQ, M, rfl⟩, fun a r ha => ?_⟩
    obtain ⟨hb, hv, hp⟩ := h r a ha
    have hn := M.forall_halted_succ_of_forall_length_le Multiset (r.toList.map some)
      fun c hc ↦ (hb c hc).1
    obtain ⟨ys, he, hv, hp⟩ := (exists_boolean_outputs_iff _ _ _).mpr
      ⟨(booleanOutput_iff_of_forall_halted hn).mp hv,
        (accepts_iff_of_forall_halted hn).symm.trans hp⟩
    exact ⟨ys, ⟨hb, _, hn, he⟩, hv, hp⟩

theorem DecidesWithin.nDecidableWithin {κ : Type} [Fintype κ]
    {Q : Type} [Finite Q] {M : NTM κ (Option Bool) Q}
    (h : DecidesWithin M p t s) : TimeSpaceModel.ntm.NDecidableWithin p t s :=
  nDecidableWithin_iff.mpr ⟨κ, inferInstance, Q, inferInstance, M, h⟩

end InputBudgets

end Complexity.NTM
