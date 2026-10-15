/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Tactic.TreeProgram.Translation
public import Complexity.Tactic.TreeProgram.Recursion
public import Complexity.Tactic.TreeProgram.Library

@[expose] public section

open Complexity TreeProgram Complexity.TreeProgram.Source Filter

namespace ComplexityTest.SourceTranslation.Asymptotics

-- The FTISP source endpoint must not bring the optional analysis bridge back into scope.
open Lean Elab in
run_elab do
  let env ← getEnv
  if env.contains `Asymptotics.IsBigO || env.contains `Real then
    throwError "the asymptotic source endpoint unexpectedly imported real analysis"

-- The base relation needs neither multiplication nor a norm on the resource type.
example {α M : Type*} [AddCommMonoid M] [PartialOrder M] [CanonicallyOrderedAdd M]
    (f g h : α → M) (hf : Dominated f g) (hg : Dominated g h) : Dominated f h := hf.trans hg

-- Substitution includes constant calls and repeatedly visited small inputs.
example {α β M : Type*} [AddCommMonoid M] [PartialOrder M] [CanonicallyOrderedAdd M]
    {f g : α → M} (h : Dominated f g) (u : β → α) : Dominated (f ∘ u) (g ∘ u) := h.comp u

def exceptional (n : ℕ) : ℕ := if n = 0 then 100 else 0

theorem exceptional_bound : Dominated exceptional (fun _ => 1) := by
  apply Dominated.of_le_mul 100
  intro n
  simp only [exceptional, Nat.mul_one]
  split <;> omega

example : Dominated (exceptional ∘ fun _ : ℕ => 0) (fun _ => 1) :=
  exceptional_bound.comp (fun _ => 0)

example : ¬ Dominated exceptional (fun _ => 0) := by
  rintro ⟨C, h⟩
  have := h 0
  simp [exceptional] at this

-- Having a separate coefficient for each callback does not give a uniform family bound.
example : (∀ i : ℕ, Dominated (fun _ : ℕ => i) (fun _ => 1)) ∧
    ¬ Dominated (fun x : ℕ × ℕ => x.2) (fun _ => 1) := by
  refine ⟨fun i => Dominated.const i, ?_⟩
  rintro ⟨C, hc⟩
  have := hc (0, C + 1)
  simp only [Nat.nsmul_eq_mul, Nat.mul_one] at this
  omega

example {α ι : Type*} (s : α → Finset ι) (f g : α → ι → ℕ)
    (h : ∃ C, ∀ x i, i ∈ s x → f x i ≤ C * g x i) :
    Dominated (fun x => ∑ i ∈ s x, f x i) (fun x => ∑ i ∈ s x, g x i) := by
  apply Dominated.sum
  obtain ⟨C, hC⟩ := h
  exact ⟨C, fun z => hC z.1.1 z.1.2 z.2⟩

-- Nonzero in a generic additive resource does not absorb unrelated overhead.
example : ¬ Dominated (fun _ : ℕ => ((0, 1) : ℕ × ℕ)) (fun _ => (1, 0)) := by
  rintro ⟨C, h⟩
  have := (h 0).2
  simp at this

-- Polynomial substitution needs no positivity assumption, including at the internal input zero.
example {f : ℕ → ℕ} (hf : Dominated f (fun n => n ^ 3))
    {u : List Bool → ℕ} (hu : Dominated u (fun xs => ⌜xs⌝ₜ.size ^ 2)) :
    Dominated (f ∘ u) (fun xs => ⌜xs⌝ₜ.size ^ 6) :=
  Dominated.comp_pow hf hu

example (s : Finset ℕ) (a b : ℕ → ℕ → ℕ) (h : ∀ i ∈ s, Dominated (a i) (b i)) :
    Dominated (fun x => ∑ i ∈ s, a i x) (fun x => ∑ i ∈ s, b i x) :=
  Dominated.finset_sum s a b h

-- Duplicates are counted, and the family coefficient covers every list length.
example (xs : ℕ → List ℕ) (a b : ℕ → ℕ → ℕ)
    (h : Dominated (fun z : {p : ℕ × ℕ // p.2 ∈ xs p.1} => a z.1.1 z.1.2)
      (fun z => b z.1.1 z.1.2)) :
    Dominated (fun x => ((xs x).map (a x)).sum) (fun x => ((xs x).map (b x)).sum) :=
  Dominated.list_sum xs a b h

-- A finite input type does not make positive costs compatible with a zero resource budget.
example : ¬ Dominated (fun _ : Unit => 7) (fun _ => 0) := by
  rintro ⟨C, h⟩
  have := h ()
  simp at this

example : Dominated (fun _ : Unit => (0 : ℕ)) (fun _ => 0) := Dominated.zero

-- Only the size-indexed complexity relation may ignore the exceptional size zero.
example : DominatedAtTop (fun _ => 1) id := by
  exact ⟨1, eventually_atTop.mpr ⟨1, fun n hn => by simpa using hn⟩⟩

example : ¬ Dominated (fun _ : ℕ => 1) id := by
  rintro ⟨C, h⟩
  have := h 0
  simp at this

-- A chosen arbitrary implementation is reused without selecting a replacement program.
example {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β] {f : α → β}
    (hf : Implementation f) {t p : α → ℕ} (usable : hf.HasGrowth t p) : hf.HasGrowth t p := by
  source_fun_prop
  all_goals exact Dominated.refl _

example {α : Type*} [UniqueEncoding Tree α] {f : α → α}
    (hf : Implementation f) {t p : α → ℕ} (usable : hf.HasGrowth t p) :
    (hf.comp hf).HasGrowth (fun x => t x + t (f x))
      (fun x => max (p x) (p (f x))) := by
  source_fun_prop
  all_goals exact Dominated.refl _

-- Constant internal inputs use the same selected callback and its all-input specification.
example {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β] {f : α → β}
    (hf : Implementation f) {t p : α → ℕ} (usable : hf.HasGrowth t p) (a : α) :
    Dominated (fun _ : Unit => hf.bounds.time a) (fun _ => t a) := usable.1.comp (fun _ => a)

-- Local fixed overhead remains readable in a structural resource expression.
example {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β] {f : α → β}
    (hf : Implementation f) {t p : α → ℕ} (usable : hf.HasGrowth t p) :
    Dominated (fun x => hf.bounds.time x + 7) (fun x => t x + 7) := by
  source_fun_prop
  exact Dominated.refl _

-- Used by two independently compiled modules to exercise conflicting imports.
noncomputable def importConflictImplementation : Implementation (id : Bool → Bool) :=
  Implementation.identity

def preciseIdentity (xs : List Bool) := xs

noncomputable def preciseIdentityImplementation : Implementation preciseIdentity := by source_fun_prop

@[source_growth] theorem preciseIdentity_growth : preciseIdentityImplementation.HasGrowth
    (fun _ => 0) (fun _ => 0) := by
  source_fun_prop
  all_goals exact Dominated.refl _

-- A weaker mathematical consequence is legal, but is not another registered call budget.
theorem preciseIdentity_weaker : preciseIdentityImplementation.HasGrowth
    (fun x => ⌜x⌝ₜ.size ^ 2) (fun x => ⌜x⌝ₜ.size ^ 2) :=
  (preciseIdentity_growth.mono Dominated.zero Dominated.zero)

/-- error: `source_growth` already has a specification for ComplexityTest.SourceTranslation.Asymptotics.preciseIdentityImplementation: ComplexityTest.SourceTranslation.Asymptotics.preciseIdentity_growth -/
#guard_msgs in
attribute [local source_growth] preciseIdentity_weaker

-- Deliberately coarser than the callback's specification, to test imported model exports.
@[source] theorem preciseIdentity_ftisp :
    preciseIdentity ∈ FTISP .tree (fun n => n ^ 2) (fun n => n ^ 2) :=
  (preciseIdentity_growth.mono (t' := fun x => ⌜x⌝ₜ.size ^ 2) (p' := fun x => ⌜x⌝ₜ.size ^ 2)
    Dominated.zero Dominated.zero).mem_ftisp_pow (by decide)

-- The saved theorem retains the original zero callback costs despite the coarser model exit.
example : preciseIdentityImplementation.HasGrowth (fun _ => 0) (fun _ => 0) :=
  preciseIdentity_ftisp.hasGrowth_sourceImplementation

-- A reducible implementation alias must preserve the original registered call specification.
def aliasedIdentity (xs : List Bool) := preciseIdentity xs

noncomputable def aliasedIdentityImplementation : Implementation aliasedIdentity :=
  preciseIdentityImplementation

theorem aliasedIdentity_weaker : aliasedIdentityImplementation.HasGrowth
    (fun x => ⌜x⌝ₜ.size ^ 2) (fun x => ⌜x⌝ₜ.size ^ 2) := preciseIdentity_weaker

@[source] theorem aliasedIdentity_ftisp :
    aliasedIdentity ∈ FTISP .tree (fun n => n ^ 2) (fun n => n ^ 2) :=
  aliasedIdentity_weaker.mem_ftisp_pow (by decide)

example : aliasedIdentityImplementation.HasGrowth (fun _ => 0) (fun _ => 0) :=
  aliasedIdentity_ftisp.hasGrowth_sourceImplementation

@[source]
theorem identity_ftisp : (id : List Bool → List Bool) ∈ FTISP .tree (fun _ => 1) id := by
  model_fun_prop
  · exact Dominated.const 4
  · have hpos (xs : List Bool) : 0 < ⌜xs⌝ₜ.size := Tree.size_pos _
    simpa only [Nat.max_zero, id_eq] using
      ((Dominated.refl (fun xs : List Bool => ⌜xs⌝ₜ.size)).add_same
      ((Dominated.const 2).trans (Dominated.one hpos)))

def viaIdentity (xs : List Bool) := xs

-- Source replacement still leaves its equality obligation ahead of the two growth goals.
@[source] theorem via_ftisp : viaIdentity ∈ FTISP .tree (fun _ => 1) id := by
  model_fun_prop via (id : List Bool → List Bool)
  case source_eq => rfl
  case time =>
    exact Dominated.of_forall_eq fun _ _ => rfl
  case peak =>
    have h : Dominated (fun xs : List Bool => ⌜xs⌝ₜ.size + 2) (fun xs => ⌜xs⌝ₜ.size) :=
      (Dominated.refl _).add_same
        ((Dominated.const 2).trans (Dominated.one fun _ => Tree.size_pos _))
    simpa only [Function.comp_apply, Nat.max_self, Nat.max_zero, id_eq] using h

-- The canonical general exit is also accepted directly, without a tactic wrapper.
@[source] theorem identity_direct_ftisp :
    (id : List Bool → List Bool) ∈ FTISP .tree (fun _ => 1) id :=
  (identity_ftisp.hasGrowth_sourceImplementation.mono
    (t' := fun _ => 1) (p' := fun xs => ⌜xs⌝ₜ.size) Dominated.zero Dominated.zero).mem_ftisp
      (Dominated.refl _) (Dominated.const 4)
      (Dominated.const_of_pos 2 fun _ => Tree.size_pos _)

-- The boundary keeps the actual small-input machine cost, while empty large-size fibers vanish.
@[source] theorem finiteIdentity_ftisp :
    (id : Unit → Unit) ∈ FTISP .tree (fun _ => 0) (fun _ => 0) := by
  have growth : (Implementation.identity (α := Unit)).HasGrowth (fun _ => 0) (fun _ => 0) := by
    source_fun_prop
    all_goals exact Dominated.zero
  apply growth.mem_ftisp_of_sizeEnvelope
  all_goals
    refine ⟨0, eventually_atTop.mpr ⟨2, fun n hn => ?_⟩⟩
    simp only [Nat.zero_mul]
    apply sizeEnvelope_le
    intro x hx
    have hs : ⌜x⌝ₜ.size = 1 := by cases x; exact size_encode_unit
    omega

-- The saved all-input callback has positive cost even though its final size class is zero.
noncomputable def finiteNotImplementation : Implementation Bool.not := by source_fun_prop

@[source_growth] theorem finiteNot_growth : finiteNotImplementation.HasGrowth
    (fun _ => 1) (fun _ => 1) := by
  source_fun_prop
  · exact Dominated.const _
  · exact (Dominated.const 3).mono_left size_encode_bool_le

@[source] theorem finiteNot_ftisp : Bool.not ∈ FTISP .tree (fun _ => 0) (fun _ => 0) := by
  apply finiteNot_growth.mem_ftisp_of_sizeEnvelope
  all_goals
    refine ⟨0, eventually_atTop.mpr ⟨4, fun n hn => ?_⟩⟩
    simp only [Nat.zero_mul]
    apply sizeEnvelope_le
    intro x hx
    have hs := size_encode_bool_le x
    omega

end ComplexityTest.SourceTranslation.Asymptotics
