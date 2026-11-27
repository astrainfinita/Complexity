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

open Complexity TreeProgram Complexity.TreeProgram.Source
open Complexity.TreeProgram.Source.Internal (HasProgramInO)
open Filter

namespace ComplexityTest.SourceTranslation.Asymptotics

-- The FDTISP source endpoint must not bring the optional analysis bridge back into scope.
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
    (h : Dominated (fun z : {p : Σ _ : ℕ, ℕ // p.2 ∈ xs p.1} => a z.1.1 z.1.2)
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

-- A chosen arbitrary implementation is reused with its own growth.
example {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β] {f : α → β}
    {pf : Value → Code Value} {t p : α → ℕ}
    (hf : HasProgramInO f pf t p) : HasProgramInO f pf t p := by
  source_fun_prop

example {α : Type*} [UniqueEncoding Tree α] {f : α → α} {pf : Value → Code Value} {t p : α → ℕ}
    (_hf : HasProgramInO f pf t p) :
    HasProgramInO (fun x => f (f x)) hole(pf ⊢ program) (fun x => t x + t (f x))
      (fun x => max (p x) (p (f x))) := by
  fill_hole program in source_fun_prop

def preciseIdentity (xs : List Bool) := xs

@[program] theorem hasProgramIn_preciseIdentity :
    HasProgramIn preciseIdentity hole(⊢ program) IsO(fun _ => 0) IsO(fun _ => 0) := by
  abstract_hole program using programPreciseIdentity
  refine HasProgramInO.toHasProgramIn ?_
  fill_hole program in
    exact HasProgramInO.identity

-- A weaker mathematical consequence is legal, but it is not another selected implementation.
theorem hasProgramIn_preciseIdentityWeaker : HasProgramIn preciseIdentity hole(⊢ program)
    IsO(fun x => ⌜x⌝ₜ.size ^ 2) IsO(fun x => ⌜x⌝ₜ.size ^ 2) := by
  abstract_hole program using programPreciseIdentityWeaker
  refine HasProgramInO.toHasProgramIn ?_
  fill_hole program in
    exact hasProgramIn_preciseIdentity.toHasProgramInO.mono Dominated.zero Dominated.zero

/-- error: `program` already has a selected implementation of preciseIdentity: hasProgramIn_preciseIdentity; choose another one at a call with a local hypothesis or `via` -/
#guard_msgs in
attribute [local program] hasProgramIn_preciseIdentityWeaker

-- A coarser model exit does not change the selected implementation's growth.
theorem preciseIdentity_fdtisp :
    preciseIdentity ∈ FDTISP .tree (fun n => n ^ 2) (fun n => n ^ 2) := by
  model_fun_prop

-- An alias of a selected implementation keeps its program and growth.
def aliasedIdentity (xs : List Bool) := preciseIdentity xs

example := (by source_fun_prop : HasProgramInO aliasedIdentity programPreciseIdentity _ _)

example : HasProgramInO aliasedIdentity hole(⊢ program) (fun _ => 0) (fun _ => 0) := by
  fill_hole program in source_fun_prop

theorem identity_fdtisp : (id : List Bool → List Bool) ∈ FDTISP .tree (fun _ => 1) id := by
  model_fun_prop

def viaIdentity (xs : List Bool) := xs

-- Source replacement still leaves its equality obligation ahead of the two growth goals.
theorem via_fdtisp : viaIdentity ∈ FDTISP .tree (fun _ => 1) id := by
  model_fun_prop via (id : List Bool → List Bool)
  case source_eq => rfl

-- The canonical general exit is also accepted directly, without a tactic wrapper.
theorem identity_direct_fdtisp :
    (id : List Bool → List Bool) ∈ FDTISP .tree (fun _ => 1) id :=
  (HasProgramInO.identity.mono Dominated.zero Dominated.zero).mem_fdtisp
      (Dominated.refl _) (Dominated.const 4)
      (Dominated.const_of_pos 2 fun _ => Tree.size_pos _)

-- The boundary keeps the actual small-input machine cost, while empty large-size fibers vanish.
theorem finiteIdentity_fdtisp :
    (id : Unit → Unit) ∈ FDTISP .tree (fun _ => 0) (fun _ => 0) := by
  apply HasProgramInO.identity.mem_fdtisp_of_sizeEnvelope
  all_goals
    refine ⟨0, eventually_atTop.mpr ⟨2, fun n hn => ?_⟩⟩
    simp only [Nat.zero_mul]
    apply sizeEnvelope_le
    intro x hx
    have hs : ⌜x⌝ₜ.size = 1 := size_encode_unit x
    omega

-- A program on a finite type has positive cost on every input, even though its size class is zero.
theorem finiteNot_fdtisp : Bool.not ∈ FDTISP .tree (fun _ => 0) (fun _ => 0) := by
  apply Bool.hasProgramIn_not.mem_fdtisp_of_sizeEnvelope
  all_goals
    refine ⟨0, eventually_atTop.mpr ⟨4, fun n hn => ?_⟩⟩
    simp only [Nat.zero_mul]
    apply sizeEnvelope_le
    intro x hx
    have hs := size_encode_bool_le x
    omega

end ComplexityTest.SourceTranslation.Asymptotics
