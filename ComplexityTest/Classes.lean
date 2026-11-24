/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Classes.Nondeterministic.Deterministic
import Complexity.Classes.TreeTuringSimulation

open Complexity

namespace Complexity.ClassesTest

-- A finite machine copies the complete structured Boolean code.
private def bit : TM Id (Fin 0) (Option Bool) Bool where
  q₀ := false
  halt := id
  transition := fun _ (a, _) ↦ pure <|
    (a.isNone, { inputMove := 1, work := Fin.elim0, output := a.map some })

private theorem bit_spec : TM.Computes bit (id : Bool → Bool) (fun _ => 4) (fun _ => 0) := by
  apply Encoding.Computes.iff_of_uniqueEncoding.mpr
  intro b
  cases b <;> apply Controller.computesWithinCost_unit_iff.mpr <;>
    exact ⟨rfl, rfl, fun _ ↦ by simp [Controller.History.space]⟩

private theorem bit_fp : (id : Bool → Bool) ∈ FP .tm :=
  FP.of_isPoly (FDTISP.subset_time
    (bit_spec.computableWithin.mem_fdtisp (T := fun _ => 4) (S := fun _ => 0))) (.const 4)

-- The same function covers both acceptance and rejection, with no work tapes.
example : (fun b : Bool => b = true) ∈ P .tm := by
  apply P.of_decides bit_fp
  intro b
  rfl

-- Increasing the time budget does not change output or invent extra space.
example : TM.Computes bit (id : Bool → Bool) (fun _ => 5) (fun _ => 0) :=
  bit_spec.mono (fun _ => by decide) (fun _ => le_rfl)

-- Budgets can distinguish input values, without requiring a function of code size.
example : TM.Computes bit (id : Bool → Bool) (fun b => if b then 5 else 4) (fun _ => 0) :=
  bit_spec.mono (fun b => by cases b <;> decide) (fun _ => le_rfl)

-- A zero resource remains zero on a finite input type in the `ComputableIn` interface.
example : TimeSpaceModel.tm.ComputableIn (id : Bool → Bool)
    IsO(fun _ => 1) IsO(fun _ => 0) :=
  bit_spec.computableWithin.computableIn.mono
    (fun _ h => h.trans ⟨4, fun _ => le_rfl⟩) fun _ h => h

-- The same proof supplies a nondeterministic machine bounding every branch.
example : TimeSpaceModel.ntm.NDecidableIn (fun b : Bool => b = true)
    IsO(fun _ => 4) IsO(fun _ => 0) :=
  TM.nDecidableIn_of_computable bit_spec.computableWithin.computableIn
    (fun _ => Iff.rfl)

-- The exact proof supplies a single machine for both asymptotic bounds.
example : (fun b : Bool => b = true) ∈ DTISP .tm (fun _ => 4) (fun _ => 0) :=
  DTISP.of_decides bit_spec.computableWithin.mem_fdtisp
    (fun _ => Iff.rfl)

-- Guards that `.tm`, `.stack` and `.ntm`, stated as instances of `TimeSpaceModel.tmWith` and
-- `TimeSpaceModel.stackWith`, keep by definition the behaviors they were written with: the
-- deterministic specifications on `Id`, and on `Multiset` the outputs of all branches mapped.
example : TimeSpaceModel.tm.behaviors =
    {R | ∃ (κ : Type) (_ : Fintype κ) (Q : Type) (_ : Finite Q) (M : TM Id κ (Option Bool) Q),
      R = fun xs result => M.ComputesWithin (xs.toList.map some) (result.run.toList.map some)} :=
  rfl

example : TimeSpaceModel.stack.behaviors =
    {R | ∃ (κ : Type) (_ : Fintype κ) (Q : Type) (_ : Finite Q) (M : StackMachine Id κ Bool Q),
      R = fun xs result ↦ M.ComputesWithin xs.toList result.run.toList} :=
  rfl

example : TimeSpaceModel.ntm.behaviors =
    {R | ∃ (κ : Type) (_ : Fintype κ) (Q : Type) (_ : Finite Q) (M : NTM κ (Option Bool) Q),
      R = fun (xs : RawWord Bool) ys =>
        M.ComputesWithinWith Multiset (xs.toList.map some) (ys.map fun y ↦ y.toList.map some)} :=
  rfl

-- Guards that a behavior of `.tm` opened by hand, rather than through
-- `TM.computableWithin_iff`, reaches the entries of the specification by dot notation: it is the
-- general specification of the model at `Id`, to which `mono` and `exists_halted` are attached.
example {f : Bool → Bool} {t s : Bool → ℕ} (h : TimeSpaceModel.tm.ComputableWithin f t s)
    (r : RawWord Bool) (b : Bool) (hb : b ∈ decode Bool r) : True := by
  obtain ⟨R, ⟨κ, hκ, Q, hQ, M, rfl⟩, h⟩ := h
  obtain ⟨q, hq, hc⟩ := h b r hb
  exact (hc.mono (Nat.le_succ _) le_rfl).exists_halted.elim fun _ _ ↦ trivial

-- A halted tree machine already has the Boolean result in its input/output register.
private def tree : TreeMachine Id 1 Unit where
  q₀ := ()
  halt _ := true
  transition _ _ := pure <| ((), .nop)

private theorem tree_spec :
    TreeMachine.Computes tree (id : Bool → Bool) (fun _ => 0) (fun b => (encode Tree b).size) := by
  apply Encoding.Computes.iff_of_uniqueEncoding.mpr
  intro b
  refine .of_halted 0 rfl ?_ le_rfl ?_
  · exact TreeMachine.input_get (0 : Fin 1) _
  · simp [TreeMachine.Cfg.mass]

private theorem tree_fp : (id : Bool → Bool) ∈ FP .sizeCostTree :=
  FP.of_isPoly (FDTISP.subset_time
    (tree_spec.computableWithin.mem_fdtisp (T := fun _ => 0) (S := id))) (.const 0)

example : (fun b : Bool => b = true) ∈ P .sizeCostTree := by
  apply P.of_decides tree_fp
  intro b
  rfl

example : (fun b : Bool => b = true) ∈ DTISP .sizeCostTree (fun _ => 0) id :=
  DTISP.of_decides tree_spec.computableWithin.mem_fdtisp
    (fun _ => Iff.rfl)

-- Tree input storage counts toward space even when no transition is executed.
example : ¬TreeMachine.Computes tree (id : Bool → Bool) (fun _ => 0) (fun _ => 0) := by
  intro h
  have hh := (Encoding.Computes.iff_of_uniqueEncoding.mp h) false
  have hm := hh.mass_le 0
  simp [TreeMachine.Cfg.mass] at hm

-- Eventual size bounds may ignore the finitely many legal sizes of a finite encoded type.
-- This does not turn the all-input machine specification above into a zero-space one.
example : (id : Bool → Bool) ∈ FDTISP .sizeCostTree (fun _ => 0) (fun _ => 0) := by
  have h : TimeSpaceModel.sizeCostTree.ComputableWithinBySize (id : Bool → Bool)
      (fun _ => 0) (fun n => if n ≤ 3 then n else 0) := by
    obtain ⟨R, hR, h⟩ := tree_spec.computableWithin
    refine ⟨R, hR, fun a r ha => ?_⟩
    obtain rfl := UniqueEncoding.mem_decode_iff.mp ha
    change ∃ q, id a ∈ decode Bool q ∧ R (encode Tree a) (pure q) 0
      (if (encode Tree a).size ≤ 3 then (encode Tree a).size else 0)
    rw [ite_eq_left (size_encode_bool_le a)]
    exact h a (encode Tree a) (UniqueEncoding.mem_decode_iff.mpr rfl)
  exact h.mem_fdtisp_of_dominated (DominatedAtTop.refl _)
    (dominatedAtTop_iff.mpr ⟨1, 4, fun n hn => by simp [show ¬n ≤ 3 by omega]⟩)

-- The abstract interface stays in Type, without storing a type of machine witnesses.
example : Type := TimeSpaceModel Id (List Bool)

-- Constants and finite initial exceptions are absorbed by O(n) for any model.
example {Data α : Type*} [Encoding Data α] [Encoding Data Bool]
    (model : TimeSpaceModel Id Data) :
    DTIME model (α := α) (fun n => 5 * n + 17) ⊆ DTIME model id :=
  DTIME.mono (dominatedAtTop_iff.2 ⟨22, 1, fun n hn => by dsimp; omega⟩)

-- The simultaneous class projects to the two separate classes.
example {Data α : Type*} [Encoding Data α] [Encoding Data Bool]
    (model : TimeSpaceModel Id Data) {p : α → Prop} {T S : ℕ → ℕ}
    (h : p ∈ DTISP model T S) : p ∈ DTIME model T ∧ p ∈ DSPACE model S :=
  DTISP.subset_inter h

section Nonunique

-- Every natural number denotes the same value, with arbitrarily expensive codes.
local instance : Encoding ℕ Unit where
  decode _ := Part.some ()
  exists_code _ := ⟨0, Part.mem_some_iff.mpr (Subsingleton.elim _ _)⟩

private def codeCost : TimeSpaceModel Id ℕ where
  inputSize := id
  behaviors := {fun x _ t _ => x ≤ t}
  budget_mono := by
    rintro R rfl x y t s t' s' h ht _
    exact h.trans ht

private theorem codeCost_spec :
    codeCost.ComputableWithinBySize (id : Unit → Unit) id (fun _ => 0) := by
  refine ⟨_, rfl, fun a r _ => ?_⟩
  cases a
  exact ⟨0, Part.mem_some_iff.mpr rfl, le_rfl⟩

example : (id : Unit → Unit) ∈ FDTISP codeCost id (fun _ => 0) :=
  codeCost_spec.mem_fdtisp

-- The size certificate keeps its all-input n+1 budget; only the class comparison ignores n=0.
example : (id : Unit → Unit) ∈ FDTIME codeCost id := by
  have h := codeCost_spec.mono (fun n => Nat.le_succ n) (fun _ => le_rfl)
  exact h.mem_fdtime_of_dominated
    (dominatedAtTop_iff.mpr ⟨2, 1, fun n hn => by dsimp; omega⟩)

-- The public value-budget API rejects a value whose legal codes have unbounded costs.
example : ¬∃ t s, codeCost.ComputableWithin (id : Unit → Unit) t s := by
  rintro ⟨t, s, R, rfl, h⟩
  obtain ⟨q, hq, ht⟩ := h () (t () + 1) (Part.mem_some_iff.mpr rfl)
  change t () + 1 ≤ t () at ht
  omega

private def constantCost : TimeSpaceModel Id ℕ where
  inputSize _ := 1
  behaviors := {fun _ q t _ => q.run = 0 ∧ 1 ≤ t}
  budget_mono := by
    rintro R rfl x y t s t' s' h ht _
    exact ⟨h.1, h.2.trans ht⟩

-- Nonunique input and output codes are supported; only one legal output is required.
example : constantCost.ComputableIn (id : Unit → Unit) IsO(fun _ => 1) IsO(fun _ => 0) := by
  apply TimeSpaceModel.ComputableWithin.computableIn
  refine ⟨_, rfl, fun a _ _ => ?_⟩
  cases a
  exact ⟨0, Part.mem_some_iff.mpr rfl, rfl, le_rfl⟩

-- The common resource layer permits budgets to depend on the actual legal code.
example : codeCost.ComputableWithinByCode (id : Unit → Unit)
    (fun _ src => src) (fun _ _ => 0) := by
  refine ⟨_, rfl, fun a _ _ => ?_⟩
  cases a
  exact ⟨0, Part.mem_some_iff.mpr rfl, le_rfl⟩

-- Each behavior can save one resource only by using the other resource.
private def resourceTradeoff : TimeSpaceModel Id ℕ where
  inputSize := id
  behaviors := {fun _ _ _ s => 1 ≤ s, fun _ _ t _ => 1 ≤ t}
  budget_mono := by
    rintro R (rfl | rfl) x y t s t' s' h ht hs
    · exact h.trans hs
    · exact h.trans ht

example : (id : Unit → Unit) ∈ FDTIME resourceTradeoff (fun _ => 0) ∩
    FDSPACE resourceTradeoff (fun _ => 0) := by
  constructor
  · apply TimeSpaceModel.ComputableWithinBySize.mem_fdtime (s := fun _ => 1)
    refine ⟨_, Or.inl rfl, fun a _ _ => ?_⟩
    cases a
    exact ⟨0, Part.mem_some_iff.mpr rfl, le_rfl⟩
  · apply TimeSpaceModel.ComputableWithinBySize.mem_fdspace (t := fun _ => 1)
    refine ⟨_, Or.inr rfl, fun a _ _ => ?_⟩
    cases a
    exact ⟨0, Part.mem_some_iff.mpr rfl, le_rfl⟩

-- Joint bounds cannot borrow time from one machine and space from another.
example : (id : Unit → Unit) ∉ FDTISP resourceTradeoff (fun _ => 0) (fun _ => 0) := by
  rintro ⟨t, s, ⟨R, hR, h⟩, ht, hs⟩
  obtain ⟨C, N, ht⟩ := dominatedAtTop_iff.mp ht
  obtain ⟨D, M, hs⟩ := dominatedAtTop_iff.mp hs
  obtain ⟨_, _, hrun⟩ := h () (max N M) (Part.mem_some_iff.mpr rfl)
  have ht := ht (max N M) (le_max_left _ _)
  have hs := hs (max N M) (le_max_right _ _)
  rcases hR with rfl | rfl
  · change 1 ≤ s (max N M) at hrun
    simp only [mul_zero] at hs
    omega
  · change 1 ≤ t (max N M) at hrun
    simp only [mul_zero] at ht
    omega

end Nonunique

-- Keep the old, fully expanded definitions here as semantic regression specifications.
-- In particular, the other resource is still a size function outside all input quantifiers.
example {Data α β : Type*} [Encoding Data α] [Encoding Data β]
    (model : TimeSpaceModel Id Data) (f : α → β) (T : ℕ → ℕ) :
    f ∈ FDTIME model T ↔
      ∃ t, (∃ s : ℕ → ℕ, ∃ R ∈ model.behaviors,
        ∀ src a, a ∈ decode α src →
          ∃ dst, f a ∈ decode β dst ∧
            R src (pure dst) (t (model.inputSize src))
              (s (model.inputSize src))) ∧ DominatedAtTop t T := by
  constructor
  · rintro ⟨t, ⟨s, R, hR, h⟩, ht⟩
    exact ⟨t, ⟨s, R, hR, fun r a ha => h a r ha⟩, ht⟩
  · rintro ⟨t, ⟨s, R, hR, h⟩, ht⟩
    exact ⟨t, ⟨s, R, hR, fun a r ha => h r a ha⟩, ht⟩

example {Data α β : Type*} [Encoding Data α] [Encoding Data β]
    (model : TimeSpaceModel Id Data) (f : α → β) (S : ℕ → ℕ) :
    f ∈ FDSPACE model S ↔
      ∃ s, (∃ t : ℕ → ℕ, ∃ R ∈ model.behaviors,
        ∀ src a, a ∈ decode α src →
          ∃ dst, f a ∈ decode β dst ∧
            R src (pure dst) (t (model.inputSize src))
              (s (model.inputSize src))) ∧ DominatedAtTop s S := by
  constructor
  · rintro ⟨s, ⟨t, R, hR, h⟩, hs⟩
    exact ⟨s, ⟨t, R, hR, fun r a ha => h a r ha⟩, hs⟩
  · rintro ⟨s, ⟨t, R, hR, h⟩, hs⟩
    exact ⟨s, ⟨t, R, hR, fun a r ha => h r a ha⟩, hs⟩

example {Data α β : Type*} [Encoding Data α] [Encoding Data β]
    (model : TimeSpaceModel Id Data) (f : α → β) (T S : ℕ → ℕ) :
    f ∈ FDTISP model T S ↔
      ∃ t s, (∃ R ∈ model.behaviors,
        ∀ src a, a ∈ decode α src →
          ∃ dst, f a ∈ decode β dst ∧
            R src (pure dst) (t (model.inputSize src))
              (s (model.inputSize src))) ∧
        DominatedAtTop t T ∧ DominatedAtTop s S := by
  constructor
  · rintro ⟨t, s, ⟨R, hR, h⟩, ht, hs⟩
    exact ⟨t, s, ⟨R, hR, fun r a ha => h a r ha⟩, ht, hs⟩
  · rintro ⟨t, s, ⟨R, hR, h⟩, ht, hs⟩
    exact ⟨t, s, ⟨R, hR, fun a r ha => h r a ha⟩, ht, hs⟩

end Complexity.ClassesTest
