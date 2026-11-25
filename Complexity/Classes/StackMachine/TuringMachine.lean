/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Classes.Deterministic
public import Complexity.Classes.Nondeterministic.Basic
public import Complexity.Resources.StackMachine.TuringMachine

/-!
# Complexity classes shared by stack and Turing machines

Space comparisons assume an eventually positive bound because each Turing work tape
counts its initial cell, while an empty stack contributes zero symbols.
-/

@[expose] public section

namespace Complexity.StackMachine

variable {α β : Type*} [Encoding (RawWord Bool) α] [Encoding (RawWord Bool) β]

/-- Constant-factor simulations identify every asymptotic time class. -/
theorem fdtime_eq_tm (T : ℕ → ℕ) :
    FDTIME (α := α) (β := β) .stack T = FDTIME .tm T := by
  apply Set.Subset.antisymm
  · rintro f ⟨t, ⟨s, h⟩, ht⟩
    obtain ⟨c, h⟩ := TimeSpaceModel.ComputableWithinByCode.toTM h
    exact ⟨t, ⟨fun n => c * (s n + 1), h⟩, ht⟩
  · rintro f ⟨t, ⟨s, h⟩, ht⟩
    exact ⟨t, ⟨fun n => 2 * s n, TimeSpaceModel.ComputableWithinByCode.toStack_of_tm h⟩, ht⟩

/-- Both simulations preserve simultaneous time and eventually positive space bounds. -/
theorem fdtisp_eq_tm (T S : ℕ → ℕ) (hS : DominatedAtTop (fun _ ↦ 1) S) :
    FDTISP (α := α) (β := β) .stack T S = FDTISP .tm T S := by
  apply Set.Subset.antisymm
  · rintro f ⟨t, s, h, ht, hs⟩
    obtain ⟨c, h⟩ := TimeSpaceModel.ComputableWithinByCode.toTM h
    exact ⟨t, fun n => c * (s n + 1), h, ht, (hs.add_same hS).const_mul_left c⟩
  · rintro f ⟨t, s, h, ht, hs⟩
    exact ⟨t, fun n => 2 * s n, TimeSpaceModel.ComputableWithinByCode.toStack_of_tm h, ht,
      hs.const_mul_left 2⟩

/-- Eventually positive asymptotic space classes agree. -/
theorem fdspace_eq_tm (S : ℕ → ℕ) (hS : DominatedAtTop (fun _ ↦ 1) S) :
    FDSPACE (α := α) (β := β) .stack S = FDSPACE .tm S := by
  apply Set.Subset.antisymm
  · rintro f ⟨s, ⟨t, h⟩, hs⟩
    exact FDTISP.subset_space ((fdtisp_eq_tm t S hS).subset
      (h.mem_fdtisp_of_dominated (DominatedAtTop.refl _) hs))
  · rintro f ⟨s, ⟨t, h⟩, hs⟩
    exact FDTISP.subset_space ((fdtisp_eq_tm t S hS).superset
      (h.mem_fdtisp_of_dominated (DominatedAtTop.refl _) hs))

/-- Stack and Turing machines compute the same polynomial-time functions. -/
theorem fp_eq_tm :
    FP (α := α) (β := β) .stack = FP .tm :=
  Set.iUnion_congr fun _ ↦ fdtime_eq_tm _

theorem dtime_eq_tm (T : ℕ → ℕ) :
    DTIME (α := α) .stack T = DTIME .tm T :=
  congrArg DecisionClass (fdtime_eq_tm T)

theorem dtisp_eq_tm (T S : ℕ → ℕ) (hS : DominatedAtTop (fun _ ↦ 1) S) :
    DTISP (α := α) .stack T S = DTISP .tm T S :=
  congrArg DecisionClass (fdtisp_eq_tm T S hS)

theorem dspace_eq_tm (S : ℕ → ℕ) (hS : DominatedAtTop (fun _ ↦ 1) S) :
    DSPACE (α := α) .stack S = DSPACE .tm S :=
  congrArg DecisionClass (fdspace_eq_tm S hS)

theorem p_eq_tm : P (α := α) .stack = P .tm :=
  congrArg DecisionClass fp_eq_tm

/-- Constant-factor simulations of every branch identify every nondeterministic time class. -/
theorem ntime_eq_ntm (T : ℕ → ℕ) :
    NTIME (α := α) .nstack T = NTIME .ntm T := by
  apply Set.Subset.antisymm
  · rintro p ⟨t, ⟨s, h⟩, ht⟩
    obtain ⟨c, h⟩ := TimeSpaceModel.NDecidableWithinByCode.toNTM h
    exact ⟨t, ⟨fun n => c * (s n + 1), h⟩, ht⟩
  · rintro p ⟨t, ⟨s, h⟩, ht⟩
    exact ⟨t, ⟨fun n => 2 * s n, TimeSpaceModel.NDecidableWithinByCode.toStack_of_ntm h⟩, ht⟩

/-- Both simulations preserve simultaneous time and eventually positive space bounds on every
branch. -/
theorem ntisp_eq_ntm (T S : ℕ → ℕ) (hS : DominatedAtTop (fun _ ↦ 1) S) :
    NTISP (α := α) .nstack T S = NTISP .ntm T S := by
  apply Set.Subset.antisymm
  · rintro p ⟨t, s, h, ht, hs⟩
    obtain ⟨c, h⟩ := TimeSpaceModel.NDecidableWithinByCode.toNTM h
    exact ⟨t, fun n => c * (s n + 1), h, ht, (hs.add_same hS).const_mul_left c⟩
  · rintro p ⟨t, s, h, ht, hs⟩
    exact ⟨t, fun n => 2 * s n, TimeSpaceModel.NDecidableWithinByCode.toStack_of_ntm h, ht,
      hs.const_mul_left 2⟩

/-- Eventually positive nondeterministic space classes agree. -/
theorem nspace_eq_ntm (S : ℕ → ℕ) (hS : DominatedAtTop (fun _ ↦ 1) S) :
    NSPACE (α := α) .nstack S = NSPACE .ntm S := by
  apply Set.Subset.antisymm
  · rintro p ⟨s, ⟨t, h⟩, hs⟩
    exact NTISP.subset_space ((ntisp_eq_ntm t S hS).subset
      (h.mem_ntisp_of_dominated (DominatedAtTop.refl _) hs))
  · rintro p ⟨s, ⟨t, h⟩, hs⟩
    exact NTISP.subset_space ((ntisp_eq_ntm t S hS).superset
      (h.mem_ntisp_of_dominated (DominatedAtTop.refl _) hs))

/-- Stack and Turing machines decide the same predicates in nondeterministic polynomial time. -/
theorem np_eq_ntm : NP (α := α) .nstack = NP .ntm :=
  Set.iUnion_congr fun _ ↦ ntime_eq_ntm _

end Complexity.StackMachine
