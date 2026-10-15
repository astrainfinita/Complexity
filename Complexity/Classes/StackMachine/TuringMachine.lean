/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Classes.Deterministic
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
theorem ftime_eq_tm (T : ℕ → ℕ) :
    FTIME (α := α) (β := β) .stack T = FTIME .tm T := by
  apply Set.Subset.antisymm
  · rintro f ⟨t, ⟨s, R, ⟨κ, hκ, Q, hQ, M, rfl⟩, h⟩, ht⟩
    exact ⟨t, ⟨fun n => Fintype.card κ * (s n + 1), _,
      ⟨κ, hκ, _, inferInstance, M.toTM, rfl⟩, h.mono (fun hc => hc.toTM)⟩, ht⟩
  · rintro f ⟨t, ⟨s, R, ⟨κ, hκ, Q, hQ, M, rfl⟩, h⟩, ht⟩
    exact ⟨t, ⟨fun n => 2 * s n, _,
      ⟨_, inferInstance, _, inferInstance, M.toStack, rfl⟩,
      h.mono (fun hc => hc.toStack)⟩, ht⟩

/-- Both simulations preserve simultaneous time and eventually positive space bounds. -/
theorem ftisp_eq_tm (T S : ℕ → ℕ) (hS : DominatedAtTop (fun _ ↦ 1) S) :
    FTISP (α := α) (β := β) .stack T S = FTISP .tm T S := by
  apply Set.Subset.antisymm
  · rintro f ⟨t, s, ⟨R, ⟨κ, hκ, Q, hQ, M, rfl⟩, h⟩, ht, hs⟩
    exact ⟨t, fun n => Fintype.card κ * (s n + 1),
      ⟨_, ⟨κ, hκ, _, inferInstance, M.toTM, rfl⟩,
        h.mono (fun hc => hc.toTM)⟩, ht, (hs.add_same hS).const_mul_left _⟩
  · rintro f ⟨t, s, ⟨R, ⟨κ, hκ, Q, hQ, M, rfl⟩, h⟩, ht, hs⟩
    exact ⟨t, fun n => 2 * s n,
      ⟨_, ⟨_, inferInstance, _, inferInstance, M.toStack, rfl⟩,
        h.mono (fun hc => hc.toStack)⟩, ht, hs.const_mul_left 2⟩

/-- Eventually positive asymptotic space classes agree. -/
theorem fspace_eq_tm (S : ℕ → ℕ) (hS : DominatedAtTop (fun _ ↦ 1) S) :
    FSPACE (α := α) (β := β) .stack S = FSPACE .tm S := by
  apply Set.Subset.antisymm
  · rintro f ⟨s, ⟨t, h⟩, hs⟩
    exact FTISP.subset_space ((ftisp_eq_tm t S hS).subset
      (h.mem_ftisp_of_dominated (DominatedAtTop.refl _) hs))
  · rintro f ⟨s, ⟨t, h⟩, hs⟩
    exact FTISP.subset_space ((ftisp_eq_tm t S hS).superset
      (h.mem_ftisp_of_dominated (DominatedAtTop.refl _) hs))

/-- Stack and Turing machines compute the same polynomial-time functions. -/
theorem fp_eq_tm :
    FP (α := α) (β := β) .stack = FP .tm :=
  Set.iUnion_congr fun _ ↦ ftime_eq_tm _

theorem dtime_eq_tm (T : ℕ → ℕ) :
    DTIME (α := α) .stack T = DTIME .tm T :=
  congrArg DecisionClass (ftime_eq_tm T)

theorem dtisp_eq_tm (T S : ℕ → ℕ) (hS : DominatedAtTop (fun _ ↦ 1) S) :
    DTISP (α := α) .stack T S = DTISP .tm T S :=
  congrArg DecisionClass (ftisp_eq_tm T S hS)

theorem dspace_eq_tm (S : ℕ → ℕ) (hS : DominatedAtTop (fun _ ↦ 1) S) :
    DSPACE (α := α) .stack S = DSPACE .tm S :=
  congrArg DecisionClass (fspace_eq_tm S hS)

theorem p_eq_tm : P (α := α) .stack = P .tm :=
  congrArg DecisionClass fp_eq_tm

end Complexity.StackMachine
