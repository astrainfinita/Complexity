/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Simulation.Layout
public import Complexity.Data.IntMemory.List
public import Complexity.Models.TuringMachine.Program.Word.Basic

/-! # Tape representations used by the tree compiler -/

@[expose] public section

namespace Complexity.TreeMachine.Simulation.Compiler

open TM.Program.Word

variable {k : ℕ} {Q : Type*}

/-- The two logical word banks in physical tape order, with an isolated nonblank counter origin. -/
def tapes (b : Bool) (ρ σ : Fin k → List Bool) (j : Fin (2 * k + 1)) : IntMemory (Option Bool) :=
  if h : j.val < k then tape (if b then σ ⟨j.val, h⟩ else ρ ⟨j.val, h⟩)
  else if h' : j.val < 2 * k then
    tape (if b then ρ ⟨j.val - k, by omega⟩ else σ ⟨j.val - k, by omega⟩)
  else IntMemory.ofList [some true]

@[simp] theorem tapes_data (b : Bool) (ρ σ : Fin k → List Bool) (i : Fin k) :
    tapes b ρ σ (data b i) = tape (ρ i) := by
  have hi := i.isLt
  cases b <;> simp [tapes, data, hi, show ¬k + i.val < k by omega,
    show k + i.val < 2 * k by omega]

@[simp] theorem tapes_other (b : Bool) (ρ σ : Fin k → List Bool) (i : Fin k) :
    tapes b ρ σ (data (!b) i) = tape (σ i) := by
  have hi := i.isLt
  cases b <;> simp [tapes, data, hi, show ¬k + i.val < k by omega,
    show k + i.val < 2 * k by omega]

@[simp] theorem tapes_counter (b : Bool) (ρ σ : Fin k → List Bool) :
    tapes b ρ σ (counter k) = IntMemory.ofList [some true] := by
  simp [tapes, counter, show ¬2 * k < k by omega]

theorem data_injective (b : Bool) : Function.Injective (data (k := k) b) := by
  intro i j h
  apply Fin.ext
  have h := congrArg Fin.val h
  cases b <;> simp [data] at h <;> omega

/-- Every physical work tape belongs to one of the two banks or is the counter. -/
theorem data_or_counter (b : Bool) (j : Fin (2 * k + 1)) :
    (∃ i, j = data b i) ∨ (∃ i, j = data (!b) i) ∨ j = counter k := by
  have hj := j.isLt
  by_cases h : j.val < k
  · have he : j = data false ⟨j.val, h⟩ := by apply Fin.ext; rfl
    cases b
    · exact .inl ⟨_, he⟩
    · exact .inr (.inl ⟨_, he⟩)
  · by_cases h' : j.val < 2 * k
    · have hi : j.val - k < k := by omega
      have he : j = data true ⟨j.val - k, hi⟩ := by apply Fin.ext; simp [data]; omega
      cases b
      · exact .inr (.inl ⟨_, he⟩)
      · exact .inl ⟨_, he⟩
    · right; right
      apply Fin.ext
      simp only [counter]
      omega

/-- Updating one destination word changes exactly its physical tape. -/
theorem tapes_update_other (b : Bool) (ρ σ : Fin k → List Bool) (i : Fin k)
    (w : List Bool) :
    tapes b ρ (Function.update σ i w) = Function.update (tapes b ρ σ) (data (!b) i) (tape w) := by
  funext j
  rcases data_or_counter b j with ⟨l, rfl⟩ | ⟨l, rfl⟩ | rfl
  · simp [data_ne_other]
  · by_cases h : l = i
    · subst l
      simp
    · have hd : data (!b) l ≠ data (!b) i := fun he ↦ h (data_injective (!b) he)
      simp [h, hd]
  · simp [(data_ne_counter (!b) i).symm]

/-- Exchanging the logical banks leaves all physical tape contents unchanged. -/
theorem tapes_swap (b : Bool) (ρ σ : Fin k → List Bool) : tapes (!b) σ ρ = tapes b ρ σ := by
  funext j
  cases b <;> simp [tapes]

end Complexity.TreeMachine.Simulation.Compiler
