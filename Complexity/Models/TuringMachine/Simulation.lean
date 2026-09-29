/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TuringMachine.Deterministic
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Composition of deterministic simulations

An execution block records an actual bounded run of the target machine. Sequential blocks
compose by adding their time bounds and joining their recorded visit intervals.
Their visit intervals share the head positions at the boundary, so adding their space
bounds is sound.

The simulation interface below assembles implementations of individual source steps. Its
hypotheses include those implementations; it does not construct a compiler or impose a
particular encoding of source configurations.
-/

@[expose] public section

namespace Complexity.TM

open Controller (History)

variable {κ : Type*} {Γ Q : Type*} [Inhabited Γ] {xs ys : Array Γ}
  {M : TM Id κ Γ Q}

/-- Concatenating execution segments combines their visited intervals. -/
theorem runHistoryFrom_space_add_le [Fintype κ] (M : TM Id κ Γ Q)
    (c : Cfg κ Γ Q xs) (s t : ℕ) :
    (M.runHistoryFrom c (s + t)).space ≤
      (M.runHistoryFrom c s).space + (M.runHistoryFrom (M.runFrom c s) t).space := by
  rw [Controller.runHistoryFrom_add]
  exact (History.space_append_le _ _ _).trans_eq (by rw [M.last_runHistoryFrom])

/-- A segment starts at `c`, reaches `d`, and bounds its own visited cells. -/
def ReachesInTimeAndSpace [Fintype κ] (M : TM Id κ Γ Q) (c d : Cfg κ Γ Q xs)
    (t s : ℕ) : Prop :=
  ∃ n ≤ t, M.runFrom c n = d ∧ (M.runHistoryFrom c n).space ≤ s

namespace ReachesInTimeAndSpace

variable [Fintype κ]

variable {c d e : Cfg κ Γ Q xs} {t s u v : ℕ}

/-- Even a zero-step block includes the initial head position of each work tape. -/
theorem refl (M : TM Id κ Γ Q) (c : Cfg κ Γ Q xs) :
    M.ReachesInTimeAndSpace c c 0 (Fintype.card κ) :=
  ⟨0, le_rfl, rfl, by simp⟩

theorem mono (h : M.ReachesInTimeAndSpace c d t s) (ht : t ≤ u) (hs : s ≤ v) :
    M.ReachesInTimeAndSpace c d u v := by
  obtain ⟨n, hn, he, hc⟩ := h
  exact ⟨n, hn.trans ht, he, hc.trans hs⟩

/-- Concatenate two actual blocks; both endpoints need not be halting configurations. -/
theorem trans (h : M.ReachesInTimeAndSpace c d t s)
    (h' : M.ReachesInTimeAndSpace d e u v) :
    M.ReachesInTimeAndSpace c e (t + u) (s + v) := by
  obtain ⟨n, hn, he, hc⟩ := h
  obtain ⟨n', hn', he', hc'⟩ := h'
  refine ⟨n + n', Nat.add_le_add hn hn', ?_, ?_⟩
  · rw [← Controller.runFrom_runFrom, he, he']
  · have h := M.runHistoryFrom_space_add_le c n n'
    rw [he] at h
    exact h.trans (Nat.add_le_add hc hc')

/-- A halted endpoint can be padded to the advertised time bound without extra space. -/
theorem computesInTimeAndSpace {xs ys : List Γ} {d : Cfg κ Γ Q xs.toArray}
    (h : M.ReachesInTimeAndSpace (M.initInput xs) d t s)
    (hd : M.Halted d) (ho : d.output = ys.toArray) :
    M.ComputesInTimeAndSpace xs ys t s := by
  obtain ⟨n, hn, rfl, hc⟩ := h
  exact ⟨n, hd, ho, (M.runHistory_spec _ _ n).length_le.trans hn, hc⟩

end ReachesInTimeAndSpace

variable {α : Type*} {f : α → α} {R : α → Cfg κ Γ Q xs → Prop} {τ σ : α → ℕ}

/-- Every source step has an implemented target block preserving `R`.
The two bounds may depend on the current source configuration. -/
def Simulates [Fintype κ] (M : TM Id κ Γ Q) (f : α → α)
    (R : α → Cfg κ Γ Q xs → Prop) (τ σ : α → ℕ) : Prop :=
  ∀ a c, R a c → ∃ d, R (f a) d ∧ M.ReachesInTimeAndSpace c d (τ a) (σ a)

/-- Concatenate the blocks implementing a finite source execution. -/
theorem Simulates.runN [Fintype κ] (h : M.Simulates f R τ σ) (n : ℕ) (a : α)
    (c : Cfg κ Γ Q xs) (hc : R a c) :
    ∃ d, R (f^[n] a) d ∧
      M.ReachesInTimeAndSpace c d
        (∑ i : Fin n, τ (f^[i.val] a))
        (Fintype.card κ + ∑ i : Fin n, σ (f^[i.val] a)) := by
  induction n generalizing a c with
  | zero => exact ⟨c, hc, ReachesInTimeAndSpace.refl M c⟩
  | succ n ih =>
    obtain ⟨d, hd, hb⟩ := h a c hc
    obtain ⟨e, he, hb'⟩ := ih (f a) d hd
    refine ⟨e, he, ?_⟩
    simpa [Fin.sum_univ_succ, Function.iterate_succ_apply, Nat.add_assoc, Nat.add_left_comm]
      using hb.trans hb'

/-- Uniform bounds on individual blocks give linear bounds in the number of source steps. -/
theorem Simulates.runN_const [Fintype κ] {t s : ℕ}
    (h : M.Simulates f R (fun _ ↦ t) (fun _ ↦ s)) (n : ℕ) (a : α)
    (c : Cfg κ Γ Q xs) (hc : R a c) :
    ∃ d, R (f^[n] a) d ∧
      M.ReachesInTimeAndSpace c d (n * t) (Fintype.card κ + n * s) := by
  simpa using h.runN n a c hc

/-- Initialization, implementations of source steps, and final output production give a
complete target computation. Every hypothesis concerns actual runs of `M`. -/
theorem computesInTimeAndSpace_of_simulates [Fintype κ] {xs ys : List Γ}
    {R : α → Cfg κ Γ Q xs.toArray → Prop} (h : M.Simulates f R τ σ)
    (a : α) (n ti si tf sf : ℕ)
    (hi : ∃ c, R a c ∧ M.ReachesInTimeAndSpace (M.initInput xs) c ti si)
    (ho : ∀ c, R (f^[n] a) c →
      ∃ d, M.Halted d ∧ d.output = ys.toArray ∧ M.ReachesInTimeAndSpace c d tf sf) :
    M.ComputesInTimeAndSpace xs ys
      (ti + (∑ i : Fin n, τ (f^[i.val] a)) + tf)
      (si + (Fintype.card κ + ∑ i : Fin n, σ (f^[i.val] a)) + sf) := by
  obtain ⟨c, hc, hi⟩ := hi
  obtain ⟨d, hd, hm⟩ := h.runN n a c hc
  obtain ⟨e, he, hy, ho⟩ := ho d hd
  exact ((hi.trans hm).trans ho).computesInTimeAndSpace he hy

end Complexity.TM
