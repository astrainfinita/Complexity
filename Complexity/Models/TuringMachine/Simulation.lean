/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TuringMachine.Deterministic
public import Complexity.Control.Transition.Cost

/-!
# Composition of deterministic simulations

An execution block records an actual bounded run of the target machine. Sequential blocks
compose by adding their time bounds and taking the union of their visited work cells.
Consequently, adding their space bounds is always sound, even when the blocks visit disjoint
parts of the same tape.

The simulation interface below assembles implementations of individual source steps. Its
hypotheses include those implementations; it does not construct a compiler or impose a
particular encoding of source configurations.
-/

@[expose] public section

namespace Complexity.TM

variable {κ : Type*} {Γ Q : Type*} [Inhabited Γ] {xs ys : Array Γ}
  {M : TM Id κ Γ Q}

/-- Each step contributes at most one newly visited cell per work tape. -/
theorem spaceUsed_le_time [Fintype κ] (M : TM Id κ Γ Q) (c : Cfg κ Γ Q xs) (t : ℕ) :
    M.spaceUsed c t ≤ Fintype.card κ * (t + 1) := by
  calc
    M.spaceUsed c t ≤ ∑ _ : κ, (t + 1) := by
      rw [spaceUsed_eq_sum_visited]
      apply Finset.sum_le_sum
      intro i _
      exact (Finset.card_image_le).trans (by simp)
    _ = Fintype.card κ * (t + 1) := by simp

/-- Sequential runs visit the union of the cells visited by their two blocks. -/
theorem visited_add (M : TM Id κ Γ Q) (c : Cfg κ Γ Q xs)
    (s t : ℕ) (i : κ) :
    M.visited c (s + t) i = M.visited c s i ∪ M.visited (M.runFrom c s) t i := by
  ext j
  constructor
  · intro hj
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hj
    have hu' : u ≤ s + t := by
      have := Finset.mem_range.mp hu
      omega
    by_cases hs : u ≤ s
    · exact Finset.mem_union.mpr (.inl (Finset.mem_image.mpr
        ⟨u, Finset.mem_range.mpr (by omega), rfl⟩))
    · apply Finset.mem_union.mpr
      right
      refine Finset.mem_image.mpr ⟨u - s, Finset.mem_range.mpr (by omega), ?_⟩
      rw [Controller.runFrom_runFrom, Nat.add_sub_of_le (by omega : s ≤ u)]
  · intro hj
    rcases Finset.mem_union.mp hj with hj | hj
    · exact M.visited_mono c (Nat.le_add_right s t) i hj
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hj
      refine Finset.mem_image.mpr ⟨s + u, Finset.mem_range.mpr ?_, ?_⟩
      · have := Finset.mem_range.mp hu
        omega
      · rw [Controller.runFrom_runFrom]

/-- Space of sequential blocks is bounded by the sum, not merely the maximum, of their bounds. -/
theorem spaceUsed_add_le [Fintype κ] (M : TM Id κ Γ Q) (c : Cfg κ Γ Q xs) (s t : ℕ) :
    M.spaceUsed c (s + t) ≤ M.spaceUsed c s + M.spaceUsed (M.runFrom c s) t := by
  simp only [spaceUsed_eq_sum_visited, visited_add, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun _ _ ↦ Finset.card_union_le _ _

/-- A single set of absolute tape positions bounds the space of a complete execution. -/
theorem spaceUsed_le_of_visited_subset [Fintype κ] (M : TM Id κ Γ Q)
    (c : Cfg κ Γ Q xs) (t : ℕ) (F : κ → Finset ℤ)
    (h : ∀ i, M.visited c t i ⊆ F i) :
    M.spaceUsed c t ≤ ∑ i, (F i).card := by
  rw [spaceUsed_eq_sum_visited]
  exact Finset.sum_le_sum fun i _ ↦ Finset.card_le_card (h i)

/-- A common absolute footprint is preserved by concatenation. -/
theorem visited_add_subset_iff (M : TM Id κ Γ Q) (c : Cfg κ Γ Q xs)
    (s t : ℕ) (i : κ) (F : Finset ℤ) :
    M.visited c (s + t) i ⊆ F ↔
      M.visited c s i ⊆ F ∧ M.visited (M.runFrom c s) t i ⊆ F := by
  rw [visited_add, Finset.union_subset_iff]

/-- Blocks sharing a fixed footprint need not pay its cardinality repeatedly. -/
theorem spaceUsed_add_le_of_visited_subset [Fintype κ] (M : TM Id κ Γ Q)
    (c : Cfg κ Γ Q xs) (s t : ℕ) (F : κ → Finset ℤ)
    (h : ∀ i, M.visited c s i ⊆ F i)
    (h' : ∀ i, M.visited (M.runFrom c s) t i ⊆ F i) :
    M.spaceUsed c (s + t) ≤ ∑ i, (F i).card := by
  apply M.spaceUsed_le_of_visited_subset
  intro i
  exact (M.visited_add_subset_iff c s t i (F i)).mpr ⟨h i, h' i⟩

/-- An execution block reaches `d` within `t` steps while visiting at most `s` work cells. -/
def ReachesInTimeAndSpace [Fintype κ] (M : TM Id κ Γ Q) (c d : Cfg κ Γ Q xs)
    (t s : ℕ) : Prop :=
  ∃ n ≤ t, M.runFrom c n = d ∧ M.spaceUsed c n ≤ s

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
  · have h := M.spaceUsed_add_le c n n'
    rw [he] at h
    exact h.trans (Nat.add_le_add hc hc')

/-- A halted endpoint can be padded to the advertised time bound without extra space. -/
theorem computesInTimeAndSpace {xs ys : List Γ} {d : Cfg κ Γ Q xs.toArray}
    (h : M.ReachesInTimeAndSpace (M.initInput xs) d t s)
    (hd : M.Halted d) (ho : d.output = ys.toArray) :
    M.ComputesInTimeAndSpace xs ys t s := by
  obtain ⟨n, hn, he, hc⟩ := h
  have hh : M.Halted (M.run (Cfg κ Γ Q xs.toArray) xs n) := by
    rw [Controller.run, he]
    exact hd
  have ht : M.run (Cfg κ Γ Q xs.toArray) xs t = d :=
    (M.run_eq_of_halted xs hh hn).trans he
  refine ⟨ht.symm ▸ hd, ht.symm ▸ ho, ?_⟩
  rw [M.spaceUsed_eq_of_halted _ hh hn]
  exact hc

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
    ∃ d, R ((Transition.runN (m := Id) (pure ∘ f) n a).run) d ∧
      M.ReachesInTimeAndSpace c d
        (Transition.runCost f (fun a _ ↦ τ a) n a)
        (Fintype.card κ + Transition.runCost f (fun a _ ↦ σ a) n a) := by
  induction n generalizing a c with
  | zero => exact ⟨c, hc, ReachesInTimeAndSpace.refl M c⟩
  | succ n ih =>
    obtain ⟨d, hd, hb⟩ := h a c hc
    obtain ⟨e, he, hb'⟩ := ih (f a) d hd
    refine ⟨e, he, ?_⟩
    simpa only [Transition.runCost_succ, Nat.add_assoc, Nat.add_left_comm]
      using hb.trans hb'

/-- Uniform bounds on individual blocks give linear bounds in the number of source steps. -/
theorem Simulates.runN_const [Fintype κ] {t s : ℕ}
    (h : M.Simulates f R (fun _ ↦ t) (fun _ ↦ s)) (n : ℕ) (a : α)
    (c : Cfg κ Γ Q xs) (hc : R a c) :
    ∃ d, R ((Transition.runN (m := Id) (pure ∘ f) n a).run) d ∧
      M.ReachesInTimeAndSpace c d (n * t) (Fintype.card κ + n * s) := by
  induction n generalizing a c with
  | zero => exact ⟨c, hc, by simpa using ReachesInTimeAndSpace.refl M c⟩
  | succ n ih =>
    obtain ⟨d, hd, hb⟩ := h a c hc
    obtain ⟨e, he, hb'⟩ := ih (f a) d hd
    refine ⟨e, he, ?_⟩
    simpa only [Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using hb.trans hb'

/-- Initialization, implementations of source steps, and final output production give a
complete target computation. Every hypothesis concerns actual runs of `M`. -/
theorem computesInTimeAndSpace_of_simulates [Fintype κ] {xs ys : List Γ}
    {R : α → Cfg κ Γ Q xs.toArray → Prop} (h : M.Simulates f R τ σ)
    (a : α) (n ti si tf sf : ℕ)
    (hi : ∃ c, R a c ∧ M.ReachesInTimeAndSpace (M.initInput xs) c ti si)
    (ho : ∀ c, R ((Transition.runN (m := Id) (pure ∘ f) n a).run) c →
      ∃ d, M.Halted d ∧ d.output = ys.toArray ∧ M.ReachesInTimeAndSpace c d tf sf) :
    M.ComputesInTimeAndSpace xs ys
      (ti + Transition.runCost f (fun a _ ↦ τ a) n a + tf)
      (si + (Fintype.card κ + Transition.runCost f (fun a _ ↦ σ a) n a) + sf) := by
  obtain ⟨c, hc, hi⟩ := hi
  obtain ⟨d, hd, hm⟩ := h.runN n a c hc
  obtain ⟨e, he, hy, ho⟩ := ho d hd
  exact ((hi.trans hm).trans ho).computesInTimeAndSpace he hy

end Complexity.TM
