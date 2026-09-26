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
compose by adding their time bounds and joining their recorded visit intervals.
Their visit intervals share the head positions at the boundary, so adding their space
bounds is sound.

The simulation interface below assembles implementations of individual source steps. Its
hypotheses include those implementations; it does not construct a compiler or impose a
particular encoding of source configurations.
-/

@[expose] public section

namespace Complexity.TM

variable {κ : Type*} {Γ Q : Type*} [Inhabited Γ] {xs ys : Array Γ}
  {M : TM Id κ Γ Q}

/-- Each step contributes at most one newly visited cell per work tape. -/
theorem tracked_space_step_le [Fintype κ] (M : TM Id κ Γ Q) (s : TrackedCfg κ Γ Q xs) :
    (M.step s).space ≤ s.space + Fintype.card κ := by
  calc
    _ ≤ ∑ i, (((s.visited i).snd + 1 - (s.visited i).fst).toNat + 1) := by
      apply Finset.sum_le_sum
      intro i _
      have hp := M.step_workPos_bounds s.cfg i
      have hv := s.head_mem i
      simp only [tracked_step_visited, Pi.sup_apply, NonemptyInterval.fst_sup,
        NonemptyInterval.snd_sup, NonemptyInterval.pure_fst, NonemptyInterval.pure_snd]
      omega
    _ = _ := by simp [Finset.sum_add_distrib, TrackedCfg.space]

/-- Fresh visit records count one initial cell per work tape. -/
theorem runConfigMaxFrom_track_le_time [Fintype κ] (M : TM Id κ Γ Q) (c : Cfg κ Γ Q xs) (t : ℕ) :
    M.runConfigMaxFrom TrackedCfg.space c.track t ≤ Fintype.card κ * (t + 1) := by
  rw [runConfigMaxFrom_tracked]
  calc
    _ ≤ c.track.space + Transition.runCost M.step (fun _ _ ↦ Fintype.card κ) t c.track :=
      Transition.potential_runN_le _ _ _ M.tracked_space_step_le t c.track
    _ = _ := by simp [Nat.mul_succ, Nat.mul_comm, Nat.add_comm]

private theorem interval_size_sup_le {u v : NonemptyInterval ℤ} {p : ℤ}
    (hu : p ∈ u) (hv : p ∈ v) :
    ((u ⊔ v).snd + 1 - (u ⊔ v).fst).toNat ≤
      (u.snd + 1 - u.fst).toNat + (v.snd + 1 - v.fst).toNat := by
  rcases hu with ⟨hu₁, hu₂⟩
  rcases hv with ⟨hv₁, hv₂⟩
  simp only [NonemptyInterval.fst_sup, NonemptyInterval.snd_sup]
  omega

/-- Space of sequential blocks is bounded by the sum of their fresh space bounds. -/
theorem runConfigMaxFrom_track_add_le [Fintype κ] (M : TM Id κ Γ Q) (c : Cfg κ Γ Q xs) (s t : ℕ) :
    M.runConfigMaxFrom TrackedCfg.space c.track (s + t) ≤
      M.runConfigMaxFrom TrackedCfg.space c.track s +
        M.runConfigMaxFrom TrackedCfg.space (M.runFrom c s).track t := by
  simp only [runConfigMaxFrom_tracked, TrackedCfg.space, tracked_runFrom_visited_add,
    Cfg.track_cfg, Pi.sup_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  exact interval_size_sup_le
    (by simpa [NonemptyInterval.mem_def] using (M.runFrom c.track s).head_mem i)
    (M.tracked_runFrom_visited_mono (M.runFrom c s).track (Nat.zero_le t) i)

/-- One common interval bound controls space without recounting shared cells. -/
theorem runConfigMaxFrom_le_of_visited_le [Fintype κ] (M : TM Id κ Γ Q)
    (s : TrackedCfg κ Γ Q xs) (n : ℕ) (V : κ → NonemptyInterval ℤ)
    (hn : (M.runFrom s n).visited ≤ V) :
    M.runConfigMaxFrom TrackedCfg.space s n ≤ ∑ i, ((V i).snd + 1 - (V i).fst).toNat := by
  rw [runConfigMaxFrom_tracked]
  exact TrackedCfg.space_le_of_visited_le _ V hn

/-- A block starts fresh visit records at `c` and reaches underlying configuration `d`. -/
def ReachesInTimeAndSpace [Fintype κ] (M : TM Id κ Γ Q) (c d : Cfg κ Γ Q xs)
    (t s : ℕ) : Prop :=
  ∃ n ≤ t, (M.runFrom c.track n).cfg = d ∧
    M.runConfigMaxFrom TrackedCfg.space c.track n ≤ s

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
  simp only [tracked_runFrom_cfg, Cfg.track_cfg] at he he'
  refine ⟨n + n', Nat.add_le_add hn hn', ?_, ?_⟩
  · rw [tracked_runFrom_cfg, Cfg.track_cfg, ← Controller.runFrom_runFrom, he, he']
  · have h := M.runConfigMaxFrom_track_add_le c n n'
    rw [he] at h
    exact h.trans (Nat.add_le_add hc hc')

/-- A halted endpoint can be padded to the advertised time bound without extra space. -/
theorem computesInTimeAndSpace {xs ys : List Γ} {d : Cfg κ Γ Q xs.toArray}
    (h : M.ReachesInTimeAndSpace (M.initInput xs) d t s)
    (hd : M.Halted d) (ho : d.output = ys.toArray) :
    M.ComputesInTimeAndSpace xs ys t s := by
  obtain ⟨n, hn, he, hc⟩ := h
  refine ⟨n, ?_, ?_, (M.runActionSumFrom_unit_le _ n).trans hn, hc⟩
  · exact (M.tracked_halted_iff _).mpr (he.symm ▸ hd)
  · exact (congrArg Cfg.output he).trans ho

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
  simpa only [Transition.runCost_const] using h.runN n a c hc

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
