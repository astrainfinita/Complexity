/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.BinaryChoice.Basic
public import Complexity.Control.Controller.Computation
public import Complexity.Control.Transition.Basic

/-!
# Binary-choice runs as choice sequences

A sequence of labels selects one alternative at every step. The values that a run can return in
the multiset interpretation are exactly the endpoints of such sequences. A halted configuration
ignores its label, so several sequences can describe the same path; membership, not
multiplicity, is what this correspondence preserves. Because every non-halted configuration has a
successor, a uniform length bound `t` on all histories implies every branch has already halted by
step `t` (`forall_halted_of_forall_length_le`, strengthening the general
`forall_halted_succ_of_forall_length_le`).
-/

@[expose] public section

universe u v

namespace Complexity.Controller

variable {Observation : Type*} {Action : Type u} {Q : Type v}
  (M : Controller BinaryChoice Observation Action Q)

section Config

variable {Config : Type (max u v)} [HasState Config Q] [Observe Config Observation]
  [Apply Config (Q × Action)]

/-- Follow the alternative with label `b`; a halted configuration is unchanged. -/
def stepAlong (c : Config) (b : Fin 2) : Config :=
  if M.halt (state c) then c else apply (M.transition (state c) (observe c) b) c

theorem stepAlong_of_halted {c : Config} (h : M.Halted c) (b : Fin 2) :
    M.stepAlong c b = c := ite_eq_left h

theorem stepAlong_of_not_halted {c : Config} (h : ¬M.Halted c) (b : Fin 2) :
    M.stepAlong c b = apply (M.transition (state c) (observe c) b) c := ite_eq_right h

/-- One multiset step can return exactly the successors along the two labels. -/
theorem mem_returns_stepWith_multiset_iff (c d : Config) :
    d ∈ returns (M.stepWith Multiset c) ↔ ∃ b, M.stepAlong c b = d := by
  by_cases h : M.Halted c
  · rw [M.stepWith_of_halted Multiset c h, mem_returns_pure_iff]
    simp only [M.stepAlong_of_halted h, exists_const, eq_comm]
  · rw [M.stepWith_of_not_halted Multiset c h, mem_returns_map_iff]
    simp [M.stepAlong_of_not_halted h, Fin.exists_fin_two]

/-- A bounded multiset run can return exactly the endpoints of label sequences of that length. -/
theorem mem_returns_runFromWith_multiset_iff (c d : Config) (n : ℕ) :
    d ∈ returns (M.runFromWith Multiset c n) ↔
      ∃ bs : Fin n → Fin 2, (List.ofFn bs).foldl M.stepAlong c = d :=
  Transition.mem_returns_runN_iff _ _ M.mem_returns_stepWith_multiset_iff c d n

end Config

/-- Standard-input runs can return exactly the endpoints of label sequences from the initial
configuration. -/
theorem mem_returns_runWith_multiset_iff {Input : Type*} {Config : Input → Type u}
    [∀ x, Observe (Config x) Observation] [∀ x, Apply (Config x) Action]
    [HasConfig Action Input Config] (input : Input) (d : Q × Config input) (n : ℕ) :
    d ∈ returns (M.runWith Multiset input n) ↔
      ∃ bs : Fin n → Fin 2, (List.ofFn bs).foldl M.stepAlong (M.init input) = d :=
  M.mem_returns_runFromWith_multiset_iff _ d n

/-- For a binary-choice controller, every non-halted configuration has a successor, so a length
bound `t` on all histories implies every branch returned at step `t` has already halted,
strengthening `forall_halted_succ_of_forall_length_le` from `t + 1` to `t`. -/
theorem forall_halted_of_forall_length_le {Input : Type*} {Config : Input → Type u}
    [∀ x, Observe (Config x) Observation] [∀ x, Apply (Config x) Action]
    [HasConfig Action Input Config] (input : Input) {t : ℕ}
    (hl : ∀ h ∈ M.histories Multiset input, h.length ≤ t) :
    ∀ c ∈ returns (M.runWith Multiset input t), M.Halted c := by
  intro c hc
  rw [← M.last_runHistoryWith Multiset, mem_returns_map_iff] at hc
  obtain ⟨h, hh, rfl⟩ := hc
  by_contra hnh
  have hlen : h.length = t :=
    (M.runHistoryFromWith_spec Multiset (M.init input) t h hh).stopped.resolve_right hnh
  have hsucc : M.stepAlong h 0 ∈ returns (M.runHistoryWith Multiset input (t + 1)) := by
    rw [runHistoryWith, runHistoryFromWith, runFromWith_succ', mem_returns_bind_iff]
    exact ⟨h, hh, (M.mem_returns_stepWith_multiset_iff h _).2 ⟨0, rfl⟩⟩
  have hle := hl _ ((M.mem_histories_iff Multiset input).2 ⟨t + 1, hsucc⟩)
  rw [M.stepAlong_of_not_halted (c := h) hnh, History.apply_def, History.snoc_length] at hle
  omega

end Complexity.Controller
