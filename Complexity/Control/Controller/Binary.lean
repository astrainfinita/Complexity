/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.BinaryChoice.Basic
public import Complexity.Control.Controller.Computation
public import Complexity.Control.Controller.RunHistory

/-!
# Deterministic controllers as binary choices

Duplicating each deterministic action preserves reachable configurations.
The multiset interpretation retains the multiplicity of coincident paths.
-/

@[expose] public section

universe u v

namespace Complexity.Controller

variable {Observation : Type*} {Action : Type u} {Q : Type v} {Config : Type (max u v)}
variable (M : Controller Id Observation Action Q)
  [HasState Config Q]

/-- Embed a deterministic controller by giving both branch indices its unique action. -/
def toBinary : Controller BinaryChoice Observation Action Q where
  q₀ := M.q₀
  halt := M.halt
  transition q a _ := (M.transition q a).run

/-- Embedding a deterministic controller preserves its halting test. -/
@[simp] theorem halted_toBinary_iff (c : Config) :
    M.toBinary.Halted c ↔ M.Halted c := Iff.rfl

variable {Input : Type*}

/-- Duplicating transitions keeps the initial state. -/
@[simp] theorem toBinary_q₀ : M.toBinary.q₀ = M.q₀ := rfl

variable [Observe Config Observation] [Apply Config (Q × Action)]

/-- Both alternatives of an embedded deterministic step have the original successor. -/
@[simp] theorem mem_stepWith_toBinary_iff (c d : Config) :
    d ∈ M.toBinary.stepWith Multiset c ↔
      d = M.step c := by
  by_cases h : M.halt (state c) = true <;>
    simp [step, stepWith, toBinary, h]

/-- Embedding retains exactly the deterministic endpoint, possibly with several paths. -/
@[simp] theorem mem_runFromWith_toBinary_iff (c d : Config) (n : ℕ) :
    d ∈ M.toBinary.runFromWith Multiset c n ↔
      d = M.runFrom c n := by
  induction n generalizing c with
  | zero => exact Multiset.mem_singleton
  | succ n ih =>
    simp only [runFromWith_succ, runFrom_succ, Multiset.bind_def, Multiset.mem_bind,
      mem_stepWith_toBinary_iff, ih, exists_eq_left]

/-- Standard input execution reaches exactly the original deterministic endpoint. -/
@[simp] theorem mem_runWith_toBinary_iff {C : Input → Type u} [∀ x, Observe (C x) Observation]
    [∀ x, Apply (C x) Action] (input : Input) [HasConfig Action Input C] (d : Q × C input) (n : ℕ) :
    d ∈ M.toBinary.runWith Multiset input n ↔ d = M.run input n :=
  M.mem_runFromWith_toBinary_iff (M.init input) d n

/-- Every branch of the embedded machine has halted at step `n` exactly when the deterministic run
has. -/
theorem forall_halted_runWith_toBinary_iff {C : Input → Type u} [∀ x, Observe (C x) Observation]
    [∀ x, Apply (C x) Action] (input : Input) [HasConfig Action Input C] (n : ℕ) :
    (∀ c ∈ M.toBinary.runWith Multiset input n, M.toBinary.Halted c) ↔
      M.Halted (M.run input n) := by
  simp only [mem_runWith_toBinary_iff, forall_eq, halted_toBinary_iff]

/-- Duplicated deterministic choices record exactly the original action history. -/
theorem mem_runHistoryFromWith_toBinary_iff (c : Config)
    (h : History Config (Q × Action)) (n : ℕ) :
    h ∈ M.toBinary.runHistoryFromWith Multiset c n ↔ h = M.runHistoryFrom c n :=
  M.mem_runFromWith_toBinary_iff (History.nil c) h n

/-- Duplicated deterministic choices preserve standard-input histories. -/
theorem mem_runHistoryWith_toBinary_iff {C : Input → Type u} [∀ x, Observe (C x) Observation]
    [∀ x, Apply (C x) Action] (input : Input) [HasConfig Action Input C]
    (h : History (Q × C input) (Q × Action)) (n : ℕ) :
    h ∈ M.toBinary.runHistoryWith Multiset input n ↔ h = M.runHistory input n :=
  M.mem_runHistoryFromWith_toBinary_iff (M.init input) h n

/-- Duplicated deterministic choices have exactly the histories of the original run. -/
theorem forall_mem_histories_toBinary_iff {C : Input → Type u} [∀ x, Observe (C x) Observation]
    [∀ x, Apply (C x) Action] (input : Input) [HasConfig Action Input C]
    {P : History (Q × C input) (Q × Action) → Prop} :
    (∀ h ∈ M.toBinary.histories Multiset input, P h) ↔ ∀ n, P (M.runHistory input n) := by
  simp only [forall_mem_histories_iff, Multiset.mem_returns, mem_runHistoryWith_toBinary_iff,
    forall_eq]

/-- Duplicated deterministic choices compute, on every branch, the output of the original run. -/
theorem computesWith_toBinary {C : Input → Type u} [∀ x, Observe (C x) Observation]
    [∀ x, Apply (C x) Action] {input : Input} [HasConfig Action Input C]
    {Output : Type (max u v)} [∀ x, HasOutput (C x) Output] {output : Output} {n : ℕ}
    (hh : M.Halted (M.run input n)) (ho : HasOutput.IsOutput (M.run input n).2 output) :
    M.toBinary.ComputesWith Multiset input
      ((M.toBinary.runWith Multiset input n).map fun _ ↦ output) := by
  refine ⟨n, ?_⟩
  rw [liftRel_multiset_iff, Multiset.rel_map_right]
  refine Multiset.rel_refl_of_refl_on fun c hc ↦ ?_
  obtain rfl := (M.mem_runWith_toBinary_iff _ _ _).1 hc
  exact ⟨hh, ho⟩

end Complexity.Controller
