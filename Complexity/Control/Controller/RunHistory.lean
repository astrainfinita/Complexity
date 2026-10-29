/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.Controller.History.Basic

/-! # Bounded execution histories

A run records only selected actions. It stops when its fuel is exhausted or its controller
halts, preserving the interpreted choices in the target monad.
-/

@[expose] public section

universe u

namespace Complexity.Controller

variable {F : Type u → Type*} {Observation Q : Type*} {Action Config : Type u}
  [HasState Config Q] [Apply Config Action]

/-- Endpoint and stopping conditions for a bounded run. These conditions alone do not require
that the actions come from the controller's transition function. -/
structure RunConditions (M : Controller F Observation Action Q) (start : Config) (fuel : ℕ)
    (h : History Config Action) : Prop where
  first_eq : h.first = start
  length_le : h.length ≤ fuel
  stopped : h.length = fuel ∨ M.Halted h.last
  active : ∀ c ∈ h.configs.dropLast, ¬M.Halted c

namespace RunConditions

variable (M : Controller F Observation Action Q)

/-- No action is performed at zero fuel or an already halted configuration. -/
theorem nil (cfg : Config) (fuel : ℕ) (h : fuel = 0 ∨ M.Halted cfg) :
    M.RunConditions cfg fuel (History.nil cfg) where
  first_eq := rfl
  length_le := Nat.zero_le _
  stopped := h.elim (fun h ↦ Or.inl h.symm) Or.inr
  active c hc := by simp at hc

/-- Prefix an action to the continuation from its resulting configuration. -/
theorem cons (cfg : Config) (a : Action) (h : ¬M.Halted cfg) {fuel : ℕ}
    {tail : History Config Action} (ht : M.RunConditions (apply a cfg) fuel tail) :
    M.RunConditions cfg (fuel + 1) (History.cons cfg a tail ht.first_eq) where
  first_eq := History.cons_first _ _ _ _
  length_le := Nat.succ_le_succ ht.length_le
  stopped := by
    simpa only [History.cons_length, History.last_cons] using
      ht.stopped.imp_left (congrArg Nat.succ)
  active := by
    simpa only [History.configs_cons,
      List.dropLast_cons_of_ne_nil tail.configs_ne_nil, List.mem_cons, forall_eq_or_imp] using
      And.intro h ht.active

end RunConditions

variable [Observe Config Observation]

/-- Run for at most the supplied fuel, selecting each recorded action exactly once. -/
def runHistoryFromWith (m : Type u → Type*) [Monad m] [MonadLiftT F m]
    (M : Controller F Observation Action Q) (cfg : Config) (fuel : ℕ) :
    m (History Config Action) :=
  Subtype.val <$> runCertified cfg fuel
where
  /-- Internal recursion retaining the conditions needed by `History.cons`. -/
  runCertified (cfg : Config) :
      (fuel : ℕ) → m {h : History Config Action // M.RunConditions cfg fuel h}
    | 0 => pure ⟨History.nil cfg, RunConditions.nil M cfg 0 (Or.inl rfl)⟩
    | fuel + 1 =>
      if h : M.Halted cfg then pure ⟨History.nil cfg, RunConditions.nil M cfg _ (Or.inr h)⟩
      else do
        let a ← monadLift (M.transition (state cfg) (observe cfg))
        let tail ← runCertified (apply a cfg) fuel
        pure ⟨History.cons cfg a tail.val tail.property.first_eq,
          RunConditions.cons M cfg a h tail.property⟩

section Interpreted

variable (m : Type u → Type*) [Monad m] [MonadLiftT F m]
  (M : Controller F Observation Action Q)

/-- Every returned history satisfies the common bounded-run conditions. -/
theorem runHistoryFromWith_spec (cfg : Config) (fuel : ℕ) :
    Functor.Liftp (M.RunConditions cfg fuel) (M.runHistoryFromWith m cfg fuel) :=
  ⟨runHistoryFromWith.runCertified m M cfg fuel, rfl⟩

private theorem runCertified_of_halted (cfg : Config) (h : M.Halted cfg) (fuel : ℕ) :
    runHistoryFromWith.runCertified m M cfg fuel =
      pure ⟨History.nil cfg, RunConditions.nil M cfg fuel (Or.inr h)⟩ := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp only [runHistoryFromWith.runCertified, dite_eq_left h]

variable [LawfulApplicative m] in
@[simp] theorem runHistoryFromWith_zero (cfg : Config) :
    M.runHistoryFromWith m cfg 0 = pure (History.nil cfg) := by
  simp only [runHistoryFromWith, runHistoryFromWith.runCertified, map_pure]

variable [LawfulApplicative m] in
@[simp] theorem runHistoryFromWith_of_halted (cfg : Config) (h : M.Halted cfg) (fuel : ℕ) :
    M.runHistoryFromWith m cfg fuel = pure (History.nil cfg) := by
  simp only [runHistoryFromWith, runCertified_of_halted m M cfg h, map_pure]

variable [LawfulMonad m]

private theorem runFromWith_certified (p : History Config Action) (n : ℕ) :
    M.runFromWith m p n =
      (fun h ↦ (⟨p.first, p.actions ++ h.val.actions⟩ : History Config Action)) <$>
        runHistoryFromWith.runCertified m M p.last n := by
  induction n generalizing p with
  | zero => simp only [runFromWith_zero, runHistoryFromWith.runCertified, map_pure,
      History.nil_actions, List.append_nil]
  | succ n ih =>
    by_cases h : M.Halted p.last
    · rw [M.runFromWith_of_halted m p h, runCertified_of_halted m M p.last h]
      simp only [map_pure, History.nil_actions, List.append_nil]
    · rw [runFromWith_succ, runHistoryFromWith.runCertified, dite_eq_right h,
        M.stepWith_of_not_halted m p h]
      simp only [History.state_def, History.observe_def, bind_map_left, History.apply_def,
        map_bind, map_pure]
      congr 1
      funext a
      rw [ih, History.last_snoc, ← map_eq_pure_bind]
      simp only [History.snoc_first, History.snoc_actions, History.cons_actions,
        List.append_assoc, List.singleton_append]

@[simp] theorem last_runFromWith (p : History Config Action) (n : ℕ) :
    History.last <$> M.runFromWith m p n = M.runFromWith m p.last n := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
    by_cases h : M.Halted p.last
    · simp [M.runFromWith_of_halted m p h, M.runFromWith_of_halted m p.last h]
    · rw [runFromWith_succ, runFromWith_succ,
        M.stepWith_of_not_halted m p h, M.stepWith_of_not_halted m p.last h]
      simp only [History.state_def, History.observe_def, bind_map_left, map_bind, ih,
        History.apply_last]

@[simp] theorem runFromWith_nil (c : Config) (n : ℕ) :
    M.runFromWith m (History.nil (Action := Action) c) n =
      M.runHistoryFromWith m c n := by
  rw [runFromWith_certified, runHistoryFromWith]
  congr 1
  funext h
  exact History.nil_append c h.val h.property.first_eq

/-- Forgetting the history recovers the original padded execution. -/
@[simp] theorem last_runHistoryFromWith (cfg : Config) (fuel : ℕ) :
    History.last <$> M.runHistoryFromWith m cfg fuel = M.runFromWith m cfg fuel := by
  rw [← M.runFromWith_nil m cfg, M.last_runFromWith m, History.last_nil]

/-- Splitting the fuel continues the first segment with its existing history. -/
theorem runHistoryFromWith_add (cfg : Config) (n k : ℕ) :
    M.runHistoryFromWith m cfg (n + k) = (do
      let p ← M.runHistoryFromWith m cfg n
      M.runFromWith m p k) := by
  rw [← M.runFromWith_nil m cfg, M.runFromWith_add m, M.runFromWith_nil m]

end Interpreted

section Multiset

variable (M : Controller F Observation Action Q) [MonadLiftT F Multiset]

/-- Membership in the returned multiset supplies the bounded-run conditions. -/
theorem runHistoryFromWith_mem_spec (cfg : Config) (fuel : ℕ) {h : History Config Action}
    (hh : h ∈ M.runHistoryFromWith Multiset cfg fuel) : M.RunConditions cfg fuel h := by
  obtain ⟨certified, heq⟩ := M.runHistoryFromWith_spec Multiset cfg fuel
  rw [← heq] at hh
  obtain ⟨h, _, rfl⟩ := Multiset.mem_map.mp hh
  exact h.property

end Multiset

section Deterministic

variable (M : Controller Id Observation Action Q)

/-- The complete action history of deterministic bounded execution. -/
def runHistoryFrom (cfg : Config) (fuel : ℕ) : History Config Action :=
  (M.runHistoryFromWith Id cfg fuel).run

theorem runHistoryFrom_spec (cfg : Config) (fuel : ℕ) :
    M.RunConditions cfg fuel (M.runHistoryFrom cfg fuel) :=
  (runHistoryFromWith.runCertified Id M cfg fuel).run.property

@[simp] theorem first_runHistoryFrom (cfg : Config) (fuel : ℕ) :
    (M.runHistoryFrom cfg fuel).first = cfg := (M.runHistoryFrom_spec cfg fuel).first_eq

@[simp] theorem runHistoryFrom_zero (cfg : Config) :
    M.runHistoryFrom cfg 0 = History.nil cfg := rfl

@[simp] theorem runHistoryFrom_of_halted (cfg : Config) (h : M.Halted cfg) (fuel : ℕ) :
    M.runHistoryFrom cfg fuel = History.nil cfg :=
  congrArg Id.run (M.runHistoryFromWith_of_halted Id cfg h fuel)

theorem runHistoryFrom_succ_of_not_halted (cfg : Config) (h : ¬M.Halted cfg) (fuel : ℕ) :
    M.runHistoryFrom cfg (fuel + 1) =
      History.cons cfg (M.transition (state cfg) (observe cfg)).run
        (M.runHistoryFrom (apply (M.transition (state cfg) (observe cfg)).run cfg) fuel)
        (M.first_runHistoryFrom _ _) := by
  simp only [runHistoryFrom, runHistoryFromWith, runHistoryFromWith.runCertified,
    dite_eq_right h]
  rfl

@[simp] theorem last_runHistoryFrom (cfg : Config) (fuel : ℕ) :
    (M.runHistoryFrom cfg fuel).last = M.runFrom cfg fuel :=
  congrArg Id.run (M.last_runHistoryFromWith Id cfg fuel)

@[simp] theorem last_runFrom (p : History Config Action) (n : ℕ) :
    (M.runFrom p n).last = M.runFrom p.last n :=
  congrArg Id.run (M.last_runFromWith Id p n)

/-- Continuing an existing history appends the newly selected actions. -/
theorem runFrom_history (p : History Config Action) (n : ℕ) :
    M.runFrom p n = p.append (M.runHistoryFrom p.last n)
      (M.first_runHistoryFrom p.last n).symm :=
  congrArg Id.run (runFromWith_certified Id M p n)

@[simp] theorem runFrom_nil (c : Config) (n : ℕ) :
    M.runFrom (History.nil (Action := Action) c) n = M.runHistoryFrom c n :=
  congrArg Id.run (M.runFromWith_nil Id c n)

/-- Deterministic histories compose at the intermediate configuration. -/
theorem runHistoryFrom_add (cfg : Config) (n k : ℕ) :
    M.runHistoryFrom cfg (n + k) =
      let p := M.runHistoryFrom cfg n
      p.append (M.runHistoryFrom p.last k) (M.first_runHistoryFrom _ _).symm := by
  rw [runHistoryFrom, M.runHistoryFromWith_add Id]
  exact M.runFrom_history _ _

/-- More fuel after halting preserves the complete recorded history. -/
theorem runHistoryFrom_eq_of_halted (cfg : Config) {n k : ℕ}
    (h : M.Halted (M.runFrom cfg n)) (hn : n ≤ k) :
    M.runHistoryFrom cfg k = M.runHistoryFrom cfg n := by
  simpa only [runFrom_nil] using M.runFrom_eq_of_halted
    (History.nil (Action := Action) cfg) (by simpa using h) hn

/-- Running for the actual action count reaches the same endpoint as the supplied fuel. -/
theorem runFrom_length_runHistoryFrom (cfg : Config) (fuel : ℕ) :
    M.runFrom cfg (M.runHistoryFrom cfg fuel).length = M.runFrom cfg fuel := by
  induction fuel generalizing cfg with
  | zero => simp
  | succ fuel ih =>
    by_cases h : M.Halted cfg
    · simp [M.runHistoryFrom_of_halted cfg h, M.runFrom_of_halted cfg h]
    · rw [M.runHistoryFrom_succ_of_not_halted cfg h,
        History.cons_length, M.runFrom_succ, M.runFrom_succ]
      rw [M.step_of_not_halted cfg h, ih]

/-- Before the first halt, the action count equals the supplied fuel. -/
theorem length_runHistoryFrom_eq (cfg : Config) (n : ℕ)
    (h : ∀ i < n, ¬M.Halted (M.runFrom cfg i)) :
    (M.runHistoryFrom cfg n).length = n := by
  have hr := M.runHistoryFrom_spec cfg n
  refine hr.stopped.elim id fun hh ↦ le_antisymm hr.length_le (le_of_not_gt fun hlt ↦ ?_)
  exact h _ hlt (by simpa only [M.runFrom_length_runHistoryFrom, ← M.last_runHistoryFrom] using hh)

/-- Recorded configurations are exactly the states reached within the supplied fuel. -/
theorem mem_configs_runHistoryFrom (cfg : Config) (fuel : ℕ) (c : Config) :
    c ∈ (M.runHistoryFrom cfg fuel).configs ↔ ∃ i ≤ fuel, M.runFrom cfg i = c := by
  induction fuel generalizing cfg with
  | zero => simp [eq_comm]
  | succ fuel ih =>
    by_cases h : M.Halted cfg
    · simp [M.runHistoryFrom_of_halted cfg h, M.runFrom_of_halted cfg h,
        show ∃ i : ℕ, i ≤ fuel + 1 from ⟨0, Nat.zero_le _⟩, eq_comm]
    · rw [M.runHistoryFrom_succ_of_not_halted cfg h, History.configs_cons, List.mem_cons, ih]
      conv_rhs => simp only [← Nat.lt_succ_iff]; rw [Nat.exists_lt_succ_left]
      simp only [Nat.lt_succ_iff, runFrom_zero, M.runFrom_succ,
        M.step_of_not_halted cfg h, eq_comm]

end Deterministic

end Complexity.Controller
