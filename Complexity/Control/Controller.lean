/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.Data.Multiset.Functor
public import Complexity.Control.Transition
public import Mathlib.Data.List.Basic

/-!
# Controllers over local observations and atomic actions

`F` describes one layer of permitted choices, independently of the monad used to
interpret a run. An action includes its destination control state. The concrete
model supplies configurations, their local observations, and action application.
No input/output representation or resource accounting is imposed here.

`stepWith`, `runFromWith`, and `runTraceWith` interpret choices in the target monad `m`
through `MonadLiftT F m`.
Their deterministic counterparts `step`, `runFrom`, and `runTrace` use `Id`. Both
interfaces and their execution laws are shared by all concrete storage models.

Types are parameters, not fields. Concrete complexity classes impose finiteness
of control and observations and select their permitted atomic choice shape.
-/

@[expose] public section

universe u

namespace Complexity

/-- A controller selecting an atomic action from its state and local observation. -/
structure Controller (F : Type u → Type*) (Observation : Type*) (Action : Type u) (Q : Type*) where
  /-- Initial control state. -/
  q₀ : Q
  /-- Decide whether the current control state is halting. -/
  halt : Q → Bool
  /-- Select an atomic action from the state and permitted local observation. -/
  transition : Q → Observation → F Action

namespace Controller

/-- Read the control state of a configuration. -/
class HasState (Config : Type*) (Q : outParam Type*) where
  /-- Extract the current control state. -/
  state : Config → Q

/-- Read the local information available to a controller. -/
class Observe (Config Observation : Type*) where
  /-- Extract the local information visible to a controller. -/
  observe : Config → Observation

/-- Execute an atomic action on a configuration. -/
class Apply (Config Action : Type*) where
  /-- Update the configuration, including its control state, with one action. -/
  apply : Action → Config → Config

export HasState (state)
export Observe (observe)
export Apply (apply)

variable {F : Type u → Type*} {Observation : Type*} {Action : Type u} {Q : Type*}

/-- Halting depends only on finite control, independently of the storage model. -/
def Halted {Config : Type*} (M : Controller F Observation Action Q)
    [HasState Config Q] (c : Config) : Prop :=
  M.halt (state c) = true

instance {Config : Type*} (M : Controller F Observation Action Q)
    [HasState Config Q] (c : Config) : Decidable (M.Halted c) :=
  inferInstanceAs (Decidable (M.halt (state c) = true))

variable {Config : Type u} [HasState Config Q] [Observe Config Observation] [Apply Config Action]

section Interpreted

variable (m : Type u → Type*) [Monad m] [MonadLiftT F m]

/-- Interpret one layer of choices and apply the selected action.
Halted configurations do not perform a choice. -/
def stepWith (M : Controller F Observation Action Q)
    (c : Config) : m Config :=
  if M.halt (state c) then pure c
  else (fun a ↦ apply a c) <$> monadLift (M.transition (state c) (observe c))

@[simp] theorem stepWith_of_halted (M : Controller F Observation Action Q)
    (c : Config) (hc : M.halt (state c) = true) :
    M.stepWith m c = pure c := by
  simp [stepWith, hc]

/-- Execute a bounded number of steps in the target monad. -/
def runFromWith (M : Controller F Observation Action Q)
    (c : Config) (n : ℕ) : m Config :=
  Transition.runN (M.stepWith m) n c

/-- Record the initial configuration and each successor in the target monad. -/
def runTraceWith (M : Controller F Observation Action Q)
    (c : Config) (n : ℕ) : m (List Config) :=
  Transition.runTrace (M.stepWith m) n c

@[simp] theorem runFromWith_zero (M : Controller F Observation Action Q)
    (c : Config) : M.runFromWith m c 0 = pure c := rfl

theorem runFromWith_succ (M : Controller F Observation Action Q)
    (c : Config) (n : ℕ) :
    M.runFromWith m c (n + 1) =
      M.stepWith m c >>= fun d ↦ M.runFromWith m d n := rfl

section Lawful

variable [LawfulMonad m]

theorem runFromWith_add (M : Controller F Observation Action Q)
    (c : Config) (n l : ℕ) :
    M.runFromWith m c (n + l) =
      M.runFromWith m c n >>= fun d ↦ M.runFromWith m d l :=
  Transition.runN_add _ _ _ _

theorem runFromWith_succ' (M : Controller F Observation Action Q)
    (c : Config) (n : ℕ) :
    M.runFromWith m c (n + 1) = M.runFromWith m c n >>= M.stepWith m :=
  Transition.runN_succ' _ _ _

@[simp] theorem runFromWith_of_halted (M : Controller F Observation Action Q)
    (c : Config) (hc : M.halt (state c) = true) (n : ℕ) :
    M.runFromWith m c n = pure c :=
  Transition.runN_of_fixed _ (M.stepWith_of_halted m c hc) n

theorem getLastD_runTraceWith (M : Controller F Observation Action Q)
    (c : Config) (n : ℕ) :
    (fun cs ↦ cs.getLastD c) <$> M.runTraceWith m c n = M.runFromWith m c n :=
  Transition.getLastD_runTrace _ _ _ _

end Lawful
end Interpreted

section Multiset

variable (M : Controller F Observation Action Q)
    [MonadLiftT F Multiset]

/-- A path of length `n + l` splits at a reachable configuration after `n` steps. -/
theorem mem_runFromWith_add_iff (c d : Config) (n l : ℕ) :
    d ∈ M.runFromWith Multiset c (n + l) ↔
      ∃ b ∈ M.runFromWith Multiset c n,
        d ∈ M.runFromWith Multiset b l := by
  rw [runFromWith_add]
  exact Multiset.mem_bind

/-- A reachable halting configuration remains reachable at every later time. -/
theorem mem_runFromWith_of_halted (c : Config) {d : Config} {n n' : ℕ}
    (hd : d ∈ M.runFromWith Multiset c n) (hh : M.Halted d) (hn : n ≤ n') :
    d ∈ M.runFromWith Multiset c n' := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hn
  refine (M.mem_runFromWith_add_iff c d n l).2 ⟨d, hd, ?_⟩
  rw [M.runFromWith_of_halted Multiset d hh]
  exact Multiset.mem_singleton_self d

/-- Once every path has halted, the endpoint multiset is unchanged, including multiplicities. -/
theorem runFromWith_eq_of_forall_halted (c : Config) {n n' : ℕ}
    (h : ∀ d ∈ M.runFromWith Multiset c n, M.Halted d) (hn : n ≤ n') :
    M.runFromWith Multiset c n' = M.runFromWith Multiset c n := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [runFromWith_add]
  change (M.runFromWith Multiset c n).bind
    (fun d => M.runFromWith Multiset d l) = _
  calc
    _ = (M.runFromWith Multiset c n).bind (fun d => {d}) :=
      Multiset.bind_congr fun d hd => M.runFromWith_of_halted Multiset d (h d hd) l
    _ = _ := by
      rw [Multiset.bind_singleton]
      exact Multiset.map_id _

/-- A common halting deadline remains valid when increased. -/
theorem forall_halted_runFromWith_mono (c : Config) {n n' : ℕ}
    (h : ∀ d ∈ M.runFromWith Multiset c n, M.Halted d) (hn : n ≤ n') :
    ∀ d ∈ M.runFromWith Multiset c n', M.Halted d := by
  rw [M.runFromWith_eq_of_forall_halted c h hn]
  exact h

/-- The final configuration of a trace is a reachable endpoint. -/
theorem getLastD_mem_runFromWith_of_mem_runTraceWith (c : Config) {cs : List Config} {n : ℕ}
    (h : cs ∈ M.runTraceWith Multiset c n) :
    cs.getLastD c ∈ M.runFromWith Multiset c n := by
  rw [← M.getLastD_runTraceWith Multiset c n]
  exact Multiset.mem_map.mpr ⟨cs, h, rfl⟩

/-- A trace records its initial configuration and one configuration for each step. -/
theorem length_of_mem_runTraceWith (c : Config) {cs : List Config} {n : ℕ}
    (h : cs ∈ M.runTraceWith Multiset c n) : cs.length = n + 1 := by
  induction n generalizing c cs with
  | zero =>
    have hc : cs = [c] := by simpa [runTraceWith, Transition.runTrace] using h
    simp [hc]
  | succ n ih =>
    change cs ∈ (M.stepWith Multiset c).bind
      (fun d => (M.runTraceWith Multiset d n).bind (fun ds => {c :: ds})) at h
    simp only [Multiset.mem_bind, Multiset.mem_singleton] at h
    obtain ⟨d, _, ds, hd, rfl⟩ := h
    simp only [List.length_cons, ih d hd]

/-- Every execution trace contains at least its initial configuration. -/
theorem ne_nil_of_mem_runTraceWith (c : Config) {cs : List Config} {n : ℕ}
    (h : cs ∈ M.runTraceWith Multiset c n) : cs ≠ [] := by
  have hn := M.length_of_mem_runTraceWith c h
  intro hc
  simp [hc] at hn

end Multiset

section Deterministic

variable (M : Controller Id Observation Action Q)

/-- Execute one deterministic transition; halted configurations are unchanged. -/
def step (c : Config) : Config :=
  (M.stepWith Id c).run

@[simp] theorem step_of_halted (c : Config) (h : M.Halted c) : M.step c = c :=
  congrArg Id.run (M.stepWith_of_halted Id c h)

/-- Execute a bounded number of deterministic transitions from a configuration. -/
def runFrom (c : Config) (n : ℕ) : Config :=
  (M.runFromWith Id c n).run

@[simp] theorem runFrom_zero (c : Config) : M.runFrom c 0 = c := rfl

theorem runFrom_succ (c : Config) (n : ℕ) :
    M.runFrom c (n + 1) = M.runFrom (M.step c) n := rfl

theorem runFrom_add (c : Config) (n l : ℕ) :
    M.runFrom c (n + l) = M.runFrom (M.runFrom c n) l :=
  congrArg Id.run (M.runFromWith_add Id c n l)

theorem runFrom_succ' (c : Config) (n : ℕ) :
    M.runFrom c (n + 1) = M.step (M.runFrom c n) :=
  congrArg Id.run (M.runFromWith_succ' Id c n)

@[simp] theorem runFrom_of_halted (c : Config) (h : M.Halted c) (n : ℕ) :
    M.runFrom c n = c :=
  congrArg Id.run (M.runFromWith_of_halted Id c h n)

/-- Once a run halts, every later configuration is identical. -/
theorem runFrom_eq_of_halted (c : Config) {t u : ℕ}
    (h : M.Halted (M.runFrom c t)) (hu : t ≤ u) :
    M.runFrom c u = M.runFrom c t := by
  obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le hu
  rw [runFrom_add]
  exact M.runFrom_of_halted _ h v

/-- Sequential deterministic runs compose by adding their lengths. -/
theorem runFrom_runFrom (c : Config) (n l : ℕ) :
    M.runFrom (M.runFrom c n) l = M.runFrom c (n + l) :=
  (M.runFrom_add c n l).symm

/-- Record the initial configuration and every deterministic successor. -/
def runTrace (c : Config) (n : ℕ) : List Config :=
  (M.runTraceWith Id c n).run

/-- The last configuration in a deterministic trace is its bounded-run endpoint. -/
theorem getLastD_runTrace (c : Config) (n : ℕ) :
    (M.runTrace c n).getLastD c = M.runFrom c n :=
  congrArg Id.run (M.getLastD_runTraceWith Id c n)

end Deterministic

end Controller
end Complexity
