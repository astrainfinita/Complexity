/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.Data.Multiset.Functor
public import Complexity.Control.Transition.Basic

/-!
# Controllers over local observations and atomic actions

`F` describes one layer of permitted choices, independently of the monad used to
interpret a run. An action includes its destination control state. The concrete
model supplies configurations, their local observations, and action application.
No input/output representation or resource accounting is imposed here.

`stepWith` and `runFromWith` interpret choices in the target monad `m` through
`MonadLiftT F m`. Their deterministic counterparts `step` and `runFrom` use `Id`.
These interfaces and their execution laws are shared by all concrete storage models.

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

theorem stepWith_of_not_halted (M : Controller F Observation Action Q)
    (c : Config) (h : ¬M.Halted c) :
    M.stepWith m c = (fun a ↦ apply a c) <$>
      monadLift (M.transition (state c) (observe c)) := by
  simp only [stepWith, ite_eq_right (show M.halt (state c) ≠ true from h)]

/-- Execute a bounded number of steps in the target monad. -/
def runFromWith (M : Controller F Observation Action Q)
    (c : Config) (n : ℕ) : m Config :=
  Transition.runN (M.stepWith m) n c

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
  simpa only [← Multiset.bind_def, bind_pure] using
    Multiset.bind_congr fun d hd => M.runFromWith_of_halted Multiset d (h d hd) l

/-- A common halting deadline remains valid when increased. -/
theorem forall_halted_runFromWith_mono (c : Config) {n n' : ℕ}
    (h : ∀ d ∈ M.runFromWith Multiset c n, M.Halted d) (hn : n ≤ n') :
    ∀ d ∈ M.runFromWith Multiset c n', M.Halted d := by
  rw [M.runFromWith_eq_of_forall_halted c h hn]
  exact h

end Multiset

section Deterministic

variable (M : Controller Id Observation Action Q)

/-- Execute one deterministic transition; halted configurations are unchanged. -/
def step (c : Config) : Config :=
  (M.stepWith Id c).run

/-- A deterministic step either stays halted or applies the selected action. -/
theorem step_eq (c : Config) :
    M.step c = if M.halt (state c) then c
      else apply ((M.transition (state c) (observe c)).run) c := rfl

@[simp] theorem step_of_halted (c : Config) (h : M.Halted c) : M.step c = c :=
  congrArg Id.run (M.stepWith_of_halted Id c h)

theorem step_of_not_halted (c : Config) (h : ¬M.Halted c) :
    M.step c = apply ((M.transition (state c) (observe c)).run) c :=
  congrArg Id.run (M.stepWith_of_not_halted Id c h)

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

end Deterministic

end Controller
end Complexity
