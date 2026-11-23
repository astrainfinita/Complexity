/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.Control.Monad.Basic
public import Mathlib.Data.Nat.Notation
public import Complexity.Control.Controller.Basic
public import Complexity.Control.LawfulFunctorLift

/-! # Controllers with internal states and exits

A control graph selects actions without a control state of its own in the configuration. Run
as a `Controller`, its internal states and exits become the control states, so a configuration
of the graph is the storage of the controller.

`Control.RunWithinWith Q` says that the runs of a graph within a budget of transitions, its
choices interpreted in a monad `m` and read by a quantifier `Q : MonadQuant m`, reach exits
satisfying a postcondition. It is a predicate defined by recursion on the budget, with no
outcome type: a run that has not reached an exit when the budget is spent satisfies nothing.
`Control.RunWithin` is its deterministic case.
-/

@[expose] public section

namespace Complexity.Program

/-- A controller with separate internal states and exits, whose transitions choose under the
shape `F`; deterministic control graphs use `F = Id`. -/
structure Control (F : Type → Type) (O A St E : Type) where
  /-- The initial internal state or immediate exit. -/
  start : St ⊕ E
  /-- One local action and the next internal state or exit, under the permitted choice shape. -/
  next : St → O → F (A × (St ⊕ E))

namespace Control

variable {O A St E St' E' S : Type}

/-- Run a control graph as a controller with the same choice shape. Its internal states and exits
are the control states, every exit halts, and each transition of the graph is one transition of
the controller. Exits never move, so `idle` only fills their transition. -/
@[simps q₀ halt]
def toController {F : Type → Type} [Functor F] [Pure F] (c : Control F O A St E) (idle : A) :
    Controller F O A (St ⊕ E) where
  q₀ := c.start
  halt := Sum.elim (fun _ ↦ false) (fun _ ↦ true)
  transition q v := match q with
    | .inl q => Prod.swap <$> c.next q v
    | .inr e => pure (.inr e, idle)

section Within

variable {F : Type → Type} {m : Type → Type} [Monad m] [MonadLiftT F m]

/-- The runs of a control graph within a budget of transitions, its choices interpreted in `m`,
that the quantifier `Q` reads reach an exit, where the exit, the storage and the remaining budget
satisfy `R`. Each transition charges one unit; a run at an internal state when the budget is
spent satisfies nothing. -/
def RunWithinWith (Q : MonadQuant m) (c : Control F O A St E) (observe : S → O)
    (act : A → S → S) (R : E → S → ℕ → Prop) : St ⊕ E → S → ℕ → Prop
  | .inr e, s, b => R e s b
  | .inl _, _, 0 => False
  | .inl q, s, b + 1 =>
      Q (fun r ↦ RunWithinWith Q c observe act R r.2 (act r.1 s) b)
        (monadLift (c.next q (observe s)) : m (A × (St ⊕ E)))

/-- Deterministic runs within a budget: the run reaches an exit within the budget, where the
exit, the storage and the remaining budget satisfy `R`. -/
abbrev RunWithin (c : Control Id O A St E) (observe : S → O) (act : A → S → S)
    (R : E → S → ℕ → Prop) : St ⊕ E → S → ℕ → Prop :=
  c.RunWithinWith (MonadQuant.all (m := Id)) observe act R

variable {Q : MonadQuant m} {c : Control F O A St E} {observe : S → O} {act : A → S → S}
  {R : E → S → ℕ → Prop} {q : St ⊕ E} {s : S} {b : ℕ}

@[simp] theorem runWithinWith_inr_iff {e : E} :
    c.RunWithinWith Q observe act R (.inr e) s b ↔ R e s b := by
  cases b <;> rfl

@[simp] theorem not_runWithinWith_inl_zero {q : St} :
    ¬ c.RunWithinWith Q observe act R (.inl q) s 0 :=
  id

theorem runWithinWith_inl_succ_iff {q : St} :
    c.RunWithinWith Q observe act R (.inl q) s (b + 1) ↔
      Q (fun r ↦ c.RunWithinWith Q observe act R r.2 (act r.1 s) b)
        (monadLift (c.next q (observe s)) : m (A × (St ⊕ E))) :=
  Iff.rfl

/-- A deterministic transition passes to the next label. -/
theorem runWithin_inl_succ_iff {c : Control Id O A St E} {q : St} :
    c.RunWithin observe act R (.inl q) s (b + 1) ↔
      c.RunWithin observe act R (c.next q (observe s)).run.2
        (act (c.next q (observe s)).run.1 s) b :=
  ⟨fun h ↦ h _ rfl, fun h _ hr ↦ hr ▸ h⟩

/-- A weaker postcondition holds of the same runs. -/
theorem RunWithinWith.mono {R' : E → S → ℕ → Prop} (h : c.RunWithinWith Q observe act R q s b)
    (hR : ∀ e t b', R e t b' → R' e t b') : c.RunWithinWith Q observe act R' q s b := by
  induction b generalizing q s with
  | zero => rcases q with q | e; exacts [h, hR _ _ _ h]
  | succ b ih =>
    rcases q with q | e
    · exact Q.mono (fun r hr ↦ ih hr) h
    · exact hR _ _ _ h

/-- An invariant indexed by the remaining budget, preserved by every action that costs one unit,
holds at the exit. -/
theorem RunWithinWith.inv {I : S → ℕ → Prop} (hI : ∀ a s b, I s (b + 1) → I (act a s) b)
    (h : c.RunWithinWith Q observe act R q s b) (hs : I s b) :
    c.RunWithinWith Q observe act (fun e t b' ↦ R e t b' ∧ I t b') q s b := by
  induction b generalizing q s with
  | zero => rcases q with q | e; exacts [h, ⟨h, hs⟩]
  | succ b ih =>
    rcases q with q | e
    · exact Q.mono (fun r hr ↦ ih hr (hI r.1 s b hs)) h
    · exact ⟨h, hs⟩

/-- Extra budget passes through a run unused. -/
theorem RunWithinWith.add_budget (h : c.RunWithinWith Q observe act R q s b) (r : ℕ) :
    c.RunWithinWith Q observe act (fun e t b' ↦ ∃ n, R e t n ∧ b' = n + r) q s (b + r) := by
  induction b generalizing q s with
  | zero =>
    rcases q with q | e
    · exact h.elim
    · exact runWithinWith_inr_iff.2 ⟨0, h, rfl⟩
  | succ b ih =>
    rcases q with q | e
    · rw [Nat.add_right_comm]
      exact Q.mono (fun r hr ↦ ih hr) h
    · exact runWithinWith_inr_iff.2 ⟨b + 1, h, rfl⟩

/-- A relation preserving observations and actions transports runs within a budget. -/
theorem RunWithinWith.simulate {T : Type} {observe' : T → O} {act' : A → T → T}
    (Rel : S → T → Prop) (ho : ∀ s t, Rel s t → observe' t = observe s)
    (ha : ∀ a s t, Rel s t → Rel (act a s) (act' a t))
    (h : c.RunWithinWith Q observe act R q s b) (u : T) (hu : Rel s u) :
    c.RunWithinWith Q observe' act' (fun e t' b' ↦ ∃ t, Rel t t' ∧ R e t b') q u b := by
  induction b generalizing q s u with
  | zero => rcases q with q | e; exacts [h, ⟨s, hu, h⟩]
  | succ b ih =>
    rcases q with q | e
    · rw [runWithinWith_inl_succ_iff, ho s u hu]
      exact Q.mono (fun r hr ↦ ih hr _ (ha r.1 s u hu)) h
    · exact ⟨s, hu, h⟩

/-- A deterministic run within a budget is an exact run, using up its own budget, followed by the
unused rest of the budget. -/
theorem RunWithin.exists_exact {c : Control Id O A St E}
    (h : c.RunWithin observe act R q s b) :
    ∃ n e t, n ≤ b ∧ c.RunWithin observe act (fun e' t' b' ↦ e' = e ∧ t' = t ∧ b' = 0) q s n ∧
      R e t (b - n) := by
  induction b generalizing q s with
  | zero =>
    rcases q with q | e
    · exact h.elim
    · exact ⟨0, e, s, le_rfl, ⟨rfl, rfl, rfl⟩, h⟩
  | succ b ih =>
    rcases q with q | e
    · obtain ⟨n, e, t, hn, he, hR⟩ := ih (runWithin_inl_succ_iff.1 h)
      exact ⟨n + 1, e, t, by omega, runWithin_inl_succ_iff.2 he, by rwa [Nat.add_sub_add_right]⟩
    · exact ⟨0, e, s, Nat.zero_le _, ⟨rfl, rfl, rfl⟩, h⟩

/-- Runs depend on the transition function, not on the graph's entry label. -/
theorem runWithinWith_congr_next {d : Control F O A St E} (hn : c.next = d.next) :
    c.RunWithinWith Q observe act R q s b ↔ d.RunWithinWith Q observe act R q s b := by
  induction b generalizing q s with
  | zero => rcases q with q | e <;> exact Iff.rfl
  | succ b ih =>
    rcases q with q | e
    · simp only [runWithinWith_inl_succ_iff, hn, ih]
    · exact Iff.rfl

variable [LawfulMonad m]

/-- Embedding a control graph and continuing at its exits substitutes the postcondition. -/
theorem runWithinWith_link_iff [Functor F] [LawfulFunctorLiftT F m] {d : Control F O A St' E'}
    (f : St → St') (g : E → St' ⊕ E')
    (hn : ∀ q o, d.next (f q) o =
      (fun r ↦ (r.1, Sum.elim (fun q ↦ Sum.inl (f q)) g r.2)) <$> c.next q o)
    {R : E' → S → ℕ → Prop} :
    d.RunWithinWith Q observe act R (Sum.elim (fun q ↦ Sum.inl (f q)) g q) s b ↔
      c.RunWithinWith Q observe act (fun e t b' ↦ d.RunWithinWith Q observe act R (g e) t b')
        q s b := by
  induction b generalizing q s with
  | zero => rcases q with q | e <;> exact Iff.rfl
  | succ b ih =>
    rcases q with q | e
    · simp only [Sum.elim_inl, runWithinWith_inl_succ_iff, hn, LawfulFunctorLiftT.monadLift_map,
        Q.map_iff, ih]
    · exact Iff.rfl

/-- Relabeling a control graph relabels the exits its postcondition receives. -/
theorem runWithinWith_relabel_iff [Functor F] [LawfulFunctorLiftT F m] {d : Control F O A St' E'}
    (f : St → St') (g : E → E')
    (hn : ∀ q o, d.next (f q) o = (fun r ↦ (r.1, Sum.map f g r.2)) <$> c.next q o)
    {R : E' → S → ℕ → Prop} :
    d.RunWithinWith Q observe act R (Sum.map f g q) s b ↔
      c.RunWithinWith Q observe act (fun e ↦ R (g e)) q s b := by
  have h := runWithinWith_link_iff (Q := Q) (observe := observe) (act := act) (q := q) (s := s)
    (b := b) (d := d) f (Sum.inr ∘ g)
    (fun q o ↦ by rw [hn]; exact congrArg (· <$> _) (funext fun r ↦ by cases r.2 <;> rfl))
    (R := R)
  rcases q with q | e
  · simpa using h
  · simp

/-- The controller of a control graph runs it within the budget: the quantifier holds of the
configurations it reaches after `b` steps, each at an exit satisfying `P`, exactly when the runs
of the graph within the budget reach such exits. -/
theorem runWithinWith_iff_runFromWith_toController [Functor F] [Pure F] [LawfulFunctorLiftT F m]
    {C : Type} [Controller.Observe C O] [Controller.Apply C A] (idle : A) {P : E → C → Prop}
    {q : St ⊕ E} {s : C} :
    c.RunWithinWith Q Controller.observe Controller.apply (fun e t _ ↦ P e t) q s b ↔
      Q (fun cfg ↦ ∃ e t, cfg = (.inr e, t) ∧ P e t)
        ((c.toController idle).runFromWith m (q, s) b) := by
  induction b generalizing q s with
  | zero =>
    rw [Controller.runFromWith_zero, Q.pure_iff]
    rcases q with q | e
    · exact iff_of_false id fun ⟨_, _, h, _⟩ ↦ by cases h
    · exact ⟨fun h ↦ ⟨e, s, rfl, h⟩, fun ⟨_, _, h, hP⟩ ↦ by cases h; exact hP⟩
  | succ b ih =>
    rcases q with q | e
    · rw [Controller.runFromWith_succ,
        Controller.stepWith_of_not_halted _ _ _ (by simp [Controller.Halted])]
      simp only [Controller.state_prod, Controller.observe_prod, toController,
        runWithinWith_inl_succ_iff]
      rw [LawfulFunctorLiftT.monadLift_map, Functor.map_map, bind_map_left, Q.bind_iff]
      exact ⟨Q.mono fun r hr ↦ ih.1 hr, Q.mono fun r hr ↦ ih.2 hr⟩
    · rw [(c.toController idle).runFromWith_of_halted m _ rfl, Q.pure_iff]
      exact ⟨fun h ↦ ⟨e, s, rfl, h⟩, fun ⟨_, _, h, hP⟩ ↦ by cases h; exact hP⟩

end Within

end Control

end Complexity.Program
