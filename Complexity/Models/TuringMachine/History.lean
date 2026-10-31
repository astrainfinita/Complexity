/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.Controller.History.Cost
public import Complexity.Models.TuringMachine.Configuration
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.Interval.Basic

/-! # Output and visited work cells of Turing-machine histories

The configurations of a history determine the nonempty interval visited on each work tape.
Both endpoints are included. No additional configuration or running visit record is needed.
-/

@[expose] public section

namespace Complexity.Controller.History

variable {κ Γ : Type*} [Inhabited Γ] {xs : Array Γ}

/-- The interval covered by the work-head positions, including both endpoints. -/
def visited (h : History (TM.Cfg κ Γ xs) (TM.Action κ Γ)) :
    κ → NonemptyInterval ℤ :=
  h.configSup fun c k ↦ NonemptyInterval.pure (c.workPos k)

/-- An interval bound holds exactly when it contains every recorded head position. -/
theorem visited_le_iff (h : History (TM.Cfg κ Γ xs) (TM.Action κ Γ))
    (V : κ → NonemptyInterval ℤ) :
    h.visited ≤ V ↔ ∀ c ∈ h.configs, ∀ k, c.workPos k ∈ V k :=
  h.configSup_le_iff _ V

theorem visited_apply_le_iff (h : History (TM.Cfg κ Γ xs) (TM.Action κ Γ))
    (k : κ) (V : NonemptyInterval ℤ) :
    h.visited k ≤ V ↔ ∀ c ∈ h.configs, c.workPos k ∈ V := by
  rw [visited, configSup_apply, configSup_le_iff]
  rfl

/-- Every recorded head lies in the history's visited interval. -/
theorem config_head_mem (h : History (TM.Cfg κ Γ xs) (TM.Action κ Γ))
    {c : TM.Cfg κ Γ xs} (hc : c ∈ h.configs) (k : κ) : c.workPos k ∈ h.visited k :=
  (h.visited_le_iff _).mp le_rfl c hc k

theorem first_head_mem (h : History (TM.Cfg κ Γ xs) (TM.Action κ Γ)) (k : κ) :
    h.first.workPos k ∈ h.visited k := h.config_head_mem h.first_mem_configs k

/-- The final heads belong to the visited intervals. -/
theorem head_mem (h : History (TM.Cfg κ Γ xs) (TM.Action κ Γ)) (k : κ) :
    h.last.workPos k ∈ h.visited k := h.config_head_mem h.last_mem_configs k

theorem head_mem_of_visited_le (h : History (TM.Cfg κ Γ xs) (TM.Action κ Γ))
    {V : κ → NonemptyInterval ℤ} (hv : h.visited ≤ V) (k : κ) :
    h.last.workPos k ∈ V k :=
  ⟨(hv k).1.trans (h.head_mem k).1, (h.head_mem k).2.trans (hv k).2⟩

@[simp] theorem visited_nil (c : TM.Cfg κ Γ xs) :
    (nil c).visited =
      fun k ↦ NonemptyInterval.pure (c.workPos k) := by
  simp [visited]

@[simp] theorem visited_cons (c : TM.Cfg κ Γ xs) (a : TM.Action κ Γ)
    (h : History (TM.Cfg κ Γ xs) (TM.Action κ Γ)) (he : h.first = apply a c) :
    (cons c a h he).visited = (fun k ↦ NonemptyInterval.pure (c.workPos k)) ⊔ h.visited :=
  configSup_cons _ _ _ _ _

/-- Joining segments joins their visited intervals, without resetting prior visits. -/
@[simp] theorem visited_append (p q : History (TM.Cfg κ Γ xs) (TM.Action κ Γ))
    (he : p.last = q.first) : (p.append q he).visited = p.visited ⊔ q.visited :=
  configSup_append _ _ _ _

/-- One action adds its new head positions to the recorded intervals. -/
@[simp] theorem visited_snoc (h : History (TM.Cfg κ Γ xs) (TM.Action κ Γ))
    (a : TM.Action κ Γ) :
    (h.snoc a).visited =
      h.visited ⊔ fun k ↦ NonemptyInterval.pure ((apply a h.last).workPos k) :=
  configSup_snoc _ _ _

@[simp↓] theorem apply_visited (a : TM.Action κ Γ)
    (h : History (TM.Cfg κ Γ xs) (TM.Action κ Γ)) :
    (apply a h).visited =
      h.visited ⊔ fun k ↦ NonemptyInterval.pure ((apply a h.last).workPos k) :=
  h.visited_snoc a

/-- An action preserves a common bound exactly when its new heads remain inside it. -/
theorem apply_visited_le_iff (a : TM.Action κ Γ)
    (h : History (TM.Cfg κ Γ xs) (TM.Action κ Γ)) (V : κ → NonemptyInterval ℤ) :
    (apply a h).visited ≤ V ↔
      h.visited ≤ V ∧ ∀ k, (apply a h.last).workPos k ∈ V k := by
  rw [apply_visited, sup_le_iff]
  rfl

/-- Total visited-cell space, computed from interval lengths. -/
def space [Fintype κ] (h : History (TM.Cfg κ Γ xs) (TM.Action κ Γ)) : ℕ :=
  ∑ k, ((h.visited k).snd + 1 - (h.visited k).fst).toNat

@[simp] theorem space_nil [Fintype κ] (c : TM.Cfg κ Γ xs) :
    (nil c).space = Fintype.card κ := by
  simp [space, NonemptyInterval.pure]

theorem space_le_of_visited_le [Fintype κ]
    (h : History (TM.Cfg κ Γ xs) (TM.Action κ Γ)) (V : κ → NonemptyInterval ℤ)
    (hv : h.visited ≤ V) : h.space ≤ ∑ k, ((V k).snd + 1 - (V k).fst).toNat := by
  apply Finset.sum_le_sum
  intro k _
  rcases hv k with ⟨hl, hr⟩
  omega

/-- Enlarging every visited interval cannot reduce space. -/
theorem space_mono [Fintype κ] {p q : History (TM.Cfg κ Γ xs) (TM.Action κ Γ)}
    (h : p.visited ≤ q.visited) : p.space ≤ q.space :=
  p.space_le_of_visited_le q.visited h

/-- A preceding action adds at most one visited cell on each tape. -/
theorem space_cons_le [Fintype κ] (c : TM.Cfg κ Γ xs) (a : TM.Action κ Γ)
    (h : History (TM.Cfg κ Γ xs) (TM.Action κ Γ)) (he : h.first = apply a c) :
    (cons c a h he).space ≤ h.space + Fintype.card κ := by
  rw [space, space, show Fintype.card κ = ∑ _ : κ, 1 by simp, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k _
  have hm := a.workPos_apply_bounds c k
  have hv := he ▸ h.first_head_mem k
  simp only [visited_cons, Pi.sup_apply, NonemptyInterval.fst_sup,
    NonemptyInterval.snd_sup, NonemptyInterval.pure_fst, NonemptyInterval.pure_snd]
  rcases hv with ⟨hl, hr⟩
  omega

/-- Each action adds at most one visited work cell per tape. -/
theorem space_le_length [Fintype κ]
    (h : History (TM.Cfg κ Γ xs) (TM.Action κ Γ)) :
    h.space ≤ Fintype.card κ * (h.length + 1) := by
  rcases h with ⟨c, as⟩
  induction as generalizing c with
  | nil =>
    change (nil c).space ≤ Fintype.card κ * (0 + 1)
    simp
  | cons a as ih =>
    exact (space_cons_le c a ⟨apply a c, as⟩ rfl).trans
      ((Nat.add_le_add_right (ih _) _).trans_eq (Nat.mul_succ _ _).symm)

end Complexity.Controller.History
