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

/-! # Visited work cells of Turing-machine histories

The configurations of a history determine the nonempty interval visited on each work tape.
Both endpoints are included. No additional configuration or running visit record is needed.
-/

@[expose] public section

namespace Complexity.Controller.History

variable {κ Γ Q : Type*} [Inhabited Γ] {xs : Array Γ}

/-- The interval covered by the work-head positions, including both endpoints. -/
def visited (h : History (TM.Cfg κ Γ Q xs) (TM.Action κ Γ Q)) :
    κ → NonemptyInterval ℤ :=
  h.configSup fun c k ↦ NonemptyInterval.pure (c.workPos k)

/-- An interval bound holds exactly when it contains every recorded head position. -/
theorem visited_le_iff (h : History (TM.Cfg κ Γ Q xs) (TM.Action κ Γ Q))
    (V : κ → NonemptyInterval ℤ) :
    h.visited ≤ V ↔ ∀ c ∈ h.configs, ∀ k, c.workPos k ∈ V k :=
  h.configSup_le_iff _ V

theorem visited_apply_le_iff (h : History (TM.Cfg κ Γ Q xs) (TM.Action κ Γ Q))
    (k : κ) (V : NonemptyInterval ℤ) :
    h.visited k ≤ V ↔ ∀ c ∈ h.configs, c.workPos k ∈ V := by
  rw [visited, configSup_apply, configSup_le_iff]
  rfl

/-- Every recorded head lies in the history's visited interval. -/
theorem config_head_mem (h : History (TM.Cfg κ Γ Q xs) (TM.Action κ Γ Q))
    {c : TM.Cfg κ Γ Q xs} (hc : c ∈ h.configs) (k : κ) : c.workPos k ∈ h.visited k :=
  (h.visited_le_iff _).mp le_rfl c hc k

theorem first_head_mem (h : History (TM.Cfg κ Γ Q xs) (TM.Action κ Γ Q)) (k : κ) :
    h.first.workPos k ∈ h.visited k := h.config_head_mem h.first_mem_configs k

/-- The final heads belong to the visited intervals. -/
theorem head_mem (h : History (TM.Cfg κ Γ Q xs) (TM.Action κ Γ Q)) (k : κ) :
    h.last.workPos k ∈ h.visited k := h.config_head_mem h.last_mem_configs k

theorem head_mem_of_visited_le (h : History (TM.Cfg κ Γ Q xs) (TM.Action κ Γ Q))
    {V : κ → NonemptyInterval ℤ} (hv : h.visited ≤ V) (k : κ) :
    h.last.workPos k ∈ V k :=
  ⟨(hv k).1.trans (h.head_mem k).1, (h.head_mem k).2.trans (hv k).2⟩

@[simp] theorem visited_nil (c : TM.Cfg κ Γ Q xs) :
    (nil (Action := TM.Action κ Γ Q) c).visited =
      fun k ↦ NonemptyInterval.pure (c.workPos k) := by
  simp [visited]

@[simp] theorem visited_cons (c : TM.Cfg κ Γ Q xs) (a : TM.Action κ Γ Q)
    (h : History (TM.Cfg κ Γ Q xs) (TM.Action κ Γ Q)) (he : h.first = apply a c) :
    (cons c a h he).visited = (fun k ↦ NonemptyInterval.pure (c.workPos k)) ⊔ h.visited :=
  configSup_cons _ _ _ _ _

/-- Joining segments joins their visited intervals, without resetting prior visits. -/
@[simp] theorem visited_append (p q : History (TM.Cfg κ Γ Q xs) (TM.Action κ Γ Q))
    (he : p.last = q.first) : (p.append q he).visited = p.visited ⊔ q.visited :=
  configSup_append _ _ _ _

/-- One action adds its new head positions to the recorded intervals. -/
@[simp] theorem visited_snoc (h : History (TM.Cfg κ Γ Q xs) (TM.Action κ Γ Q))
    (a : TM.Action κ Γ Q) :
    (h.snoc a).visited =
      h.visited ⊔ fun k ↦ NonemptyInterval.pure ((apply a h.last).workPos k) :=
  configSup_snoc _ _ _

@[simp↓] theorem apply_visited (a : TM.Action κ Γ Q)
    (h : History (TM.Cfg κ Γ Q xs) (TM.Action κ Γ Q)) :
    (apply a h).visited =
      h.visited ⊔ fun k ↦ NonemptyInterval.pure ((apply a h.last).workPos k) :=
  h.visited_snoc a

/-- An action preserves a common bound exactly when its new heads remain inside it. -/
theorem apply_visited_le_iff (a : TM.Action κ Γ Q)
    (h : History (TM.Cfg κ Γ Q xs) (TM.Action κ Γ Q)) (V : κ → NonemptyInterval ℤ) :
    (apply a h).visited ≤ V ↔
      h.visited ≤ V ∧ ∀ k, (apply a h.last).workPos k ∈ V k := by
  rw [apply_visited, sup_le_iff]
  rfl

/-- Total visited-cell space, computed from interval lengths. -/
def space [Fintype κ] (h : History (TM.Cfg κ Γ Q xs) (TM.Action κ Γ Q)) : ℕ :=
  ∑ k, ((h.visited k).snd + 1 - (h.visited k).fst).toNat

@[simp] theorem space_nil [Fintype κ] (c : TM.Cfg κ Γ Q xs) :
    (nil (Action := TM.Action κ Γ Q) c).space = Fintype.card κ := by
  simp [space, NonemptyInterval.pure]

theorem space_le_of_visited_le [Fintype κ]
    (h : History (TM.Cfg κ Γ Q xs) (TM.Action κ Γ Q)) (V : κ → NonemptyInterval ℤ)
    (hv : h.visited ≤ V) : h.space ≤ ∑ k, ((V k).snd + 1 - (V k).fst).toNat := by
  apply Finset.sum_le_sum
  intro k _
  rcases hv k with ⟨hl, hr⟩
  omega

/-- Enlarging every visited interval cannot reduce space. -/
theorem space_mono [Fintype κ] {p q : History (TM.Cfg κ Γ Q xs) (TM.Action κ Γ Q)}
    (h : p.visited ≤ q.visited) : p.space ≤ q.space :=
  p.space_le_of_visited_le q.visited h

/-- A preceding action adds at most one visited cell on each tape. -/
theorem space_cons_le [Fintype κ] (c : TM.Cfg κ Γ Q xs) (a : TM.Action κ Γ Q)
    (h : History (TM.Cfg κ Γ Q xs) (TM.Action κ Γ Q)) (he : h.first = apply a c) :
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

private theorem interval_size_sup_le {u v : NonemptyInterval ℤ} {p : ℤ}
    (hu : p ∈ u) (hv : p ∈ v) :
    ((u ⊔ v).snd + 1 - (u ⊔ v).fst).toNat ≤
      (u.snd + 1 - u.fst).toNat + (v.snd + 1 - v.fst).toNat := by
  simp only [NonemptyInterval.mem_def, NonemptyInterval.fst_sup,
    NonemptyInterval.snd_sup] at *
  omega

/-- Adjacent segments share a head position, so their combined footprint is subadditive. -/
theorem space_append_le [Fintype κ]
    (p q : History (TM.Cfg κ Γ Q xs) (TM.Action κ Γ Q)) (he : p.last = q.first) :
    (p.append q he).space ≤ p.space + q.space := by
  simp only [space, visited_append, Pi.sup_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k _
  exact interval_size_sup_le (p.head_mem k) (he.symm ▸ q.first_head_mem k)

/-- Relabel every configuration and action while preserving the recorded tape evolution. -/
def mapState {Q' : Type*} (f : Q → Q')
    (h : History (TM.Cfg κ Γ Q xs) (TM.Action κ Γ Q)) :
    History (TM.Cfg κ Γ Q' xs) (TM.Action κ Γ Q') :=
  h.map (TM.Cfg.mapState f) (TM.Action.mapState f)

@[simp] theorem mapState_nil {Q' : Type*} (f : Q → Q') (c : TM.Cfg κ Γ Q xs) :
    (nil (Action := TM.Action κ Γ Q) c).mapState f = nil (c.mapState f) := rfl

@[simp] theorem mapState_id (h : History (TM.Cfg κ Γ Q xs) (TM.Action κ Γ Q)) :
    h.mapState id = h := h.map_id

@[simp] theorem mapState_mapState {Q' Q'' : Type*} (f : Q → Q') (g : Q' → Q'')
    (h : History (TM.Cfg κ Γ Q xs) (TM.Action κ Γ Q)) :
    (h.mapState f).mapState g = h.mapState (g ∘ f) := h.map_map _ _ _ _

@[simp↓] theorem apply_mapState {Q' : Type*} (f : Q → Q') (a : TM.Action κ Γ Q)
    (h : History (TM.Cfg κ Γ Q xs) (TM.Action κ Γ Q)) :
    apply (a.mapState f) (h.mapState f) = (apply a h).mapState f :=
  (h.map_snoc a (TM.Cfg.mapState f) (TM.Action.mapState f)).symm

@[simp] theorem first_mapState {Q' : Type*} (f : Q → Q')
    (h : History (TM.Cfg κ Γ Q xs) (TM.Action κ Γ Q)) :
    (h.mapState f).first = h.first.mapState f := rfl

@[simp] theorem last_mapState {Q' : Type*} (f : Q → Q')
    (h : History (TM.Cfg κ Γ Q xs) (TM.Action κ Γ Q)) :
    (h.mapState f).last = h.last.mapState f :=
  h.last_map _ _ (fun a c ↦ (TM.Action.apply_mapState f a c).symm)

@[simp↓] theorem observe_mapState {Q' : Type*} (f : Q → Q')
    (h : History (TM.Cfg κ Γ Q xs) (TM.Action κ Γ Q)) :
    (observe (h.mapState f) : Γ × (κ → Γ)) = observe h := by
  simp [History.observe_def, TM.Cfg.observe_def]

@[simp] theorem visited_mapState {Q' : Type*} (f : Q → Q')
    (h : History (TM.Cfg κ Γ Q xs) (TM.Action κ Γ Q)) :
    (h.mapState f).visited = h.visited :=
  h.configSup_map _ _ (fun a c ↦ (TM.Action.apply_mapState f a c).symm) _

@[simp] theorem space_mapState [Fintype κ] {Q' : Type*} (f : Q → Q')
    (h : History (TM.Cfg κ Γ Q xs) (TM.Action κ Γ Q)) :
    (h.mapState f).space = h.space := by
  simp [space]

end Complexity.Controller.History
