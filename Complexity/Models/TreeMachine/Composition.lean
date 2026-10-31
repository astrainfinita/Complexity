/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Deterministic
public import Complexity.Models.TreeMachine.Embedding
public import Complexity.Control.Transition.Simulation

/-!
# Sequential composition with shared registers

Both machines use register zero for input and output. Their register banks overlap;
a reserved empty register clears the other work registers between phases. The bridge
performs one `nop` followed by one left projection per nonzero work register. It never
copies the intermediate tree or increases register mass.
-/

@[expose] public section

namespace Complexity.TreeMachine

variable {k l : ℕ} {Q Q' : Type*}

namespace Comp

/-- Control states for the first machine, the clearing pass, and the second machine. -/
abbrev State (k l : ℕ) (Q Q' : Type*) := Q ⊕ (Fin (max k l - 1) ⊕ Q')

/-- Enter the next clearing instruction, or start the second machine once clearing ends. -/
def next (N : TreeMachine Id l Q') (n : ℕ) : State k l Q Q' :=
  if h : n < max k l - 1 then .inr (.inl ⟨n, h⟩) else .inr (.inr N.q₀)

end Comp

/-- Run two machines over a shared work bank, clearing every register except zero
before the second phase. The final register is permanently reserved as `nil`. -/
def comp (M : TreeMachine Id k Q) (N : TreeMachine Id l Q') :
    TreeMachine Id (max k l + 1) (Comp.State k l Q Q') where
  q₀ := .inl M.q₀
  halt
    | .inl _ => false
    | .inr (.inl _) => false
    | .inr (.inr q) => N.halt q
  transition q v := pure <| match q with
    | .inl q =>
      if M.halt q then (Comp.next N 0, .nop)
      else
        let a := (M.transition q (v ∘ Fin.castLE (by omega : k ≤ max k l + 1))).run
        (.inl a.1, a.2.rename (Fin.castLE (by omega)))
    | .inr (.inl j) =>
      (Comp.next N (j.val + 1), .left ⟨j.val + 1, by omega⟩ ⟨max k l, by omega⟩)
    | .inr (.inr q) =>
      let a := (N.transition q (v ∘ Fin.castLE (by omega : l ≤ max k l + 1))).run
      (.inr (.inr a.1), a.2.rename (Fin.castLE (by omega)))

namespace Comp

variable (M : TreeMachine Id k Q) (N : TreeMachine Id l Q')

/-- Pad a first-phase configuration with empty registers. -/
def left (c : Q × Cfg k) : State k l Q Q' × Cfg (max k l + 1) :=
  (.inl c.1, ⟨pad (by omega) c.2.regs⟩)

/-- Pad a second-phase configuration with empty registers. -/
def right (c : Q' × Cfg l) : State k l Q Q' × Cfg (max k l + 1) :=
  (.inr (.inr c.1), ⟨pad (by omega) c.2.regs⟩)

private theorem observe_pad {r : ℕ} (h : k ≤ r) (c : Cfg k) :
    (observe (Cfg.mk (pad h c.regs)) : Fin r → Bool) ∘ Fin.castLE h = observe c := by
  funext i
  simp [pad_get]

@[simp] theorem mass_left (c : Q × Cfg k) :
    (left (l := l) (Q' := Q') c).2.mass = c.2.mass + (max k l + 1 - k) :=
  sum_size_pad (by omega) _

@[simp] theorem mass_right (c : Q' × Cfg l) :
    (right (k := k) (Q := Q) c).2.mass = c.2.mass + (max k l + 1 - l) :=
  sum_size_pad (by omega) _

@[simp] theorem step_left (c : Q × Cfg k) (h : ¬M.Halted c) :
    (comp M N).step (left c) = left (M.step c) := by
  have h' : M.halt c.1 = false := Bool.eq_false_iff.mpr h
  simp [step_eq, comp, left, h', observe_pad, pad_eval, Cfg.ext_iff]

@[simp] theorem step_right (c : Q' × Cfg l) :
    (comp M N).step (right c) = right (N.step c) := by
  by_cases h : N.halt c.1 = true
  · simp [step_eq, comp, right, h]
  · have h' : N.halt c.1 = false := Bool.eq_false_iff.mpr h
    simp [step_eq, comp, right, h', observe_pad, pad_eval, Cfg.ext_iff]

@[simp] theorem actionSum_one_left (c : Q × Cfg k) (h : ¬M.Halted c) :
    ((comp M N).runHistoryFrom (left c) 1).actionSum (fun a c ↦ a.2.sizeCost c.2) =
      (M.runHistoryFrom c 1).actionSum (fun a c ↦ a.2.sizeCost c.2) := by
  have h' : M.halt c.1 = false := Bool.eq_false_iff.mpr h
  simp [Controller.actionSum_runHistoryFrom_one, comp, left, h', observe_pad,
    Action.sizeCost_rename, pad_comp_castLE]

@[simp] theorem actionSum_one_right (c : Q' × Cfg l) :
    ((comp M N).runHistoryFrom (right c) 1).actionSum (fun a c ↦ a.2.sizeCost c.2) =
      (N.runHistoryFrom c 1).actionSum (fun a c ↦ a.2.sizeCost c.2) := by
  simp [Controller.actionSum_runHistoryFrom_one, comp, right, observe_pad,
    Action.sizeCost_rename, pad_comp_castLE]

theorem runFrom_left (c : Q × Cfg k) (n : ℕ)
    (h : ∀ j < n, ¬M.Halted (M.runFrom c j)) :
    (comp M N).runFrom (left c) n = left (M.runFrom c n) := by
  exact Transition.rel_runN_of_not_halted (R := fun c d ↦ d = left c)
    rfl (by rintro c _ rfl hc; exact step_left M N c hc) h

theorem actionSum_left (c : Q × Cfg k) (n : ℕ)
    (h : ∀ j < n, ¬M.Halted (M.runFrom c j)) :
    ((comp M N).runHistoryFrom (left c) n).actionSum (fun a c ↦ a.2.sizeCost c.2) =
      (M.runHistoryFrom c n).actionSum (fun a c ↦ a.2.sizeCost c.2) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Controller.actionSum_runHistoryFrom_add, ih (fun j hj => h j (by omega)),
      runFrom_left M N _ n (fun j hj => h j (by omega)),
      actionSum_one_left M N _ (h n (by omega))]

theorem runFrom_right (c : Q' × Cfg l) (n : ℕ) :
    (comp M N).runFrom (right c) n = right (N.runFrom c n) := by
  exact Transition.runN_map right (step_right M N) c n

theorem actionSum_right (c : Q' × Cfg l) (n : ℕ) :
    ((comp M N).runHistoryFrom (right c) n).actionSum (fun a c ↦ a.2.sizeCost c.2) =
      (N.runHistoryFrom c n).actionSum (fun a c ↦ a.2.sizeCost c.2) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Controller.actionSum_runHistoryFrom_add, ih, runFrom_right, actionSum_one_right]

/-- Clear registers one through `n`, preserving zero and all later registers. -/
def clear {r : ℕ} (ρ : Fin r → Tree) (n : ℕ) : Fin r → Tree :=
  fun j => if 0 < j.val ∧ j.val ≤ n then .nil else ρ j

@[simp] theorem clear_zero {r : ℕ} (ρ : Fin r → Tree) : clear ρ 0 = ρ := by
  funext j
  exact ite_eq_right (by omega)

private theorem clear_succ {r : ℕ} (ρ : Fin r → Tree) (n : ℕ) (h : n + 1 < r) :
    Function.update (clear ρ n) ⟨n + 1, h⟩ .nil = clear ρ (n + 1) := by
  funext j
  by_cases hj : j.val = n + 1
  · have he : j = ⟨n + 1, h⟩ := Fin.ext hj
    simp [he, clear]
  · have he : j ≠ ⟨n + 1, h⟩ := fun he => hj (congrArg Fin.val he)
    have hc : (0 < j.val ∧ j.val ≤ n + 1) ↔ (0 < j.val ∧ j.val ≤ n) := by omega
    simp only [Function.update_of_ne he, clear, hc]

private theorem clear_size_le {r : ℕ} (ρ : Fin r → Tree) (n : ℕ) (j : Fin r) :
    (clear ρ n j).size ≤ (ρ j).size := by
  unfold clear
  split
  · exact (ρ j).size_pos
  · exact le_rfl

/-- The configuration after a prefix of the clearing pass. -/
def bridge (ρ : Fin (max k l + 1) → Tree) (n : ℕ) :
    State k l Q Q' × Cfg (max k l + 1) := (next N n, ⟨clear ρ n⟩)

private theorem step_bridge (ρ : Fin (max k l + 1) → Tree)
    (hz : ρ ⟨max k l, by omega⟩ = .nil) {n : ℕ} (hn : n < max k l - 1) :
    (comp M N).step (bridge N ρ n) = bridge N ρ (n + 1) := by
  have hz' : clear ρ n ⟨max k l, by omega⟩ = .nil := by
    simp [clear, hz, show ¬max k l ≤ n by omega]
  simp [step_eq, bridge, next, hn, comp, hz', clear_succ, Cfg.ext_iff]

private theorem actionSum_one_bridge (ρ : Fin (max k l + 1) → Tree)
    (hz : ρ ⟨max k l, by omega⟩ = .nil) {n : ℕ} (hn : n < max k l - 1) :
    ((comp M N).runHistoryFrom (bridge N ρ n) 1).actionSum (fun a c ↦ a.2.sizeCost c.2) = 1 := by
  simp [Controller.actionSum_runHistoryFrom_one, bridge, next, hn, comp,
    Action.sizeCost, clear, hz, show ¬max k l ≤ n by omega]

private theorem runFrom_bridge (ρ : Fin (max k l + 1) → Tree)
    (hz : ρ ⟨max k l, by omega⟩ = .nil) {n : ℕ} (hn : n ≤ max k l - 1) :
    (comp M N).runFrom (bridge N ρ 0) n = bridge N ρ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Controller.runFrom_succ', ih (by omega), step_bridge M N ρ hz (by omega)]

private theorem actionSum_bridge (ρ : Fin (max k l + 1) → Tree)
    (hz : ρ ⟨max k l, by omega⟩ = .nil) {n : ℕ} (hn : n ≤ max k l - 1) :
    ((comp M N).runHistoryFrom (bridge N ρ 0) n).actionSum (fun a c ↦ a.2.sizeCost c.2) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Controller.actionSum_runHistoryFrom_add, ih (by omega),
      runFrom_bridge M N ρ hz (by omega), actionSum_one_bridge M N ρ hz (by omega)]

private theorem mass_bridge (ρ : Fin (max k l + 1) → Tree) (n : ℕ) :
    (bridge (Q := Q) N ρ n).2.mass ≤ ∑ j, (ρ j).size := by
  unfold bridge Cfg.mass
  exact Finset.sum_le_sum fun j _ => clear_size_le ρ n j

private theorem step_left_halted (c : Q × Cfg k) (h : M.Halted c) :
    (comp M N).step (left c) =
      bridge N (pad (by omega) c.2.regs) 0 := by
  have h' : M.halt c.1 = true := h
  simp [step_eq, comp, left, bridge, h']

private theorem actionSum_one_left_halted (c : Q × Cfg k) (h : M.Halted c) :
    ((comp M N).runHistoryFrom (left c) 1).actionSum (fun a c ↦ a.2.sizeCost c.2) = 1 := by
  simp [Controller.actionSum_runHistoryFrom_one, left, comp,
    show M.halt c.1 = true from h, Action.sizeCost]

private theorem clear_eq_input {r : ℕ} (ρ : Fin (r + 1) → Tree)
    (hz : ρ ⟨r, by omega⟩ = .nil) : clear ρ (r - 1) = input 0 (ρ 0) := by
  funext j
  by_cases hj : j = 0
  · subst j
    simp [clear]
  · have hj' : 0 < j.val := by
      have : j.val ≠ 0 := fun h => hj (Fin.ext h)
      omega
    by_cases hr : j.val < r
    · simp [clear, hj', show j.val ≤ r - 1 by omega, input_get_of_ne _ hj]
    · have he : j = ⟨r, by omega⟩ := by
        apply Fin.ext
        change j.val = r
        omega
      rw [input_get_of_ne _ hj]
      rw [he]
      have hr' : 0 < r := by omega
      simp [clear, show ¬r ≤ r - 1 by omega, hz]

variable [NeZero k] [NeZero l]

private theorem bridge_end (c : Q × Cfg k) :
    bridge N (pad (by omega) c.2.regs) (max k l - 1) =
      right (k := k) (Q := Q) (N.init (c.2.regs 0)) := by
  have hz : pad (by omega : k ≤ max k l + 1) c.2.regs ⟨max k l, by omega⟩ = .nil :=
    pad_of_le _ _ _ (Nat.le_max_left k l)
  have hzero : pad (by omega : k ≤ max k l + 1) c.2.regs 0 = c.2.regs 0 :=
    pad_get _ _ 0
  simp only [bridge, clear_eq_input _ hz, hzero, next, lt_self_iff_false, ↓reduceDIte,
    right, Controller.init, hasConfig_init, Cfg.init_regs, pad_input]
  rfl

/-- The bridge leaves the first result in zero and clears every other register. -/
theorem runFrom_clear (c : Q × Cfg k) (h : M.Halted c) :
    (comp M N).runFrom (left c) (max k l) =
      right (N.init (c.2.regs 0)) := by
  have hk : 0 < k := NeZero.pos k
  conv_lhs => arg 3; rw [show max k l = (max k l - 1) + 1 by omega]
  rw [Controller.runFrom_succ, step_left_halted M N c h]
  rw [runFrom_bridge M N _ (pad_of_le _ _ _ (Nat.le_max_left k l)) le_rfl]
  exact bridge_end N c

omit [NeZero l] in
/-- Clearing writes an empty leaf and charges one per instruction. -/
theorem actionSum_clear (c : Q × Cfg k) (h : M.Halted c) :
    ((comp M N).runHistoryFrom (left c) (max k l)).actionSum (fun a c ↦ a.2.sizeCost c.2) =
      max k l := by
  have hk : 0 < k := NeZero.pos k
  conv_lhs => enter [1, 3]; rw [show max k l = 1 + (max k l - 1) by omega]
  rw [Controller.actionSum_runHistoryFrom_add, Controller.runFrom_succ, Controller.runFrom_zero,
    step_left_halted M N c h, actionSum_one_left_halted M N c h,
    actionSum_bridge M N _ (pad_of_le _ _ _ (Nat.le_max_left k l)) le_rfl]
  omega

omit [NeZero k] [NeZero l] in
/-- Every clearing prefix has at most the first phase's final register mass. -/
theorem mass_clear_le (c : Q × Cfg k) (h : M.Halted c) {n : ℕ} (hn : n ≤ max k l) :
    ((comp M N).runFrom (left c) n).2.mass ≤
      (left (l := l) (Q' := Q') c).2.mass := by
  cases n with
  | zero => exact le_rfl
  | succ n =>
    rw [Controller.runFrom_succ, step_left_halted M N c h,
      runFrom_bridge M N _ (pad_of_le _ _ _ (Nat.le_max_left k l)) (by omega)]
    exact mass_bridge N _ n

omit [NeZero l] in
/-- Standard initialization embeds the first machine and leaves the shared padding empty. -/
theorem init_eq (x : Tree) : (comp M N).init x = left (M.init x) := by
  simp [Controller.init, comp, left, pad_input]
  rfl

end Comp

/-- Sequential machines share their work registers. Clearing costs only the fixed number
of work registers; peak space is the larger padded phase bound. -/
theorem comp_computesWithin [NeZero k] [NeZero l]
    (M : TreeMachine Id k Q) (N : TreeMachine Id l Q')
    {x a b : Tree} {t s u v : ℕ}
    (hM : M.ComputesWithin x a t s)
    (hN : N.ComputesWithin a b u v) :
    (comp M N).ComputesWithin x b (t + max k l + u)
      (max (s + (max k l + 1 - k)) (v + (max k l + 1 - l))) := by
  obtain ⟨n, _, hn, ha, hc, _⟩ := hM.exists_haltsAt
  obtain ⟨m, _, hm, hb, hd, _⟩ := hN.exists_haltsAt
  let C := comp M N
  let c := M.run x n
  have h₀ : C.init x = Comp.left (M.init x) :=
    Comp.init_eq M N x
  have hleft (d : ℕ) (hd : d ≤ n) :
      C.run x d = Comp.left (M.run x d) := by
    rw [Controller.run, h₀]
    exact Comp.runFrom_left M N _ d (fun j hj => hn.2 j (by omega))
  have h₁ : C.run x n = Comp.left c := hleft n le_rfl
  have h₂ : C.runFrom (Comp.left c) (max k l) =
      Comp.right (N.init a) := by
    rw [Comp.runFrom_clear M N c hn.1]
    exact congrArg (fun a => Comp.right (N.init a)) ha
  have hright (d : ℕ) : C.run x (n + max k l + d) = Comp.right (N.run a d) := by
    rw [Controller.run, Controller.runFrom_add, Controller.runFrom_add, ← Controller.run, h₁, h₂]
    exact Comp.runFrom_right M N _ d
  have hw : (C.runHistory x (n + max k l + m)).snd.actionSum Action.sizeCost ≤
      t + max k l + u := by
    simp only [Controller.History.actionSum_snd] at hc hd ⊢
    rw [Controller.runHistory, Controller.actionSum_runHistoryFrom_add,
      Controller.actionSum_runHistoryFrom_add, Controller.runFrom_add, ← Controller.run, h₁, h₂, h₀,
      Comp.actionSum_left M N _ n hn.2, Comp.actionSum_clear M N c hn.1, Comp.actionSum_right M N]
    exact Nat.add_le_add (Nat.add_le_add_right hc _) hd
  refine ⟨n + max k l + m, ?_, ?_, hw, ?_⟩
  · change C.Halted (C.run x (n + max k l + m))
    rw [hright]
    exact hm.1
  · change (C.run x (n + max k l + m)).2.regs 0 = b
    rw [hright]
    exact (pad_get (by omega) (N.run a m).2.regs 0).trans hb
  · simp only [Controller.History.configSup_snd]
    apply (C.configSup_runHistory_le_iff x (Cfg.mass ∘ Prod.snd) _ _).2
    intro d _
    rw [Function.comp_apply]
    by_cases hdn : d ≤ n
    · rw [hleft d hdn, Comp.mass_left]
      exact (Nat.add_le_add_right (hM.mass_le d) _).trans (Nat.le_max_left _ _)
    · by_cases hdk : d ≤ n + max k l
      · have hde : d = n + (d - n) := by omega
        rw [hde, Controller.run, Controller.runFrom_add, ← Controller.run, h₁]
        have hs := Comp.mass_clear_le M N c hn.1 (n := d - n) (by omega)
        rw [Comp.mass_left] at hs
        exact (hs.trans (Nat.add_le_add_right (hM.mass_le n) _)).trans (Nat.le_max_left _ _)
      · have hde : d = n + max k l + (d - (n + max k l)) := by omega
        rw [hde, hright, Comp.mass_right]
        exact (Nat.add_le_add_right (hN.mass_le _) _).trans (Nat.le_max_right _ _)

end Complexity.TreeMachine
