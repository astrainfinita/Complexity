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
      if M.halt q then ⟨.nop, Comp.next N 0⟩
      else
        let a := (M.transition q (v ∘ Fin.castLE (by omega : k ≤ max k l + 1))).run
        ⟨a.op.rename (Fin.castLE (by omega)), .inl a.state⟩
    | .inr (.inl j) =>
      ⟨.left ⟨j.val + 1, by omega⟩ ⟨max k l, by omega⟩, Comp.next N (j.val + 1)⟩
    | .inr (.inr q) =>
      let a := (N.transition q (v ∘ Fin.castLE (by omega : l ≤ max k l + 1))).run
      ⟨a.op.rename (Fin.castLE (by omega)), .inr (.inr a.state)⟩

namespace Comp

variable (M : TreeMachine Id k Q) (N : TreeMachine Id l Q')

/-- Pad a first-phase configuration with empty registers. -/
def left (c : Cfg k Q) : Cfg (max k l + 1) (State k l Q Q') :=
  ⟨.inl c.state, pad (by omega) c.regs⟩

/-- Pad a second-phase configuration with empty registers. -/
def right (c : Cfg l Q') : Cfg (max k l + 1) (State k l Q Q') :=
  ⟨.inr (.inr c.state), pad (by omega) c.regs⟩

private theorem observe_pad {r : ℕ} (h : k ≤ r) (c : Cfg k Q) (q : Q') :
    (observe (Cfg.mk q (pad h c.regs)) : Fin r → Bool) ∘ Fin.castLE h = observe c := by
  funext i
  simp [pad_get]

@[simp] theorem mass_left (c : Cfg k Q) :
    (left (l := l) (Q' := Q') c).mass = c.mass + (max k l + 1 - k) :=
  sum_size_pad (by omega) _

@[simp] theorem mass_right (c : Cfg l Q') :
    (right (k := k) (Q := Q) c).mass = c.mass + (max k l + 1 - l) :=
  sum_size_pad (by omega) _

@[simp] theorem step_left (c : Cfg k Q) (h : ¬M.Halted c) :
    (comp M N).step (left (l := l) (Q' := Q') c) = left (M.step c) := by
  have h' : M.halt c.state = false := Bool.eq_false_iff.mpr h
  apply Cfg.ext <;> simp [step_eq, comp, left, h', observe_pad, pad_eval]

@[simp] theorem step_right (c : Cfg l Q') :
    (comp M N).step (right (k := k) (Q := Q) c) = right (N.step c) := by
  by_cases h : N.halt c.state = true
  · simp [step_eq, comp, right, h]
  · have h' : N.halt c.state = false := Bool.eq_false_iff.mpr h
    apply Cfg.ext <;> simp [step_eq, comp, right, h', observe_pad, pad_eval]

@[simp] theorem actionSum_one_left (c : Cfg k Q) (h : ¬M.Halted c) :
    ((comp M N).runHistoryFrom (left c) 1).actionSum Action.timeCost =
      (M.runHistoryFrom c 1).actionSum Action.timeCost := by
  have h' : M.halt c.state = false := Bool.eq_false_iff.mpr h
  simp [Controller.actionSum_runHistoryFrom_one, Action.timeCost, comp, left, h', observe_pad,
    Op.timeCost_rename, pad_comp_castLE]

@[simp] theorem actionSum_one_right (c : Cfg l Q') :
    ((comp M N).runHistoryFrom (right c) 1).actionSum Action.timeCost =
      (N.runHistoryFrom c 1).actionSum Action.timeCost := by
  simp [Controller.actionSum_runHistoryFrom_one, Action.timeCost, comp, right, observe_pad,
    Op.timeCost_rename, pad_comp_castLE]

theorem runFrom_left (c : Cfg k Q) (n : ℕ)
    (h : ∀ j < n, ¬M.Halted (M.runFrom c j)) :
    (comp M N).runFrom (left (l := l) (Q' := Q') c) n = left (M.runFrom c n) := by
  exact Transition.rel_runN_of_not_halted (H := M.Halted)
    (R := fun c d ↦ d = left (l := l) (Q' := Q') c)
    rfl (by rintro c _ rfl hc; exact step_left M N c hc) h

theorem actionSum_left (c : Cfg k Q) (n : ℕ)
    (h : ∀ j < n, ¬M.Halted (M.runFrom c j)) :
    ((comp M N).runHistoryFrom (left c) n).actionSum Action.timeCost =
      (M.runHistoryFrom c n).actionSum Action.timeCost := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Controller.actionSum_runHistoryFrom_add, ih (fun j hj => h j (by omega)),
      runFrom_left M N _ n (fun j hj => h j (by omega)),
      actionSum_one_left M N _ (h n (by omega))]

theorem runFrom_right (c : Cfg l Q') (n : ℕ) :
    (comp M N).runFrom (right (k := k) (Q := Q) c) n = right (N.runFrom c n) := by
  exact Transition.runN_map right (step_right M N) c n

theorem actionSum_right (c : Cfg l Q') (n : ℕ) :
    ((comp M N).runHistoryFrom (right c) n).actionSum Action.timeCost =
      (N.runHistoryFrom c n).actionSum Action.timeCost := by
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
    Cfg (max k l + 1) (State k l Q Q') := ⟨next N n, clear ρ n⟩

private theorem step_bridge (ρ : Fin (max k l + 1) → Tree)
    (hz : ρ ⟨max k l, by omega⟩ = .nil) {n : ℕ} (hn : n < max k l - 1) :
    (comp M N).step (bridge (Q := Q) N ρ n) = bridge N ρ (n + 1) := by
  have hz' : clear ρ n ⟨max k l, by omega⟩ = .nil := by
    simp [clear, hz, show ¬max k l ≤ n by omega]
  apply Cfg.ext <;> simp [step_eq, bridge, next, hn, comp, hz', clear_succ]

private theorem actionSum_one_bridge (ρ : Fin (max k l + 1) → Tree)
    (hz : ρ ⟨max k l, by omega⟩ = .nil) {n : ℕ} (hn : n < max k l - 1) :
    ((comp M N).runHistoryFrom (bridge (Q := Q) N ρ n) 1).actionSum Action.timeCost = 1 := by
  simp [Controller.actionSum_runHistoryFrom_one, Action.timeCost, bridge, next, hn, comp,
    Op.timeCost, clear, hz, show ¬max k l ≤ n by omega]

private theorem runFrom_bridge (ρ : Fin (max k l + 1) → Tree)
    (hz : ρ ⟨max k l, by omega⟩ = .nil) {n : ℕ} (hn : n ≤ max k l - 1) :
    (comp M N).runFrom (bridge (Q := Q) N ρ 0) n = bridge N ρ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Controller.runFrom_succ', ih (by omega), step_bridge M N ρ hz (by omega)]

private theorem actionSum_bridge (ρ : Fin (max k l + 1) → Tree)
    (hz : ρ ⟨max k l, by omega⟩ = .nil) {n : ℕ} (hn : n ≤ max k l - 1) :
    ((comp M N).runHistoryFrom (bridge (Q := Q) N ρ 0) n).actionSum Action.timeCost = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Controller.actionSum_runHistoryFrom_add, ih (by omega),
      runFrom_bridge M N ρ hz (by omega), actionSum_one_bridge M N ρ hz (by omega)]

private theorem mass_bridge (ρ : Fin (max k l + 1) → Tree) (n : ℕ) :
    (bridge (Q := Q) N ρ n).mass ≤ ∑ j, (ρ j).size := by
  exact Finset.sum_le_sum fun j _ => clear_size_le ρ n j

private theorem step_left_halted (c : Cfg k Q) (h : M.Halted c) :
    (comp M N).step (left (l := l) (Q' := Q') c) =
      bridge N (pad (by omega) c.regs) 0 := by
  have h' : M.halt c.state = true := h
  apply Cfg.ext <;> simp [step_eq, comp, left, bridge, h']

private theorem actionSum_one_left_halted (c : Cfg k Q) (h : M.Halted c) :
    ((comp M N).runHistoryFrom (left c) 1).actionSum Action.timeCost = 1 := by
  simp [Controller.actionSum_runHistoryFrom_one, Action.timeCost, left, comp,
    show M.halt c.state = true from h, Op.timeCost]

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

private theorem bridge_end (c : Cfg k Q) :
    bridge (k := k) (Q := Q) N (pad (by omega) c.regs) (max k l - 1) =
      right (k := k) (Q := Q) (N.initInput (Config := Cfg l Q') (c.regs 0)) := by
  have hz : pad (by omega : k ≤ max k l + 1) c.regs ⟨max k l, by omega⟩ = .nil :=
    pad_of_le _ _ _ (Nat.le_max_left k l)
  have hzero : pad (by omega : k ≤ max k l + 1) c.regs 0 = c.regs 0 :=
    pad_get _ _ 0
  simp only [bridge, clear_eq_input _ hz, hzero, next, lt_self_iff_false, ↓reduceDIte,
    right, initInput_tree, pad_input]
  rfl

/-- The bridge leaves the first result in zero and clears every other register. -/
theorem runFrom_clear (c : Cfg k Q) (h : M.Halted c) :
    (comp M N).runFrom (left (l := l) (Q' := Q') c) (max k l) =
      right (N.initInput (Config := Cfg l Q') (c.regs 0)) := by
  have hk : 0 < k := NeZero.pos k
  conv_lhs => arg 3; rw [show max k l = (max k l - 1) + 1 by omega]
  rw [Controller.runFrom_succ, step_left_halted M N c h]
  rw [runFrom_bridge M N _ (pad_of_le _ _ _ (Nat.le_max_left k l)) le_rfl]
  exact bridge_end N c

omit [NeZero l] in
/-- Clearing writes an empty leaf and charges one per instruction. -/
theorem actionSum_clear (c : Cfg k Q) (h : M.Halted c) :
    ((comp M N).runHistoryFrom (left c) (max k l)).actionSum Action.timeCost = max k l := by
  have hk : 0 < k := NeZero.pos k
  conv_lhs => enter [1, 3]; rw [show max k l = 1 + (max k l - 1) by omega]
  rw [Controller.actionSum_runHistoryFrom_add, Controller.runFrom_succ, Controller.runFrom_zero,
    step_left_halted M N c h, actionSum_one_left_halted M N c h,
    actionSum_bridge M N _ (pad_of_le _ _ _ (Nat.le_max_left k l)) le_rfl]
  omega

omit [NeZero k] [NeZero l] in
/-- Every clearing prefix has at most the first phase's final register mass. -/
theorem mass_clear_le (c : Cfg k Q) (h : M.Halted c) {n : ℕ} (hn : n ≤ max k l) :
    ((comp M N).runFrom (left (l := l) (Q' := Q') c) n).mass ≤
      (left (l := l) (Q' := Q') c).mass := by
  cases n with
  | zero => exact le_rfl
  | succ n =>
    rw [Controller.runFrom_succ, step_left_halted M N c h,
      runFrom_bridge M N _ (pad_of_le _ _ _ (Nat.le_max_left k l)) (by omega)]
    exact mass_bridge N _ n

omit [NeZero l] in
/-- Standard initialization embeds the first machine and leaves the shared padding empty. -/
theorem initInput_eq (x : Tree) :
    (comp M N).initInput (Config := Cfg (max k l + 1) (State k l Q Q')) x =
      left (l := l) (Q' := Q') (M.initInput (Config := Cfg k Q) x) := by
  simp only [initInput_tree, comp, left, pad_input]
  rfl

end Comp

/-- Sequential machines share their work registers. Clearing costs only the fixed number
of work registers; peak space is the larger padded phase bound. -/
theorem comp_computesInTimeAndSpace [NeZero k] [NeZero l]
    (M : TreeMachine Id k Q) (N : TreeMachine Id l Q')
    {x a b : Tree} {t s u v : ℕ}
    (hM : M.ComputesInTimeAndSpace x a t s)
    (hN : N.ComputesInTimeAndSpace a b u v) :
    (comp M N).ComputesInTimeAndSpace x b (t + max k l + u)
      (max (s + (max k l + 1 - k)) (v + (max k l + 1 - l))) := by
  obtain ⟨n, _, hn, ha, hc, _⟩ := hM.exists_haltsAt
  obtain ⟨m, _, hm, hb, hd, _⟩ := hN.exists_haltsAt
  let C := comp M N
  let c := M.run (Cfg k Q) x n
  have h₀ : C.initInput (Config := Cfg (max k l + 1) (Comp.State k l Q Q')) x =
      Comp.left (l := l) (Q' := Q') (M.initInput (Config := Cfg k Q) x) :=
    Comp.initInput_eq M N x
  have hleft (d : ℕ) (hd : d ≤ n) :
      C.run (Cfg (max k l + 1) (Comp.State k l Q Q')) x d =
        Comp.left (l := l) (Q' := Q') (M.run (Cfg k Q) x d) := by
    rw [Controller.run, h₀]
    exact Comp.runFrom_left M N _ d (fun j hj => hn.2 j (by omega))
  have h₁ : C.run (Cfg (max k l + 1) (Comp.State k l Q Q')) x n =
      Comp.left (l := l) (Q' := Q') c := hleft n le_rfl
  have h₂ : C.runFrom (Comp.left (l := l) (Q' := Q') c) (max k l) =
      Comp.right (k := k) (Q := Q) (N.initInput (Config := Cfg l Q') a) := by
    rw [Comp.runFrom_clear M N c hn.1]
    exact congrArg (fun a => Comp.right (k := k) (Q := Q) (N.initInput (Config := Cfg l Q') a)) ha
  have hright (d : ℕ) : C.run
      (Cfg (max k l + 1) (Comp.State k l Q Q')) x (n + max k l + d) =
      Comp.right (k := k) (Q := Q) (N.run (Cfg l Q') a d) := by
    rw [Controller.run, Controller.runFrom_add, Controller.runFrom_add, ← Controller.run, h₁, h₂]
    exact Comp.runFrom_right M N _ d
  have hw : (C.runHistory (Cfg (max k l + 1) (Comp.State k l Q Q')) x
      (n + max k l + m)).actionSum Action.timeCost ≤ t + max k l + u := by
    rw [Controller.runHistory, Controller.actionSum_runHistoryFrom_add,
      Controller.actionSum_runHistoryFrom_add, Controller.runFrom_add, ← Controller.run, h₁, h₂, h₀,
      Comp.actionSum_left M N _ n hn.2, Comp.actionSum_clear M N c hn.1, Comp.actionSum_right M N]
    exact Nat.add_le_add (Nat.add_le_add_right hc _) hd
  refine ⟨n + max k l + m, ?_, ?_, hw, ?_⟩
  · change C.Halted (C.run (Cfg (max k l + 1) (Comp.State k l Q Q')) x (n + max k l + m))
    rw [hright]
    exact hm.1
  · change (C.run (Cfg (max k l + 1) (Comp.State k l Q Q'))
      x (n + max k l + m)).regs 0 = b
    rw [hright]
    exact (pad_get (by omega) (N.run (Cfg l Q') a m).regs 0).trans hb
  · apply (C.configSup_runHistory_le_iff Cfg.mass x _ _).2
    intro d _
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
