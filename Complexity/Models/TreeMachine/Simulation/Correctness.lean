/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Simulation.Init
public import Complexity.Models.StackMachine.Program.Correctness
public import Complexity.Models.TreeMachine.Deterministic

/-! # Linear time and space simulation through local stack operations -/

@[expose] public section

set_option experimental.vcgen true

namespace Complexity.TreeMachine.Simulation

/-- During each macro, time bounds stack growth from a source-space-bounded endpoint. -/
def spaceBound (k s : ℕ) : ℕ := (42 * (k + 4) + 1) * s

namespace Program

open StackMachine.Program Work Std.WP
open Controller (History)

variable {k : ℕ} [NeZero k] {Q : Type} [FinEnum Q]

omit [NeZero k] in
/-- The local macro bound is uniform over all instructions within a source space bound. -/
theorem macro_space_le {xs : Array Bool} (c : StackMachine.Cfg (Work k) Bool xs)
    {n s : ℕ} (hm : c.mass ≤ s) (hn : n ≤ 42 * s) :
    c.mass + Fintype.card (Work k) * n ≤ spaceBound k s := by
  rw [card_work]
  calc
    _ ≤ s + (k + 4) * (42 * s) := Nat.add_le_add hm (Nat.mul_le_mul_left _ hn)
    _ = _ := by
      simp [spaceBound, Nat.add_mul, Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.add_comm]

/-- Simulate a source run, charging creation and amortizing destination erasure.
Histories retain the peak across macros; no internal macro invariant is required. -/
theorem spec_loop {xs : Array Bool} (M : TreeMachine Id k Q)
    (r : Q × Cfg k) (c₀ : StackMachine.Cfg (Work k) Bool xs) (n s q : ℕ)
    (hw : c₀.stacks = contents r.2.regs)
    (hh : M.Halted (M.runFrom r n)) (hn : ∀ j < n, ¬M.Halted (M.runFrom r j))
    (hm : ∀ j ≤ n, (M.runFrom r j).2.mass ≤ s) :
    Triple ((Program.loopOn idle (body M) r.1).verify (historySemantics xs))
      (fun h b ↦ h.last = c₀ ∧ h.configSup StackMachine.Cfg.mass ≤ spaceBound k s ∧
        40 * (M.runHistoryFrom r n).snd.actionSum Action.sizeCost +
          3 * r.2.mass + 1 + q ≤ b)
      (fun _ h b ↦ h.last = bank c₀ (M.runFrom r n).2.regs ∧
        h.configSup StackMachine.Cfg.mass ≤ spaceBound k s ∧ q ≤ b) () := by
  let W := fun j ↦ (M.runHistoryFrom r j).snd.actionSum Action.sizeCost
  let I : Q → History (StackMachine.Cfg (Work k) Bool xs)
      (StackMachine.Action (Work k) Bool) → ℕ → Prop := fun v h b ↦
    ∃ j ≤ n, v = (M.runFrom r j).1 ∧ h.last = bank c₀ (M.runFrom r j).2.regs ∧
      h.configSup StackMachine.Cfg.mass ≤ spaceBound k s ∧
      40 * (W n - W j) + 3 * (M.runFrom r j).2.mass + 1 + q ≤ b
  constructor
  apply Triple.entails_wp_of_pre
    (Program.spec_loopOn_of_invariant idle (body M) r.1 (historySemantics xs) I _ ?_ ?_ ?_)
  · rintro h b ⟨hc, hS, hb⟩
    refine ⟨0, Nat.zero_le _, rfl, ?_, hS, ?_⟩
    · simpa only [Controller.runFrom_zero, bank_self c₀ r.2.regs hw] using hc
    · simpa [W] using hb
  · intro v h b hv
    simpa only [I, historySemantics_act, History.apply_def, History.last_snoc, idle_apply,
      History.configSup_snoc, sup_eq_left.mpr
        (h.config_le_configSup StackMachine.Cfg.mass h.last_mem_configs)] using hv
  · rintro v h b ⟨j, hj, hv, hc, hs, ht⟩
    omega
  · intro v
    constructor
    rintro h b ⟨j, hj, rfl, hc, hS, ht⟩
    by_cases hj' : j < n
    · have hf : M.halt (M.runFrom r j).1 = false := Bool.eq_false_iff.mpr (hn j hj')
      let a := (M.transition (M.runFrom r j).1 (observe (M.runFrom r j).2)).run
      have he : M.step (M.runFrom r j) = M.runFrom r (j + 1) := (M.runFrom_succ' _ j).symm
      have hcost : W (j + 1) = W j + a.2.sizeCost (M.runFrom r j).2 := by
        simp [W, Controller.actionSum_runHistoryFrom_add,
          Controller.actionSum_runHistoryFrom_one, hf, a]
      have hle : W (j + 1) ≤ W n := M.actionSum_runHistoryFrom_mono _ r hj'
      have hnext := hm (j + 1) hj'
      rw [← he, M.step_of_not_halted _ (hn j hj'), Controller.apply_prod] at hnext
      have ha : a.2.sizeCost (M.runFrom r j).2 ≤ s :=
        (a.2.sizeCost_le_mass _).trans (sup_le (hm j hj) hnext)
      have hp : 0 < a.2.sizeCost (M.runFrom r j).2 := a.2.sizeCost_pos _
      have hmj := hm j hj
      dsimp only [a] at hcost ha hp
      let z := 40 * (W n - W (j + 1)) + 1 + q
      have hbody :=
        spec_body_continue M (bank c₀ (M.runFrom r j).2.regs) (M.runFrom r j) 0 hf rfl
      simp only [Nat.add_zero] at hbody
      have hs := spec_history hbody
        (macro_space_le (bank c₀ (M.runFrom r j).2.regs) (by simpa [Cfg.mass] using hmj)
          (by omega)) z
      apply (Triple.entails_wp_of_post hs ?_) h b ⟨hc, hS, by dsimp only [z]; omega⟩
      rintro _ t b ⟨⟨rfl, hd⟩, hS', hq⟩
      refine ⟨j + 1, hj', congrArg Prod.fst he, ?_, hS', ?_⟩
      · simpa only [he, bank_bank] using hd
      · simpa only [he, z, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hq
    · have hj : j = n := by omega
      subst j
      have hf : M.halt (M.runFrom r n).1 = true := hh
      unfold body
      simp only [hf, ↓reduceIte]
      vcgen
      exact ⟨hc, hS, by omega⟩

end Program

open StackMachine.Program TreeMachine.Simulation.Program Work Std.WP
open Controller (History)

variable {k : ℕ} [NeZero k] {Q : Type} [FinEnum Q]

/-- Load a tree, simulate the source, and serialize the selected output register. -/
def Program.program (M : TreeMachine Id k Q) (i o : Fin k) :
    StackMachine.Program (Work k) Bool Unit := do
  init i
  Program.loopOn idle (body M) M.q₀
  IO.emitStack (data o)

/-- Input conversion, amortized source execution, and output serialization. -/
def timeBound (k N t : ℕ) : ℕ :=
  (6 * N + 5) + (40 * t + 3 * (N + k) + 1) + (3 * (N + k + t) + 2)

/-- On a nonempty input, the simulation time is linear in the source time and the input
size, with the factor of `spaceBound`. -/
theorem timeBound_le {k N t : ℕ} (hN : 0 < N) :
    timeBound k N t ≤ (42 * (k + 4) + 1) * (t + N) := by
  have := Nat.le_mul_of_pos_right (42 * k + 126) (Nat.add_pos_right t hN)
  rw [show 42 * (k + 4) + 1 = 43 + (42 * k + 126) by omega, Nat.add_mul]
  unfold timeBound
  omega

/-- The complete simulator preserves output and an independent source-space bound. -/
theorem Program.spec_program (M : TreeMachine Id k Q)
    {x a : Tree} {t s : ℕ} (h : M.ComputesWithin x a t s) :
    Triple ((program M 0 0).verify (historySemantics (BitList.encodeTree x).toArray))
      (fun c b ↦ c = History.nil (StackMachine.Cfg.init (Work k) (BitList.encodeTree x)) ∧
        timeBound k x.size t ≤ b)
      (fun _ c _ ↦ c.last.output = (BitList.encodeTree a).toArray ∧
        c.configSup StackMachine.Cfg.mass ≤ spaceBound k s) () := by
  obtain ⟨n, _, hh, ha, ht, _⟩ := h.exists_haltsAt
  have hx := h.input_size_le_space
  have hp : 0 < s := x.size_pos.trans_le hx
  let d := bank (loadedCfg 0 x) (M.run x n).2.regs
  have hd : d.mass ≤ s := by simpa [d, Cfg.mass] using h.mass_le n
  have hi := spec_history (by simpa only [Nat.add_zero] using spec_init (k := k) 0 x 0)
    (macro_space_le _ (s := s) (by simp [StackMachine.Cfg.mass]) (by omega))
    (40 * t + 3 * (x.size + k) + 1 + (3 * (x.size + k + t) + 2))
  have hl := spec_loop M (M.init x) (loadedCfg 0 x) n s (3 * a.size + 2) rfl
    hh.1 hh.2 (fun j _ ↦ h.mass_le j)
  rw [Controller.init_fst] at hl
  have he := Program.spec_exact_budget_le (fun q ↦ IO.spec_emitStack d (data 0) q)
    (m := 3 * a.size + 2) (by simp [d, ha]) 0
  simp only [Nat.add_zero] at he
  have hs := h.output_size_le_space
  have ho := spec_history he (macro_space_le d hd (by omega)) 0
  have hm₀ := Cfg.mass_init_le (k := k) x
  have hout := h.output_size_le_mass_add_time
  unfold program
  vcgen [hi, hl, ho]
  all_goals simp_all [d, timeBound, Controller.run, Controller.runHistory, loadedCfg,
    StackMachine.Cfg.mass] <;> omega

/-- Compile the serialized tree simulator to a native stack controller. -/
def compiler (M : TreeMachine Id k Q) := StackMachine.Program.compile (program M 0 0)

/-- Both time and space have linear simulation bounds. -/
theorem computesWithin (M : TreeMachine Id k Q)
    {x a : Tree} {t s : ℕ} (h : M.ComputesWithin x a t s) :
    (compiler M).ComputesWithin (BitList.encodeTree x) (BitList.encodeTree a)
      (timeBound k x.size t) (spaceBound k s) :=
  StackMachine.Program.computesWithin_history (Program.spec_program M h)

end Complexity.TreeMachine.Simulation
