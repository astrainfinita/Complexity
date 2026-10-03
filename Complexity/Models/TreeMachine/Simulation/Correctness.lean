/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Simulation.Init
public import Complexity.Models.StackMachine.Program.Correctness
public import Complexity.Models.TreeMachine.Deterministic

/-! # Total specifications for the monadic tree simulator -/

@[expose] public section

set_option experimental.vcgen true

namespace Complexity.TreeMachine.Simulation.Program

open StackMachine.Program Work Std.WP

variable {k : ℕ} {Q : Type} [FinEnum Q]

/-- Current source registers, bounded old words, and empty output at each loop entry. -/
def Rep {xs : Array Bool} (r : Cfg k Q) (b : Bool)
    (c : StackMachine.Cfg (Work k) Bool Unit xs) (B : ℕ) : Prop :=
  c.output = #[] ∧
    ∃ σ, c.stacks = contents b (fun i ↦ BitList.encodeTree (r.regs i)) σ ∧
      ∀ i, (σ i).length ≤ B

/-- One loop entry, root observation, and a uniform allowance for every register block. -/
def stepTime (k B : ℕ) : ℕ := 2 + k * (30 * (B + 1))

omit [FinEnum Q] in
private theorem rep_loaded (q : Q) (i : Fin k) (x : Tree) (B : ℕ) :
    Rep (Cfg.mk q (input i x)) false (loadedCfg i x) B := by
  refine ⟨rfl, fun _ ↦ [], rfl, ?_⟩
  simp

/-- Simulate a source run and return its final register bank, preserving unused credits.
The source and target need not be initial configurations, and the target may have any input. -/
theorem spec_loop {xs : Array Bool} (M : TreeMachine Id k Q)
    (r : Cfg k Q) (c₀ : StackMachine.Cfg (Work k) Bool Unit xs) (b₀ : Bool)
    (n B q : ℕ) (hr₀ : Rep r b₀ c₀ B)
    (hh : M.Halted (M.runFrom r n))
    (hn : ∀ j < n, ¬M.Halted (M.runFrom r j))
    (hm : ∀ j ≤ n, (M.runFrom r j).mass ≤ B) :
    Triple ((Program.loopOn StackMachine.Program.idle (body M) (r.state, b₀)).verify
      (StackMachine.Program.semantics xs))
      (fun s t ↦ s = c₀ ∧ n * stepTime k B + 1 + q ≤ t)
      (fun b s t ↦ Rep (M.runFrom r n) b s B ∧ q ≤ t) () := by
  have hB (j : ℕ) (hj : j ≤ n) (i : Fin k) : ((M.runFrom r j).regs i).size ≤ B :=
    ((M.runFrom r j).reg_size_le_mass i).trans (hm j hj)
  let I : (Q × Bool) →
      StackMachine.Cfg (Work k) Bool Unit xs → ℕ → Prop :=
    fun v c t ↦ ∃ j ≤ n, v.1 = (M.runFrom r j).state ∧ Rep (M.runFrom r j) v.2 c B ∧
      (n - j) * stepTime k B + 1 + q ≤ t
  constructor
  apply Triple.entails_wp_of_pre
    (Program.spec_loopOn_nop StackMachine.Program.idle (body M) (r.state, b₀)
      (StackMachine.Program.semantics xs) I _ StackMachine.Program.idle_apply ?_ ?_)
  · rintro c t ⟨rfl, ht⟩
    exact ⟨0, Nat.zero_le _, rfl, hr₀, by simpa using ht⟩
  · rintro v c t ⟨j, hj, hstate, hr, ht⟩
    omega
  · rintro ⟨state, b⟩
    constructor
    rintro c t ⟨j, hj, hstate, ⟨hy, σ, hw, hσ⟩, ht⟩
    dsimp only at hstate
    subst state
    by_cases hj' : j < n
    · let z := (n - (j + 1)) * stepTime k B + 1 + q
      have hb : (1 + k * (30 * (B + 1))) + z ≤ t := by
        have hn : n - j = (n - (j + 1)) + 1 := by omega
        rw [hn, Nat.add_mul] at ht
        dsimp only [stepTime, z] at ht ⊢
        omega
      have hf : M.halt (M.runFrom r j).state = false := Bool.eq_false_iff.mpr (hn j hj')
      have he : M.step (M.runFrom r j) = M.runFrom r (j + 1) :=
        (M.runFrom_succ' _ j).symm
      have hs := spec_body_continue M c (M.runFrom r j) b σ B z hf hw
        (hB j hj'.le)
        (by rw [he]; exact hB (j + 1) hj') hσ
      rw [he] at hs
      apply (Triple.entails_wp_of_post hs ?_) c t ⟨rfl, hb⟩
      rintro v d z ⟨rfl, rfl, hz⟩
      refine ⟨j + 1, hj', rfl, ⟨hy, fun l ↦
        BitList.encodeTree ((M.runFrom r j).regs l), rfl, ?_⟩, hz⟩
      intro l
      simpa only [BitList.length_encodeTree] using hB j hj'.le l
    · have hj : j = n := by omega
      subst j
      have hf : M.halt (M.runFrom r n).state = true := hh
      unfold body
      simp only [hf, ↓reduceIte]
      vcgen
      exact ⟨⟨hy, σ, hw, hσ⟩, by omega⟩

end Complexity.TreeMachine.Simulation.Program

namespace Complexity.TreeMachine.Simulation

open TreeMachine.Simulation.Program Work Std.WP

variable {k : ℕ} [NeZero k] {Q : Type} [FinEnum Q]

/-- Load a tree, simulate its source run, and serialize the selected output register. -/
def Program.program (M : TreeMachine Id k Q) (i o : Fin k) :
    StackMachine.Program (Work k) Bool Unit := do
  init i
  let b ← Program.loopOn StackMachine.Program.idle (body M) (M.q₀, false)
  StackMachine.Program.IO.emitStack (data b o)

/-- The native stack program computes the serialized result and preserves unused credits. -/
theorem Program.spec_program (M : TreeMachine Id k Q)
    {x a : Tree} {t s : ℕ} (h : M.ComputesInTimeAndSpace x a t s) (q : ℕ) :
    Triple ((program M 0 0).verify (StackMachine.Program.semantics
      (BitList.encodeTree x).toArray))
      (fun c b ↦ c = (StackMachine.execution (BitList.encodeTree x)).init () ∧
        (6 * x.size + 5) + t * stepTime k (x.size + k + t) +
          (3 * (x.size + k + t) + 3) + q ≤ b)
      (fun _ c b ↦ c.output = (BitList.encodeTree a).toArray ∧ q ≤ b) () := by
  obtain ⟨n, hn, hh, ha, _, _⟩ := h.exists_haltsAt
  let B := x.size + k + t
  have hm (j : ℕ) : (M.run (Cfg k Q) x j).mass ≤ B := h.space_of_time.mass_le j
  have hi := spec_init (k := k) 0 x (t * stepTime k B + (3 * B + 3) + q)
  have hl := spec_loop M (M.initInput x) (loadedCfg 0 x) false n B (3 * B + 2 + q)
    (rep_loaded M.q₀ 0 x B) hh.1 hh.2 (fun j _ ↦ hm j)
  rw [show (M.initInput x : Cfg k Q).state = M.q₀ from
    M.state_initInput (Config := Cfg k Q) x] at hl
  have he (b : Bool) (c : StackMachine.Cfg (Work k) Bool Unit (BitList.encodeTree x).toArray)
      (hr : Rep (M.run (Cfg k Q) x n) b c B) :
      Triple ((StackMachine.Program.IO.emitStack (data b 0)).verify
        (StackMachine.Program.semantics (BitList.encodeTree x).toArray))
        (fun d z ↦ d = c ∧ 3 * B + 2 + q ≤ z)
        (fun _ d z ↦ d.output = (BitList.encodeTree a).toArray ∧ q ≤ z) () := by
    obtain ⟨hy, σ, hw, _⟩ := hr
    have ht : c.stacks (data b 0) = BitList.encodeTree a := by
      rw [hw, contents_data, ha]
    have hb : a.size ≤ B := by
      rw [← ha]
      exact ((M.run (Cfg k Q) x n).reg_size_le_mass 0).trans (hm n)
    have hs := Program.spec_exact_budget_le
      (fun z ↦ StackMachine.Program.IO.spec_emitStack c (data b 0) z)
      (m := 3 * B + 2) (by simp only [ht, BitList.length_encodeTree]; omega) q
    constructor
    apply Triple.entails_wp_of_post hs
    rintro _ d z ⟨rfl, hz⟩
    exact ⟨by simp [hy, ht], hz⟩
  have hn' := Nat.mul_le_mul_right (stepTime k B) hn
  unfold program
  vcgen [hi, hl, he]
  case vc1 =>
    rename_i c b hc
    exact ⟨hc.1, by simpa only [B, Nat.add_assoc] using hc.2⟩
  case vc2 =>
    rename_i c b hc u d z hd
    exact ⟨hd.1, by omega⟩
  all_goals simp_all only [Controller.run]

/-- Compile the serialized tree simulator to its native stack controller. -/
def compiler (M : TreeMachine Id k Q) := StackMachine.Program.compile (program M 0 0)

/-- Initialization, bounded source transitions, and final serialization. -/
def timeBound (k N W : ℕ) : ℕ :=
  (6 * N + 5) + W * Program.stepTime k (N + k + W) + (3 * (N + k + W) + 3)

/-- Each stack grows by at most one cell per transition. -/
def spaceBound (k N W : ℕ) : ℕ := (2 * k + 3) * timeBound k N W

/-- Every bounded tree computation is simulated through ordinary local stack operations. -/
theorem computesInTimeAndSpace (M : TreeMachine Id k Q)
    {x a : Tree} {t s : ℕ} (h : M.ComputesInTimeAndSpace x a t s) :
    (compiler M).ComputesInTimeAndSpace (BitList.encodeTree x) (BitList.encodeTree a)
      (timeBound k x.size t) (spaceBound k x.size t) := by
  have hs := Program.spec_program M h 0
  simp only [Nat.add_zero, Nat.zero_le, and_true] at hs
  simpa only [compiler, timeBound, spaceBound, card_work] using
    StackMachine.Program.computesInTimeAndSpace (program M 0 0) hs

end Complexity.TreeMachine.Simulation
