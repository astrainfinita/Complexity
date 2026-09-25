/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TuringMachine.Program.Specification.Trace
public import Complexity.Models.TreeMachine.Simulation.Program.Init
public import Complexity.Models.TreeMachine.Simulation.Program.Bank
public import Complexity.Models.TreeMachine.Simulation.Program.Output
public import Complexity.Models.TuringMachine.Program.Specification.Configuration
public import Complexity.Models.TreeMachine.Deterministic

/-! # Total specifications for the monadic tree simulator -/

@[expose] public section

set_option experimental.vcgen true

namespace Complexity.TreeMachine.Simulation.Program

open Compiler Std.WP

variable {k : ℕ} {Q : Type} [FinEnum Q]

/-- The current bank stores the source registers, with every head at zero and bounded old words. -/
def Rep {xs : Array (Option Bool)} (r : Cfg k Q) (b : Bool)
    (c : TM.Cfg (Fin (2 * k + 1)) (Option Bool) Unit xs) (B : ℕ) : Prop :=
  c.workPos = (fun _ ↦ 0) ∧ c.output = #[] ∧
    ∃ σ, c.workTapes = tapes b (fun i ↦ BitList.encodeTree (r.regs i)) σ ∧
      ∀ i, (σ i).length ≤ B

/-- One loop entry, root observation, and a uniform allowance for every register block. -/
def stepTime (k B : ℕ) : ℕ := 2 + k * (50 * (B + 1))

end Complexity.TreeMachine.Simulation.Program

namespace Complexity.TreeMachine.Simulation.Compiler

/-- Initialization, bounded source transitions, and final serialization. -/
def timeBound (k N W : ℕ) : ℕ :=
  (6 * N + 7) + W * Program.stepTime k (N + k + W) + (3 * (N + k + W) + 3)

/-- The same conservative visited-cell bound as the original simulation proof. -/
def spaceBound (k N W : ℕ) : ℕ := (2 * k + 1) * (timeBound k N W + 1)

end Complexity.TreeMachine.Simulation.Compiler

namespace Complexity.TreeMachine.Simulation.Program

open Compiler Std.WP

variable {k : ℕ} {Q : Type} [FinEnum Q]

omit [FinEnum Q] in
private theorem rep_loaded (q : Q) (i : Fin k) (x : Tree) (B : ℕ) :
    Rep (Cfg.mk q (input i x)) false (loadedCfg i x) B := by
  refine ⟨rfl, rfl, fun _ ↦ [], rfl, ?_⟩
  simp

private theorem spec_loop_of_body {xs : Array (Option Bool)} (M : TreeMachine Id k Q)
    (r : Cfg k Q) (o : Fin k)
    (c₀ : TM.Cfg (Fin (2 * k + 1)) (Option Bool) Unit xs) (b₀ : Bool)
    (a : Tree) (n B : ℕ) (hr₀ : Rep r b₀ c₀ B)
    (hc : ∀ (j : ℕ), j < n → ∀ (b : Bool)
      (c : TM.Cfg (Fin (2 * k + 1)) (Option Bool) Unit xs) (q : ℕ),
      Rep (M.runFrom r j) b c B →
      Triple ((body M o ((M.runFrom r j).state, b)).verify
        (TM.Program.cfgSemantics xs))
        (fun s t ↦ s = c ∧ (1 + k * (50 * (B + 1))) + q ≤ t)
        (fun v s t ↦ v = .inl ((M.runFrom r (j + 1)).state, !b) ∧
          Rep (M.runFrom r (j + 1)) (!b) s B ∧ q ≤ t) ())
    (he : ∀ (b : Bool)
      (c : TM.Cfg (Fin (2 * k + 1)) (Option Bool) Unit xs),
      Rep (M.runFrom r n) b c B →
      Triple ((body M o ((M.runFrom r n).state, b)).verify
        (TM.Program.cfgSemantics xs))
        (fun s t ↦ s = c ∧ 3 * B + 2 ≤ t)
        (fun v s _ ↦ v = .inr () ∧ s.output = (TreeMachine.code a).toArray) ()) :
    Triple ((Complexity.Program.loopOn TM.Program.idle (body M o) (r.state, b₀)).verify
      (TM.Program.cfgSemantics xs))
      (fun s t ↦ s = c₀ ∧ n * stepTime k B + (3 * B + 3) ≤ t)
      (fun _ s _ ↦ s.output = (TreeMachine.code a).toArray) () := by
  let I : (Q × Bool) →
      TM.Cfg (Fin (2 * k + 1)) (Option Bool) Unit xs → ℕ → Prop :=
    fun v c t ↦ ∃ j ≤ n, v.1 = (M.runFrom r j).state ∧ Rep (M.runFrom r j) v.2 c B ∧
      (n - j) * stepTime k B + (3 * B + 3) ≤ t
  have hl : Triple
      ((Complexity.Program.loopOn TM.Program.idle (body M o) (r.state, b₀)).verify
        (TM.Program.cfgSemantics xs))
      (I (r.state, b₀)) (fun _ s _ ↦ s.output = (TreeMachine.code a).toArray) () := by
    apply TM.Program.cfg_spec_loopOn
    · rintro v c t ⟨j, hj, hq, hr, ht⟩
      omega
    · rintro ⟨r, b⟩
      constructor
      rintro c t ⟨j, hj, hq, hr, ht⟩
      dsimp only at hq
      subst r
      by_cases hj' : j < n
      · have hb : (1 + k * (50 * (B + 1))) +
            ((n - (j + 1)) * stepTime k B + (3 * B + 3)) ≤ t := by
          have hn : n - j = (n - (j + 1)) + 1 := by omega
          rw [hn, Nat.add_mul] at ht
          dsimp only [stepTime] at ht ⊢
          omega
        apply (Triple.entails_wp_of_post
          (hc j hj' b c ((n - (j + 1)) * stepTime k B + (3 * B + 3)) hr) ?_) c t ⟨rfl, hb⟩
        rintro v d z ⟨rfl, hd, hz⟩
        exact ⟨j + 1, by omega, rfl, hd, hz⟩
      · have hj : j = n := by omega
        subst j
        have hb : 3 * B + 2 ≤ t := by simpa using ht
        apply (Triple.entails_wp_of_post (he b c hr) ?_) c t ⟨rfl, hb⟩
        rintro v d z ⟨rfl, hd⟩
        exact hd
  constructor
  rintro c t ⟨hc, ht⟩
  subst c
  apply hl.le_wp c₀ t
  exact ⟨0, Nat.zero_le _, rfl, hr₀, by simpa using ht⟩

/-- Starting from any represented source configuration, the loop simulates its run
and serializes the chosen output register. The source and target need not be initial
configurations, and the target may have any external input. -/
theorem spec_loop {xs : Array (Option Bool)} (M : TreeMachine Id k Q)
    (r : Cfg k Q) (o : Fin k)
    (c₀ : TM.Cfg (Fin (2 * k + 1)) (Option Bool) Unit xs) (b₀ : Bool)
    (a : Tree) (n B : ℕ) (hr₀ : Rep r b₀ c₀ B)
    (hh : M.Halted (M.runFrom r n))
    (hn : ∀ j < n, ¬M.Halted (M.runFrom r j))
    (ha : (M.runFrom r n).regs o = a)
    (hm : ∀ j ≤ n, (M.runFrom r j).mass ≤ B) :
    Triple ((Complexity.Program.loopOn TM.Program.idle (body M o) (r.state, b₀)).verify
      (TM.Program.cfgSemantics xs))
      (fun s t ↦ s = c₀ ∧ n * stepTime k B + (3 * B + 3) ≤ t)
      (fun _ s _ ↦ s.output = (TreeMachine.code a).toArray) () := by
  apply spec_loop_of_body M r o c₀ b₀ a n B hr₀
  · intro j hj b c q hr
    obtain ⟨hp, hy, σ, hw, hσ⟩ := hr
    have hf : M.halt (M.runFrom r j).state = false := Bool.eq_false_iff.mpr (hn j hj)
    have he : M.step (M.runFrom r j) = M.runFrom r (j + 1) := (M.runFrom_succ' _ j).symm
    have hs := spec_body_continue M o c (M.runFrom r j) b σ B q hf hw hp
      (fun l ↦ ((M.runFrom r j).reg_size_le_mass l).trans (hm j (Nat.le_of_lt hj)))
      (fun l ↦ by
        rw [he]
        exact ((M.runFrom r (j + 1)).reg_size_le_mass l).trans
          (hm (j + 1) (Nat.succ_le_of_lt hj))) hσ
    rw [he] at hs
    constructor
    apply Triple.entails_wp_of_post hs
    rintro v d t ⟨hv, rfl, ht⟩
    refine ⟨hv, ?_, ht⟩
    refine ⟨rfl, hy, fun l ↦ BitList.encodeTree ((M.runFrom r j).regs l), rfl, ?_⟩
    intro l
    simpa only [BitList.length_encodeTree] using
      ((M.runFrom r j).reg_size_le_mass l).trans (hm j (Nat.le_of_lt hj))
  · intro b c hr
    obtain ⟨hp, hy, σ, hw, hσ⟩ := hr
    have hs := spec_body_halt M o c (M.runFrom r n) b a 0 hh
      (by rw [hw, tapes_data, ha]) (by simp only [hp]) hy
    have hb : a.size ≤ B := by
      rw [← ha]
      exact ((M.runFrom r n).reg_size_le_mass o).trans (hm n le_rfl)
    constructor
    rintro d t ⟨hd, ht⟩
    exact (Triple.entails_wp_of_post hs (fun _ _ _ h ↦ ⟨h.1, h.2.1⟩)) d t
      ⟨hd, by omega⟩

end Complexity.TreeMachine.Simulation.Program

namespace Complexity.TreeMachine.Simulation.Compiler

open Complexity.TreeMachine.Simulation.Program Std.WP

variable {k : ℕ} [NeZero k] {Q : Type} [FinEnum Q]

/-- Every bounded tree computation is simulated by the controller compiled from the
monadic program. Both target bounds are quadratic in initial tree size and time cost
for fixed register count. All implementation obligations are discharged by program specs. -/
theorem computesInTimeAndSpace (M : TreeMachine Id k Q)
    {x : Tree} {a : Tree} {t s : ℕ}
    (h : M.ComputesInTimeAndSpace x a t s) :
    (compiler M).ComputesInTimeAndSpace
      (TreeMachine.code x) (TreeMachine.code a)
      (timeBound k x.size t) (spaceBound k x.size t) := by
  obtain ⟨n, hn, hh, ha, _, _⟩ := h.exists_haltsAt
  let B := x.size + k + t
  have hm (j : ℕ) : (M.run (Cfg k Q) x j).mass ≤ B :=
    h.space_of_time.mass_le j
  have hi := spec_init (k := k) 0 x (t * stepTime k B + (3 * B + 3))
  have hl := spec_loop M (M.initInput x) 0
    (loadedCfg 0 x) false a n B (rep_loaded M.q₀ 0 x B) hh.1 hh.2 ha (fun j _ ↦ hm j)
  rw [show (M.initInput x : Cfg k Q).state = M.q₀ from
    M.state_initInput (Config := Cfg k Q) x] at hl
  have hs : Triple ((program M 0 0).verify (TM.Program.cfgSemantics ((TreeMachine.code x).toArray)))
      (fun c b ↦ c = (TM.rawExecution (TreeMachine.code x)).init () ∧
        b = timeBound k x.size t)
      (fun _ c _ ↦ c.output = (TreeMachine.code a).toArray) () := by
    unfold program
    vcgen [hi, hl]
    case vc1 =>
      rename_i c b hc
      refine ⟨hc.1, ?_⟩
      rw [hc.2]
      simp only [timeBound, B, Nat.add_assoc]
      exact Nat.le_refl _
    case vc2 =>
      rename_i c b hc u d z hd
      refine ⟨hd.1, ?_⟩
      exact (Nat.add_le_add_right (Nat.mul_le_mul_right (stepTime k B) hn) _).trans hd.2
  simpa only [compiler, spaceBound, Fintype.card_fin] using
    TM.Program.cfg_computesInTimeAndSpace hs ⟨rfl, rfl⟩

end Complexity.TreeMachine.Simulation.Compiler
