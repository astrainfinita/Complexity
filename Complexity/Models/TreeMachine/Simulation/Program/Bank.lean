/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Simulation.Program.Step
public import Complexity.Models.TreeMachine.Simulation.Program.Build

/-! # Reading and rebuilding the represented register bank -/

@[expose] public section

set_option experimental.vcgen true

namespace Complexity.TreeMachine.Simulation.Program

open Compiler Std.WP

variable {k : ℕ} {Q : Type} {xs : Array (Option Bool)}

/-- Read every represented tree root in one local transition without changing tape data. -/
theorem spec_roots (c : TM.Cfg (Fin (2 * k + 1)) (Option Bool) Unit xs) (b : Bool)
    (ρ : Fin k → Tree) (σ : Fin k → List Bool)
    (hw : c.workTapes = tapes b (fun i ↦ BitList.encodeTree (ρ i)) σ)
    (hp : c.workPos = fun _ ↦ 0)
    (n : ℕ) (hn : 0 < n) :
    Triple ((roots b).verify (TM.Program.cfgSemantics xs))
      (fun s t ↦ s = c ∧ t = n)
      (fun v s t ↦ v = (fun i ↦ Tree.root (ρ i)) ∧ s = c ∧ t = n - 1) () := by
  have hr := TM.Program.cfg_spec_observeBits
    (fun v : (Option Bool) × (Fin (2 * k + 1) → (Option Bool)) ↦
      fun i ↦ v.2 (data b i) == some true) xs c n hn ()
  unfold roots
  vcgen [hr]
  all_goals simp_all [workSymbols_roots c b ρ σ hw hp]

private theorem body_continue_of_bank (M : TreeMachine Id k Q) (o : Fin k)
    (c : TM.Cfg (Fin (2 * k + 1)) (Option Bool) Unit xs) (r : Cfg k Q) (b : Bool)
    (σ : Fin k → List Bool) (R q : ℕ) (hf : M.halt r.state = false)
    (hw : c.workTapes = tapes b (fun i ↦ BitList.encodeTree (r.regs i)) σ)
    (hp : c.workPos = fun _ ↦ 0)
    (hb : Triple
      ((Complexity.Program.forFin (build b ((M.transition r.state (observe r)).run))).verify
        (TM.Program.cfgSemantics xs))
      (fun s t ↦ s = c ∧ k * R + q ≤ t)
      (fun _ s t ↦
        s = bankCfg c (!b) (M.step r).regs (fun i ↦ BitList.encodeTree (r.regs i)) ∧ q ≤ t) ()) :
    Triple ((body M o (r.state, b)).verify (TM.Program.cfgSemantics xs))
      (fun s t ↦ s = c ∧ (1 + k * R) + q ≤ t)
      (fun v s t ↦ v = .inl ((M.step r).state, !b) ∧
        s = bankCfg c (!b) (M.step r).regs (fun i ↦ BitList.encodeTree (r.regs i)) ∧ q ≤ t) () := by
  have hr := spec_roots c b r.regs σ hw hp
  have hs : (M.step r).state = ((M.transition r.state (observe r)).run).state := by
    rw [TreeMachine.step_eq, hf]
    rfl
  have hb' (v : Fin k → Bool) (hv : v = observe r) : Triple
      ((Complexity.Program.forFin (build b ((M.transition r.state v).run))).verify
        (TM.Program.cfgSemantics xs))
      (fun s t ↦ s = c ∧ k * R + q ≤ t)
      (fun _ s t ↦
        s = bankCfg c (!b) (M.step r).regs (fun i ↦ BitList.encodeTree (r.regs i)) ∧ q ≤ t) () := by
    simpa only [hv] using hb
  unfold body
  simp only [hf, Bool.false_eq_true, ↓reduceIte]
  vcgen [hr, hb']
  all_goals simp_all only [Sum.inl.injEq, Prod.mk.injEq, and_true, true_and]
  all_goals first | rfl | omega

/-- Rebuild all destination registers and swap the interpretation of the two physical banks. -/
theorem spec_bank (c : TM.Cfg (Fin (2 * k + 1)) (Option Bool) Unit xs) (b : Bool)
    (a : Action k Q) (ρ : Fin k → Tree) (σ : Fin k → List Bool) (B q : ℕ)
    (hρ : ∀ i, (ρ i).size ≤ B) (hν : ∀ i, (a.op.eval ρ i).size ≤ B)
    (hσ : ∀ i, (σ i).length ≤ B) :
    Triple ((Complexity.Program.forFin (build b a)).verify (TM.Program.cfgSemantics xs))
      (fun s t ↦ s = bankCfg c b ρ σ ∧ k * (50 * (B + 1)) + q ≤ t)
      (fun _ s t ↦ s = bankCfg c (!b) (a.op.eval ρ)
        (fun i ↦ BitList.encodeTree (ρ i)) ∧ q ≤ t) () := by
  apply spec_bank_of_register c b a ρ (a.op.eval ρ) σ (50 * (B + 1)) q
  intro i z
  have hσ' : ∀ j, (buffer σ (fun j ↦ BitList.encodeTree (a.op.eval ρ j)) i.val j).length ≤ B := by
    intro j
    unfold buffer
    split
    · simpa only [BitList.length_encodeTree] using hν j
    · exact hσ j
  have h := spec_build (cycleCfg c b ρ (a.op.eval ρ) σ i.val) b a i ρ
    (buffer σ (fun j ↦ BitList.encodeTree (a.op.eval ρ j)) i.val) B z rfl rfl hρ hσ'
  simpa only [built, cycleCfg_next] using h

/-- A nonhalting source step is executed by the actual monadic simulator body. -/
theorem spec_body_continue (M : TreeMachine Id k Q) (o : Fin k)
    (c : TM.Cfg (Fin (2 * k + 1)) (Option Bool) Unit xs) (r : Cfg k Q) (b : Bool)
    (σ : Fin k → List Bool) (B q : ℕ) (hf : M.halt r.state = false)
    (hw : c.workTapes = tapes b (fun i ↦ BitList.encodeTree (r.regs i)) σ)
    (hp : c.workPos = fun _ ↦ 0)
    (hρ : ∀ i, (r.regs i).size ≤ B) (hν : ∀ i, ((M.step r).regs i).size ≤ B)
    (hσ : ∀ i, (σ i).length ≤ B) :
    Triple ((body M o (r.state, b)).verify (TM.Program.cfgSemantics xs))
      (fun s t ↦ s = c ∧ (1 + k * (50 * (B + 1))) + q ≤ t)
      (fun v s t ↦ v = .inl ((M.step r).state, !b) ∧
        s = bankCfg c (!b) (M.step r).regs (fun i ↦ BitList.encodeTree (r.regs i)) ∧ q ≤ t) () := by
  have he : (M.step r).regs = ((M.transition r.state (observe r)).run).op.eval r.regs := by
    rw [TreeMachine.step_eq, hf]
    rfl
  apply body_continue_of_bank M o c r b σ (50 * (B + 1)) q hf hw hp
  have hb := spec_bank c b ((M.transition r.state (observe r)).run) r.regs σ B q hρ
    (by simpa only [← he] using hν) hσ
  simpa only [bankCfg_eq c b r.regs σ hw hp, ← he] using hb

end Complexity.TreeMachine.Simulation.Program
