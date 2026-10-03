/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Simulation.Build

/-! # One simulated tree-machine transition -/

@[expose] public section

set_option experimental.vcgen true

namespace Complexity.TreeMachine.Simulation.Program

open StackMachine.Program Work Std.WP

variable {k : ℕ} {Q : Type} {xs : Array Bool}

/-- Simulate one source step, or return the current register bank on halting. -/
def body (M : TreeMachine Id k Q) (s : Q × Bool) :
    StackMachine.Program (Work k) Bool ((Q × Bool) ⊕ Bool) := do
  if M.halt s.1 then
    pure (.inr s.2)
  else
    let v ← roots s.2
    let a := (M.transition s.1 v).run
    Program.forFin (build s.2 a)
    pure (.inl (a.state, !s.2))

private theorem spec_roots (c : StackMachine.Cfg (Work k) Bool Unit xs) (b : Bool)
    (ρ : Fin k → Complexity.Tree) (σ : Fin k → List Bool)
    (hw : c.stacks = contents b (fun i ↦ BitList.encodeTree (ρ i)) σ) (n : ℕ) (hn : 0 < n) :
    Triple ((roots b).verify (semantics xs))
      (fun s t ↦ s = c ∧ t = n)
      (fun v s t ↦ v = (fun i ↦ Complexity.Tree.root (ρ i)) ∧ s = c ∧ t = n - 1) () := by
  have he : (fun i ↦ ((c.stacks (data b i)).head? == some true)) =
      fun i ↦ Complexity.Tree.root (ρ i) := by
    funext i
    rw [hw, contents_data]
    cases ρ i <;> rfl
  unfold roots
  vcgen
  all_goals simp_all

/-- Each register block rebuilds just its destination in the spare bank. -/
private theorem spec_bank (c : StackMachine.Cfg (Work k) Bool Unit xs) (b : Bool)
    (a : Action k Q) (ρ : Fin k → Complexity.Tree) (σ : Fin k → List Bool) (B q : ℕ)
    (hρ : ∀ i, (ρ i).size ≤ B) (hν : ∀ i, (a.op.eval ρ i).size ≤ B)
    (hσ : ∀ i, (σ i).length ≤ B) :
    Triple ((Program.forFin (build b a)).verify (semantics xs))
      (fun s t ↦ s = bank c b ρ σ ∧ k * (30 * (B + 1)) + q ≤ t)
      (fun _ s t ↦ s = bank c (!b) (a.op.eval ρ)
        (fun i ↦ BitList.encodeTree (ρ i)) ∧ q ≤ t) () := by
  have h := Program.spec_forFin (build b a) (semantics xs)
    (I := fun n s t ↦
      s = cycle c b ρ (a.op.eval ρ) σ n ∧ (k - n) * (30 * (B + 1)) + q ≤ t) (by
    intro i
    have hσ' : ∀ j, (buffer σ (fun j ↦ BitList.encodeTree (a.op.eval ρ j)) i.val j).length ≤ B := by
      intro j
      unfold buffer
      split
      · simpa only [BitList.length_encodeTree] using hν j
      · exact hσ j
    have hs := spec_build (cycle c b ρ (a.op.eval ρ) σ i.val) b a i ρ
      (buffer σ (fun j ↦ BitList.encodeTree (a.op.eval ρ j)) i.val) B
      ((k - (i.val + 1)) * (30 * (B + 1)) + q) rfl hρ hσ'
    rw [cycle_next] at hs
    constructor
    rintro s t ⟨hc, ht⟩
    apply hs.le_wp s t
    refine ⟨hc, ?_⟩
    have hk : k - i.val = (k - (i.val + 1)) + 1 := by omega
    rw [hk, Nat.add_mul] at ht
    omega)
  simpa using h

@[spec] theorem spec_body_continue (M : TreeMachine Id k Q)
    (c : StackMachine.Cfg (Work k) Bool Unit xs) (r : Cfg k Q) (b : Bool)
    (σ : Fin k → List Bool) (B q : ℕ) (hf : M.halt r.state = false)
    (hw : c.stacks = contents b (fun i ↦ BitList.encodeTree (r.regs i)) σ)
    (hρ : ∀ i, (r.regs i).size ≤ B) (hν : ∀ i, ((M.step r).regs i).size ≤ B)
    (hσ : ∀ i, (σ i).length ≤ B) :
    Triple ((body M (r.state, b)).verify (semantics xs))
      (fun s t ↦ s = c ∧ (1 + k * (30 * (B + 1))) + q ≤ t)
      (fun v s t ↦ v = .inl ((M.step r).state, !b) ∧
        s = bank c (!b) (M.step r).regs (fun i ↦ BitList.encodeTree (r.regs i)) ∧ q ≤ t) () := by
  have he : (M.step r).regs = ((M.transition r.state (observe r)).run).op.eval r.regs := by
    simp [Controller.step_eq, hf]
  have hs : (M.step r).state = ((M.transition r.state (observe r)).run).state := by
    simp [Controller.step_eq, hf]
  have hr := spec_roots c b r.regs σ hw
  have hb (v : Fin k → Bool) (hv : v = observe r) : Triple
      ((Program.forFin (build b ((M.transition r.state v).run))).verify (semantics xs))
      (fun s t ↦ s = c ∧ k * (30 * (B + 1)) + q ≤ t)
      (fun _ s t ↦ s = bank c (!b) (M.step r).regs
        (fun i ↦ BitList.encodeTree (r.regs i)) ∧ q ≤ t) () := by
    subst v
    simpa only [bank_self c b r.regs σ hw, ← he] using
      spec_bank c b ((M.transition r.state (observe r)).run) r.regs σ B q hρ
        (by simpa only [← he] using hν) hσ
  unfold body
  simp only [hf, Bool.false_eq_true, ↓reduceIte]
  vcgen [hr, hb]
  all_goals simp_all only [Sum.inl.injEq, Prod.mk.injEq, and_true, true_and]
  all_goals first | rfl | omega

end Complexity.TreeMachine.Simulation.Program
