/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Simulation.Build
public import Complexity.Models.StackMachine.Deterministic

/-! # One simulated tree-machine transition -/

@[expose] public section

set_option experimental.vcgen true

namespace Complexity.TreeMachine.Simulation.Program

open StackMachine.Program Work Std.WP

variable {k : ℕ} {Q : Type} {xs : Array Bool}

/-- Read the roots and update just the selected register. -/
def body (M : TreeMachine Id k Q) (q : Q) : StackMachine.Program (Work k) Bool (Q ⊕ Unit) := do
  if M.halt q then pure (.inr ())
  else
    let v ← roots
    let a := (M.transition q v).run
    build a.op
    pure (.inl a.state)

private theorem spec_roots (c : StackMachine.Cfg (Work k) Bool Unit xs)
    (ρ : Fin k → Complexity.Tree) (hw : c.stacks = contents ρ) (n : ℕ) (hn : 0 < n) :
    Triple (roots.verify (semantics xs))
      (fun s t ↦ s = c ∧ t = n)
      (fun v s t ↦ v = (fun i ↦ Complexity.Tree.root (ρ i)) ∧ s = c ∧ t = n - 1) () := by
  have he : (fun i ↦ ((c.stacks (data i)).head? == some true)) =
      fun i ↦ Complexity.Tree.root (ρ i) := by
    funext i
    rw [hw, contents_data]
    cases ρ i <;> rfl
  unfold roots
  vcgen
  all_goals simp_all

@[spec] theorem spec_body_continue (M : TreeMachine Id k Q)
    (c : StackMachine.Cfg (Work k) Bool Unit xs) (r : Cfg k Q) (q : ℕ)
    (hf : M.halt r.state = false) (hw : c.stacks = contents r.regs) :
    Triple ((body M r.state).verify (semantics xs))
      (fun s t ↦ s = c ∧
        39 * ((M.transition r.state (observe r)).run).sizeCost r + 3 * r.mass + q ≤ t)
      (fun v s t ↦ (v = .inl (M.step r).state ∧ s = bank c (M.step r).regs) ∧
        3 * (M.step r).mass + q ≤ t) () := by
  have he : (M.step r).regs = ((M.transition r.state (observe r)).run).op.eval r.regs := by
    simp [Controller.step_eq, hf]
  have hs : (M.step r).state = ((M.transition r.state (observe r)).run).state := by
    simp [Controller.step_eq, hf]
  have hp := ((M.transition r.state (observe r)).run).op.sizeCost_pos r.regs
  have hr := spec_roots c r.regs hw
  have hb (v : Fin k → Bool) (hv : v = observe r) :
      Triple ((build ((M.transition r.state v).run).op).verify (semantics xs))
        (fun s t ↦ s = c ∧
          38 * ((M.transition r.state (observe r)).run).sizeCost r + 3 * r.mass + q ≤ t)
        (fun _ s t ↦ s = bank c (M.step r).regs ∧ 3 * (M.step r).mass + q ≤ t) () := by
    subst v
    simpa only [Cfg.mass, Action.sizeCost, he] using
      spec_build c ((M.transition r.state (observe r)).run).op r.regs q hw
  unfold body
  simp only [hf, Bool.false_eq_true, ↓reduceIte]
  vcgen [hr, hb]
  all_goals simp_all only [Action.sizeCost, Sum.inl.injEq, and_true, true_and]
  all_goals first | rfl | omega

/-- At instruction boundaries, stack storage is exactly the source register mass. -/
@[simp] theorem mass_bank (c : StackMachine.Cfg (Work k) Bool Unit xs) (ρ : Fin k → Tree) :
    (bank c ρ).mass = ∑ i, (ρ i).size := by
  unfold StackMachine.Cfg.mass
  rw [Fintype.sum_equiv (proxy_equiv% (Work k)).symm _
    (fun i ↦ Sum.elim (fun i ↦ (ρ i).size) (fun _ ↦ 0) i)]
  · simp
  · intro i
    cases i with
    | data i => exact BitList.length_encodeTree (ρ i)
    | scratch i => rfl

end Complexity.TreeMachine.Simulation.Program
