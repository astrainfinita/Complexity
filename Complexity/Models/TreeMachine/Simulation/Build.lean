/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Simulation.Basic
public import Complexity.Models.TreeMachine.StackProgram
public import Complexity.Control.Program.Bound

/-! # Rebuilding one register from an unchanged source bank -/

@[expose] public section

set_option experimental.vcgen true

namespace Complexity.TreeMachine.Simulation.Program

open StackMachine.Program Work Std.WP
open StackMachine.Program.Tree (project spec_project spec_pair projectTime_le)

variable {k : ℕ} {Q : Type} {xs : Array Bool}

/-- Construct one register in the spare bank from the unchanged source bank. -/
def make (b : Bool) (a : Action k Q) (i : Fin k) : StackMachine.Program (Work k) Bool Unit := do
  let d := data (!b) i
  match a.writeAt i with
  | none | some .nop => Word.copy (data b i) d (.scratch .temp)
  | some (.left _ j) =>
      project (data b j) d (.scratch .saved) (.scratch .temp) (.scratch .counter) false
  | some (.right _ j) =>
      project (data b j) d (.scratch .saved) (.scratch .temp) (.scratch .counter) true
  | some (.pair _ j l) => StackMachine.Program.Tree.pair (data b j) (data b l) d (.scratch .temp)

/-- Clear the old destination before constructing its replacement. -/
def build (b : Bool) (a : Action k Q) (i : Fin k) : StackMachine.Program (Work k) Bool Unit := do
  Word.clear (data (!b) i)
  make b a i

/-- Constructing a register preserves the source bank and restores all scratch stacks. -/
@[spec] theorem spec_make (c : StackMachine.Cfg (Work k) Bool Unit xs) (b : Bool)
    (a : Action k Q) (i : Fin k) (ρ : Fin k → Complexity.Tree) (B q : ℕ)
    (hd : c.stacks (data (!b) i) = [])
    (hr : ∀ j, c.stacks (data b j) = BitList.encodeTree (ρ j))
    (hc : ∀ j : Scratch, c.stacks (.scratch j) = [])
    (hB : ∀ j, (ρ j).size ≤ B) :
    Triple ((make b a i).verify (semantics xs))
      (fun s t ↦ s = c ∧ 20 * (B + 1) + q ≤ t)
      (fun _ s t ↦ s = c.setStack (data (!b) i) (BitList.encodeTree (a.op.eval ρ i)) ∧
        q ≤ t) () := by
  have hcopy := Program.spec_exact_budget_le (fun z ↦ Word.spec_copy c (data b i) (data (!b) i)
    (.scratch .temp) z (by simp) (by simp) (by simp) (hc .temp))
    (m := 20 * (B + 1)) (by simp only [hr, BitList.length_encodeTree]; have := hB i; omega) q
  simp only [hr, hd, List.append_nil] at hcopy
  have hproject (j : Fin k) (right : Bool) := Program.spec_exact_budget_le
    (fun z ↦ spec_project c (data b j) (data (!b) i)
      (.scratch .saved) (.scratch .temp) (.scratch .counter) (ρ j) [] right z
      (by simp) (by simp [hr])
      (hc .saved) (hc .temp) (hc .counter)) (m := 20 * (B + 1))
    (by have := projectTime_le (ρ j) right; have := hB j; omega) q
  cases h : a.writeAt i with
  | none =>
    have he : a.op.eval ρ i = ρ i := a.regs_apply_of_none ⟨a.state, ρ⟩ h
    simpa only [make, h, he] using hcopy
  | some op =>
    obtain ⟨ho, hi⟩ := a.writeAt_eq_some_iff.mp h
    cases op with
    | nop => simp at hi
    | left l j =>
      cases Option.some.inj hi
      simpa only [make, h, hd, List.append_nil, ho, Op.eval_left,
        Function.update_self, Bool.false_eq_true, ↓reduceIte] using hproject j false
    | right l j =>
      cases Option.some.inj hi
      simpa only [make, h, hd, List.append_nil, ho, Op.eval_right,
        Function.update_self, ↓reduceIte] using hproject j true
    | pair l j m =>
      cases Option.some.inj hi
      have ht := Program.spec_exact_budget_le (fun z ↦ spec_pair c (data b j) (data b m)
        (data (!b) i) (.scratch .temp) (BitList.encodeTree (ρ j)) (BitList.encodeTree (ρ m)) z
        (by simp) (by simp) (by simp) (by simp) (by simp) (hr j) (hr m) (hc .temp))
        (m := 20 * (B + 1))
        (by simp only [BitList.length_encodeTree]; have := hB j; have := hB m; omega) q
      simpa only [make, h, hd, List.append_nil, ho, Op.eval_pair,
        Function.update_self, BitList.encodeTree] using ht

/-- Clearing the previous word and rebuilding leave all other stacks unchanged. -/
@[spec] theorem spec_build (c : StackMachine.Cfg (Work k) Bool Unit xs) (b : Bool)
    (a : Action k Q) (i : Fin k) (ρ : Fin k → Complexity.Tree) (σ : Fin k → List Bool)
    (B q : ℕ) (hw : c.stacks = contents b (fun j ↦ BitList.encodeTree (ρ j)) σ)
    (hρ : ∀ j, (ρ j).size ≤ B) (hσ : ∀ j, (σ j).length ≤ B) :
    Triple ((build b a i).verify (semantics xs))
      (fun s t ↦ s = c ∧ 30 * (B + 1) + q ≤ t)
      (fun _ s t ↦ s = c.setStack (data (!b) i) (BitList.encodeTree (a.op.eval ρ i)) ∧
        q ≤ t) () := by
  let d := c.setStack (data (!b) i) []
  have h₁ := Program.spec_exact_budget_le
    (fun z ↦ Word.spec_clear c (data (!b) i) z)
    (m := 10 * (B + 1)) (by simp only [hw, contents_other]; have := hσ i; omega)
    (20 * (B + 1) + q)
  have h₂ := spec_make d b a i ρ B q (by simp [d])
    (fun j ↦ by simp [d, hw])
    (fun j ↦ by simp [d, hw]) hρ
  unfold build
  vcgen [h₁, h₂]
  all_goals simp_all [d] <;> omega

end Complexity.TreeMachine.Simulation.Program
