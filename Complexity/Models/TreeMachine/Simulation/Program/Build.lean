/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Simulation.Program.Compiler
public import Complexity.Models.TreeMachine.Program.Pair
public import Complexity.Models.TreeMachine.Program.Project
public import Complexity.Models.TuringMachine.Program.Word.Clear
public import Complexity.Control.Program.Bound

/-! # Constructing a simulated register by composing verified programs -/

@[expose] public section

set_option experimental.vcgen true

namespace Complexity.TreeMachine.Simulation.Program

open TM.Program.Word TreeMachine.Program Std.WP

variable {k : ℕ} {Q : Type} {xs : Array (Option Bool)}

/-- The exact cost of filling one empty destination register. -/
def makeTime (a : Action k Q) (i : Fin k) (ρ : Fin k → Tree) : ℕ :=
  match a.writeAt i with
  | none | some .nop => 9 * (ρ i).size + 10
  | some (.left _ j) => projectTime (ρ j) false
  | some (.right _ j) => projectTime (ρ j) true
  | some (.pair _ j l) => 9 * ((ρ j).size + (ρ l).size) + 20

/-- The complete configuration after constructing a single destination register. -/
def built (c : TM.Cfg (Fin (2 * k + 1)) (Option Bool) Unit xs) (b : Bool)
    (a : Action k Q) (i : Fin k) (ρ : Fin k → Tree) :
    TM.Cfg (Fin (2 * k + 1)) (Option Bool) Unit xs :=
  { c with
    workTapes := Function.update c.workTapes (Compiler.data (!b) i)
      (tape (BitList.encodeTree (a.op.eval ρ i))) }

/-- Filling an empty word uses only the source bank, also when a source equals the destination
register logically: the source and destination physical banks remain disjoint. -/
@[spec]
theorem spec_make (c : TM.Cfg (Fin (2 * k + 1)) (Option Bool) Unit xs) (b : Bool)
    (a : Action k Q) (i : Fin k) (ρ : Fin k → Tree) (q : ℕ)
    (hw : c.workTapes (Compiler.data (!b) i) = tape [])
    (ht : ∀ j, c.workTapes (Compiler.data b j) = tape (BitList.encodeTree (ρ j)))
    (hc : c.workTapes (Compiler.counter k) = IntMemory.ofList [some true])
    (hp : c.workPos = fun _ ↦ 0) :
    Triple ((make b a i).verify (TM.Program.cfgSemantics xs))
      (fun s z ↦ s = c ∧ z = makeTime a i ρ + q)
      (fun _ s z ↦ s = built c b a i ρ ∧ z = q) () := by
  have hd (j : Fin k) : Compiler.data (!b) i ≠ Compiler.data b j :=
    (Compiler.data_ne_other b j i).symm
  have hdi : c.workPos (Compiler.data (!b) i) = 0 := by simp [hp]
  have hs (j : Fin k) : c.workPos (Compiler.data b j) = 0 := by simp [hp]
  have hck : c.workPos (Compiler.counter k) = 0 := by simp [hp]
  cases h : a.writeAt i with
  | none =>
    have he : a.op.eval ρ i = ρ i := a.regs_apply_of_none ⟨a.state, ρ⟩ h
    simpa [make, makeTime, h, built, he, hp] using
      spec_append_rewind_cfg c (Compiler.data (!b) i) (Compiler.data b i)
        [] [] (BitList.encodeTree (ρ i)) q (hd i)
        (by simpa using ht i) (by simpa using hs i) hw (by simpa using hdi)
  | some o =>
    obtain ⟨ho, hi⟩ := a.writeAt_eq_some_iff.mp h
    cases o with
    | nop => simp at hi
    | left l j =>
      have he : l = i := Option.some.inj hi
      subst l
      simpa [make, makeTime, h, built, projected, ho] using
        spec_project_cfg c (Compiler.data (!b) i) (Compiler.data b j) (Compiler.counter k)
          (ρ j) false q (hd j) (Compiler.data_ne_counter (!b) i)
          (Compiler.data_ne_counter b j) hw (ht j) hc hdi (hs j) hck
    | right l j =>
      have he : l = i := Option.some.inj hi
      subst l
      simpa [make, makeTime, h, built, projected, ho] using
        spec_project_cfg c (Compiler.data (!b) i) (Compiler.data b j) (Compiler.counter k)
          (ρ j) true q (hd j) (Compiler.data_ne_counter (!b) i)
          (Compiler.data_ne_counter b j) hw (ht j) hc hdi (hs j) hck
    | pair l j m =>
      have he : l = i := Option.some.inj hi
      subst l
      simpa [make, makeTime, h, built, paired, ho, BitList.encodeTree] using
        spec_pair_cfg c (Compiler.data (!b) i) (Compiler.data b j) (Compiler.data b m)
          (BitList.encodeTree (ρ j)) (BitList.encodeTree (ρ m)) q
          (hd j) (hd m) hw (ht j) (ht m) hdi (hs j) (hs m)

/-- A single destination register needs a linear number of work actions. -/
theorem makeTime_le (a : Action k Q) (i : Fin k) (ρ : Fin k → Tree) (B : ℕ)
    (hρ : ∀ j, (ρ j).size ≤ B) : makeTime a i ρ ≤ 30 * (B + 1) := by
  unfold makeTime
  cases h : a.writeAt i with
  | none => have := hρ i; dsimp; omega
  | some o =>
    cases o with
    | nop => have := hρ i; dsimp; omega
    | left l j => have := projectTime_le (ρ j) false; have := hρ j; dsimp; omega
    | right l j => have := projectTime_le (ρ j) true; have := hρ j; dsimp; omega
    | pair l j m => have := hρ j; have := hρ m; dsimp; omega

/-- Exact clearing and construction cost, before replacing word sizes by a common bound. -/
def buildTime (a : Action k Q) (i : Fin k) (ρ : Fin k → Tree)
    (σ : Fin k → List Bool) : ℕ := 6 * (σ i).length + 6 + makeTime a i ρ

private theorem spec_build_exact (c : TM.Cfg (Fin (2 * k + 1)) (Option Bool) Unit xs) (b : Bool)
    (a : Action k Q) (i : Fin k) (ρ : Fin k → Tree) (σ : Fin k → List Bool) (q : ℕ)
    (hw : c.workTapes = Compiler.tapes b (fun j ↦ BitList.encodeTree (ρ j)) σ)
    (hp : c.workPos = fun _ ↦ 0) :
    Triple ((build b a i).verify (TM.Program.cfgSemantics xs))
      (fun s z ↦ s = c ∧ z = buildTime a i ρ σ + q)
      (fun _ s z ↦ s = built c b a i ρ ∧ z = q) () := by
  let d := cleared c (Compiler.data (!b) i)
  have hi : c.workPos (Compiler.data (!b) i) = 0 := by simp [hp]
  have he : Function.update c.workPos (Compiler.data (!b) i) 0 = c.workPos := by
    rw [← hi, Function.update_eq_self]
  have h₁ := spec_clear_cfg c (Compiler.data (!b) i) (σ i) (makeTime a i ρ + q)
    (by simp [hw]) hi
  have h₂ := spec_make d b a i ρ q
    (by simp [d, cleared])
    (fun j ↦ by simp [d, cleared, Compiler.data_ne_other, hw])
    (by simp [d, cleared, (Compiler.data_ne_counter (!b) i).symm, hw])
    (by simpa [d, cleared, he] using hp)
  have hf : built d b a i ρ = built c b a i ρ := by simp [built, d, cleared, he]
  unfold build
  vcgen [h₁, h₂]
  case vc1 =>
    rename_i s z h
    exact ⟨h.1, by simp only [buildTime] at h; omega⟩
  case vc2 =>
    rename_i h
    exact h
  case vc3 =>
    rename_i h
    exact ⟨h.1.trans hf, h.2⟩

/-- One register is built from the old bank, retaining its complete configuration and
any reserved continuation budget. No traversal history appears in the caller's assertions. -/
@[spec]
theorem spec_build (c : TM.Cfg (Fin (2 * k + 1)) (Option Bool) Unit xs) (b : Bool)
    (a : Action k Q) (i : Fin k) (ρ : Fin k → Tree) (σ : Fin k → List Bool) (B q : ℕ)
    (hw : c.workTapes = Compiler.tapes b (fun j ↦ BitList.encodeTree (ρ j)) σ)
    (hp : c.workPos = fun _ ↦ 0) (hρ : ∀ j, (ρ j).size ≤ B)
    (hσ : ∀ j, (σ j).length ≤ B) :
    Triple ((build b a i).verify (TM.Program.cfgSemantics xs))
      (fun s z ↦ s = c ∧ 50 * (B + 1) + q ≤ z)
      (fun _ s z ↦ s = built c b a i ρ ∧ q ≤ z) () := by
  apply Program.spec_exact_budget_le (fun q ↦ spec_build_exact c b a i ρ σ q hw hp)
  have := makeTime_le a i ρ B hρ
  have := hσ i
  simp only [buildTime]
  omega

end Complexity.TreeMachine.Simulation.Program
