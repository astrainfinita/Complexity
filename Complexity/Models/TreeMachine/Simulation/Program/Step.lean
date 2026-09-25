/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Simulation.Program.Compiler
public import Complexity.Models.TreeMachine.Simulation.Program.Representation
public import Complexity.Models.TuringMachine.Program.Specification.Configuration
public import Complexity.Control.Program.Bound

/-! # Composing register programs into a tree-machine transition -/

@[expose] public section

namespace Complexity.TreeMachine.Simulation.Program

open Compiler Std.WP

variable {k : ℕ} {Q : Type} {xs : Array (Option Bool)}

/-- A finite register traversal needs only a specification for each component. -/
theorem spec_bank_of_register (c : TM.Cfg (Fin (2 * k + 1)) (Option Bool) Unit xs) (b : Bool)
    (a : Action k Q) (ρ ν : Fin k → Tree) (σ : Fin k → List Bool) (R q : ℕ)
    (h : ∀ (i : Fin k) (z : ℕ),
      Triple ((build b a i).verify (TM.Program.cfgSemantics xs))
        (fun s t ↦ s = cycleCfg c b ρ ν σ i.val ∧ R + z ≤ t)
        (fun _ s t ↦ s = cycleCfg c b ρ ν σ (i.val + 1) ∧ z ≤ t) ()) :
    Triple ((Complexity.Program.forFin (build b a)).verify (TM.Program.cfgSemantics xs))
      (fun s t ↦ s = bankCfg c b ρ σ ∧ k * R + q ≤ t)
      (fun _ s t ↦ s = bankCfg c (!b) ν (fun i ↦ BitList.encodeTree (ρ i)) ∧ q ≤ t) () := by
  have hf : Triple
      ((Complexity.Program.forFin (build b a)).verify (TM.Program.cfgSemantics xs))
      (fun s t ↦ s = cycleCfg c b ρ ν σ 0 ∧ (k - 0) * R + q ≤ t)
      (fun _ s t ↦ s = cycleCfg c b ρ ν σ k ∧ (k - k) * R + q ≤ t) () := by
    apply Complexity.Program.spec_forFin (I := fun n s t ↦
      s = cycleCfg c b ρ ν σ n ∧ (k - n) * R + q ≤ t)
    intro i
    constructor
    rintro s t ⟨hs, ht⟩
    apply (h i ((k - (i.val + 1)) * R + q)).le_wp s t
    refine ⟨hs, ?_⟩
    have he : k - i.val = (k - (i.val + 1)) + 1 := by omega
    rw [he, Nat.add_mul] at ht
    omega
  simpa only [cycleCfg, buffer_zero, Nat.sub_zero, Nat.sub_self, Nat.zero_mul,
    Nat.zero_add, buffer_all, bankCfg, tapes_swap] using hf

end Complexity.TreeMachine.Simulation.Program
