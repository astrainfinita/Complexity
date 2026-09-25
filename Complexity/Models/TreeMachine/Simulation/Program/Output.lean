/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Simulation.Program.Compiler
public import Complexity.Models.TuringMachine.Program.Word.IO
public import Complexity.Control.Program.Bound

/-! # Output production by the compositional tree simulator -/

@[expose] public section

set_option experimental.vcgen true

namespace Complexity.TreeMachine.Simulation.Program

open Std.WP TM.Program.Word

variable {k : ℕ} {Q : Type} {xs : Array (Option Bool)}

/-- Once the source halts, its output register is emitted and the simulation loop exits.
The remaining credits are available to the caller; no invariant on the other tapes is needed. -/
@[spec]
theorem spec_body_halt (M : TreeMachine Id k Q) (o : Fin k)
    (c : TM.Cfg (Fin (2 * k + 1)) (Option Bool) Unit xs) (r : TreeMachine.Cfg k Q)
    (b : Bool) (a : Tree) (q : ℕ) (hf : M.halt r.state = true)
    (ht : c.workTapes (Compiler.data b o) = tape (BitList.encodeTree a))
    (hp : c.workPos (Compiler.data b o) = 0) (hy : c.output = #[]) :
    Triple ((body M o (r.state, b)).verify (TM.Program.cfgSemantics xs))
      (fun s t ↦ s = c ∧ (3 * a.size + 2) + q ≤ t)
      (fun v s t ↦ v = .inr () ∧ s.output = (TreeMachine.code a).toArray ∧ q ≤ t) () := by
  have he := Complexity.Program.spec_exact_budget_le
    (fun z ↦ spec_emit_cfg c (Compiler.data b o) (BitList.encodeTree a) z ht hp)
    (m := 3 * a.size + 2) (by simp) q
  unfold body
  simp only [hf, ↓reduceIte]
  vcgen [he]
  case vc1 =>
    rename_i s t hs u v t' hv
    rcases hv with ⟨rfl, hq⟩
    exact ⟨by simp [hy, TreeMachine.code], hq⟩

end Complexity.TreeMachine.Simulation.Program
