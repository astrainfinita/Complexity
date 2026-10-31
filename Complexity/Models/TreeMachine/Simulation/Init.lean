/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Simulation.Bank
public import Complexity.Models.StackMachine.Program.IO

/-! # Loading one tree and initializing the remaining registers -/

@[expose] public section

set_option experimental.vcgen true

namespace Complexity.TreeMachine.Simulation.Program

open StackMachine.Program Work Std.WP

variable {k : ℕ}

/-- Initialize non-input registers to the one-bit code of `nil`. -/
def boot (i : Fin k) : StackMachine.Action (Work k) Bool :=
  { idle (κ := Work k) with work := fun j ↦ match j with
    | .data l => if l = i then .nop else .push false
    | _ => .nop }

/-- Initialize the source bank and load the input tree into register `i`. -/
def init (i : Fin k) : StackMachine.Program (Work k) Bool Unit := do
  act (boot i)
  IO.load (data i) (.scratch .temp)

/-- The source bank contains the input and empty trees, with every scratch stack empty. -/
@[simps -fullyApplied]
def loadedCfg (i : Fin k) (x : Complexity.Tree) :
    StackMachine.Cfg (Work k) Bool (BitList.encodeTree x).toArray where
  inputPos := Fin.last ((BitList.encodeTree x).toArray.size + 1)
  «stacks» := contents (input i x)
  output := #[]

private theorem loaded_boot (i : Fin k) (x : Complexity.Tree) :
    let c := apply (boot i) (StackMachine.Cfg.init (Work k) (BitList.encodeTree x))
    { c.setStack (data i) (BitList.encodeTree x ++ c.stacks (data i)) with
      inputPos := ⟨(BitList.encodeTree x).length + 1, by simp⟩ } = loadedCfg i x := by
  ext j <;> try rfl
  rcases j with l | j
  · by_cases h : l = i <;>
      simp [boot, idle, contents, h, input, StackMachine.Op.apply]
  · simp [boot, idle, contents, StackMachine.Op.apply]

@[spec] theorem spec_init (i : Fin k) (x : Complexity.Tree) (q : ℕ) :
    Triple ((init i).verify (semantics (BitList.encodeTree x).toArray))
      (fun s t ↦ s = StackMachine.Cfg.init (Work k) (BitList.encodeTree x) ∧
        (6 * x.size + 5) + q ≤ t)
      (fun _ s t ↦ s = loadedCfg i x ∧ q ≤ t) () := by
  let c := apply (boot i) (StackMachine.Cfg.init (Work k) (BitList.encodeTree x))
  have h := Program.spec_exact_budget_le (fun z ↦ IO.spec_load c (data i) (.scratch .temp) z
    (by simp) (by simp [c, boot, idle, StackMachine.Op.apply])
    (by simp [c, boot, idle])) (m := 6 * x.size + 4) (by simp) q
  simp only [c, loaded_boot] at h
  unfold init
  vcgen [h]
  all_goals (casesm* _ ∧ _; subst_vars; and_intros <;> first | rfl | omega)

end Complexity.TreeMachine.Simulation.Program
