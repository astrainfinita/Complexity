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
def boot (i : Fin k) : StackMachine.Action (Work k) Bool Unit :=
  { idle (κ := Work k) with work := fun j ↦ match j with
    | .data false l => if l = i then .nop else .push false
    | _ => .nop }

/-- Initialize the source bank and load the input tree into register `i`. -/
def init (i : Fin k) : StackMachine.Program (Work k) Bool Unit := do
  act (boot i)
  IO.load (data false i) (.scratch .temp)

/-- The source bank contains the input and empty trees, with every scratch stack empty. -/
@[simps -fullyApplied]
def loadedCfg (i : Fin k) (x : Complexity.Tree) :
    StackMachine.Cfg (Work k) Bool Unit (BitList.encodeTree x).toArray where
  state := ()
  inputPos := Fin.last ((BitList.encodeTree x).toArray.size + 1)
  «stacks» := contents false (fun j ↦ BitList.encodeTree (input i x j)) (fun _ ↦ [])
  output := #[]

private theorem loaded_boot (i : Fin k) (x : Complexity.Tree) :
    let c := apply (boot i) ((StackMachine.execution (κ := Work k) (BitList.encodeTree x)).init ())
    { c.setStack (data false i) (BitList.encodeTree x ++ c.stacks (data false i)) with
      inputPos := ⟨(BitList.encodeTree x).length + 1, by simp⟩ } = loadedCfg i x := by
  ext j <;> try rfl
  rcases j with ⟨b, l⟩ | j
  · cases b <;> by_cases h : l = i <;>
      simp [boot, idle, contents, h, input, StackMachine.Op.apply]
  · simp [boot, idle, contents, StackMachine.Op.apply]

@[spec] theorem spec_init (i : Fin k) (x : Complexity.Tree) (q : ℕ) :
    Triple ((init i).verify (semantics (BitList.encodeTree x).toArray))
      (fun s t ↦ s = (StackMachine.execution (κ := Work k) (BitList.encodeTree x)).init () ∧
        (6 * x.size + 5) + q ≤ t)
      (fun _ s t ↦ s = loadedCfg i x ∧ q ≤ t) () := by
  let c := apply (boot i) ((StackMachine.execution (κ := Work k) (BitList.encodeTree x)).init ())
  have h := Program.spec_exact_budget_le (fun z ↦ IO.spec_load c (data false i) (.scratch .temp) z
    (by simp) (by simp [c, boot, idle, StackMachine.Op.apply])
    (by simp [c, boot, idle])) (m := 6 * x.size + 4) (by simp) q
  simp only [c, loaded_boot] at h
  unfold init
  vcgen [h]
  all_goals simp_all
  all_goals omega

end Complexity.TreeMachine.Simulation.Program
