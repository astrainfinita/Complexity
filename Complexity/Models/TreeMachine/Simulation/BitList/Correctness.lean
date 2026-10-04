/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Simulation.Correctness
public import Complexity.Models.TreeMachine.Simulation.BitList.Input
public import Complexity.Models.TreeMachine.Simulation.BitList.Output

/-! # Linear tree-machine simulation on ordinary bit-string input and output -/

@[expose] public section

set_option experimental.vcgen true

namespace Complexity.TreeMachine.Simulation.BitList

open StackMachine.Program TreeMachine.Simulation.Program Work Std.WP
open Controller (History)

variable {k : ℕ} [NeZero k] {Q : Type} [FinEnum Q]

/-- Initialize the empty registers and encode the external input in register zero. -/
def loadInput : StackMachine.Program (Work k) Bool Unit := do
  act (boot 0)
  Input.program (data 0) (.scratch .temp)

/-- Encode, simulate, and decode using one register bank. -/
def program (M : TreeMachine Id k Q) : StackMachine.Program (Work k) Bool Unit := do
  loadInput
  Program.loopOn idle (body M) M.q₀
  output (data 0)

/-- Input conversion, amortized source execution, and output decoding. -/
def timeBound (k n t : ℕ) : ℕ :=
  (9 * n + 6) + (40 * t + 3 * (4 * n + 1 + k) + 1) + (7 * (4 * n + 1 + k + t) + 2)

/-- A bounded tree computation gives linear target time and independent linear space. -/
theorem spec_program (M : TreeMachine Id k Q)
    {xs ys : List Bool} {t s : ℕ}
    (h : M.ComputesInTimeAndSpace (Tree.encodeBitList xs) (Tree.encodeBitList ys) t s) :
    Triple ((program M).verify (historySemantics xs.toArray))
      (fun c b ↦ c = History.nil ((StackMachine.execution xs).init ()) ∧
        timeBound k xs.length t ≤ b)
      (fun _ c _ ↦ c.last.output = ys.toArray ∧
        c.configSup StackMachine.Cfg.mass ≤ spaceBound k s) () := by
  obtain ⟨n, _, hh, ha, ht, _⟩ := h.exists_haltsAt
  let c : StackMachine.Cfg (Work k) Bool Unit xs.toArray := (StackMachine.execution xs).init ()
  let d := apply (boot (0 : Fin k)) c
  let e := Input.result d (data 0)
  have hx := (Tree.length_le_size_encodeBitList xs).trans h.input_size_le_space
  have hp : 0 < s := (Tree.encodeBitList xs).size_pos.trans_le h.input_size_le_space
  have hr : e.stacks = contents (input 0 (Tree.encodeBitList xs)) := by
    funext j
    rcases j with j | j
    · by_cases hj : j = 0 <;>
        simp [e, d, c, boot, idle, contents, hj, input, payload_eq_encodeTree,
          StackMachine.Op.apply]
    · simp [e, d, c, boot, idle, contents, StackMachine.Op.apply]
  have hi₀ : Triple (loadInput.verify (semantics xs.toArray))
      (fun s b ↦ s = c ∧ 9 * xs.length + 6 ≤ b)
      (fun _ s b ↦ s = e ∧ 0 ≤ b) () := by
    have hi := Input.spec_program d (data 0) (.scratch .temp) 0 (by simp)
      (by simp [d, c, boot, idle, StackMachine.Op.apply])
      (by simp [d, c, boot, idle])
    unfold loadInput
    vcgen [hi]
    all_goals simp_all [d, e]; omega
  have hi := spec_history hi₀
    (macro_space_le c (s := s) (by simp [c, StackMachine.Cfg.mass]) (by omega))
    ((40 * t + 3 * (4 * xs.length + 1 + k) + 1) + (7 * (4 * xs.length + 1 + k + t) + 2))
  have hl := spec_loop M (M.initInput (Tree.encodeBitList xs)) e n s (7 * ys.length + 2) hr
    hh.1 hh.2 (fun j _ ↦ h.mass_le j)
  rw [show (M.initInput (Tree.encodeBitList xs) : Cfg k Q).state = M.q₀ from
    M.state_initInput (Config := Cfg k Q) _] at hl
  let f := bank e (M.run (Cfg k Q) (Tree.encodeBitList xs) n).regs
  have he : f.stacks (data 0) = payload ys ++ [] := by
    simp [f, ha, payload_eq_encodeTree]
  have hout := spec_output f (data 0) ys [] 0 he
  simp only [Nat.add_zero] at hout
  have hy := (Tree.length_le_size_encodeBitList ys).trans h.output_size_le_space
  have ho := spec_history hout
    (macro_space_le f (by simpa [f, Cfg.mass] using h.mass_le n) (by omega)) 0
  have hm₀ := M.mass_input_le (Tree.encodeBitList xs)
  have hsize := Tree.size_encodeBitList_le xs
  have houtsize := (Tree.length_le_size_encodeBitList ys).trans h.output_size_le_mass_add_time
  unfold program
  vcgen [hi, hl, ho]
  all_goals simp_all [c, d, e, f, timeBound, Controller.run, Controller.runHistory,
    boot, idle, StackMachine.Op.apply, StackMachine.Cfg.mass] <;> omega

/-- Compile the complete raw-bit computation to its native stack controller. -/
def compiler (M : TreeMachine Id k Q) := (program M).compile

/-- Both resource bounds refer to the complete computation on the original bit strings. -/
theorem computesInTimeAndSpace (M : TreeMachine Id k Q)
    {xs ys : List Bool} {t s : ℕ}
    (h : M.ComputesInTimeAndSpace (Tree.encodeBitList xs) (Tree.encodeBitList ys) t s) :
    (compiler M).ComputesInTimeAndSpace xs ys
      (timeBound k xs.length t) (spaceBound k s) :=
  StackMachine.Program.computesInTimeAndSpace_history (spec_program M h)

end Complexity.TreeMachine.Simulation.BitList
