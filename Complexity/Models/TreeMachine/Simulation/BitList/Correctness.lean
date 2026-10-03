/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Simulation.Correctness
public import Complexity.Models.TreeMachine.Simulation.BitList.Input
public import Complexity.Models.TreeMachine.Simulation.BitList.Output

/-! # Tree computations on raw bit strings through stack programs

The stack program constructs the input register directly, runs the shared tree
simulation loop, and decodes the result stack. Its resource bounds use the
native stack-machine semantics.
-/

@[expose] public section

set_option experimental.vcgen true

namespace Complexity.TreeMachine.Simulation.BitList

open StackMachine.Program TreeMachine.Simulation.Program Work Std.WP

variable {k : ℕ} [NeZero k] {Q : Type} [FinEnum Q]

/-- Encode, simulate, and decode entirely within the same stack configuration. -/
def program (M : TreeMachine Id k Q) : StackMachine.Program (Work k) Bool Unit := do
  act (boot 0)
  Input.program (data false 0) (.scratch .temp)
  let b ← Program.loopOn idle (body M) (M.q₀, false)
  output (data b 0)

/-- Stack transitions for input conversion, source simulation, and output decoding. -/
def timeBound (k n t : ℕ) : ℕ :=
  9 * n + 6 + t * Program.stepTime k (4 * n + 1 + k + t) +
    (7 * (4 * n + 1 + k + t) + 3)

/-- A bounded tree computation yields a complete stack-program specification on raw bits. -/
theorem spec_program (M : TreeMachine Id k Q)
    {xs ys : List Bool} {t s : ℕ}
    (h : M.ComputesInTimeAndSpace (Tree.encodeBitList xs) (Tree.encodeBitList ys) t s) :
    Triple ((program M).verify (semantics xs.toArray))
      (fun c b ↦ c = (StackMachine.execution xs).init () ∧ timeBound k xs.length t ≤ b)
      (fun _ c _ ↦ c.output = ys.toArray) () := by
  obtain ⟨n, hn, hh, ha, _, _⟩ := h.exists_haltsAt
  let B := 4 * xs.length + 1 + k + t
  let c : StackMachine.Cfg (Work k) Bool Unit xs.toArray :=
    (StackMachine.execution xs).init ()
  let d := apply (boot (0 : Fin k)) c
  let e := Input.result d (data false 0)
  have hm (j : ℕ) : (M.run (Cfg k Q) (Tree.encodeBitList xs) j).mass ≤ B := by
    have hm := h.space_of_time.mass_le j
    have hx := Tree.size_encodeBitList_le xs
    dsimp only [B]
    omega
  have hr : Rep (M.initInput (Tree.encodeBitList xs)) false e B := by
    refine ⟨?_, fun _ ↦ [], ?_, ?_⟩
    · simp [e, d, c, boot, idle]
    · funext j
      rcases j with ⟨b, i⟩ | j
      · cases b <;> by_cases hi : i = 0 <;>
          simp [e, d, c, boot, idle, contents, hi, input, payload_eq_encodeTree,
            StackMachine.Op.apply]
      · simp [e, d, c, boot, idle, contents, StackMachine.Op.apply]
    · simp
  have hy : ys.length ≤ B := by
    have hz := (M.run (Cfg k Q) (Tree.encodeBitList xs) n).reg_size_le_mass (0 : Fin k)
    have hl := Tree.length_le_size_encodeBitList ys
    rw [ha] at hz
    exact hl.trans (hz.trans (hm n))
  have hi := Input.spec_program d (data false 0) (.scratch .temp)
    (t * stepTime k B + (7 * B + 3)) (by simp)
    (by simp [d, c, boot, idle, StackMachine.Op.apply])
    (by simp [d, c, boot, idle])
  have hl := spec_loop M (M.initInput (Tree.encodeBitList xs)) e false n B
    (7 * B + 2) hr hh.1 hh.2 (fun j _ ↦ hm j)
  rw [show (M.initInput (Tree.encodeBitList xs) : Cfg k Q).state = M.q₀ from
    M.state_initInput (Config := Cfg k Q) _] at hl
  have ho (b : Bool) (d : StackMachine.Cfg (Work k) Bool Unit xs.toArray)
      (hr : Rep (M.run (Cfg k Q) (Tree.encodeBitList xs) n) b d B) :
      Triple ((output (data b 0)).verify (semantics xs.toArray))
        (fun c q ↦ c = d ∧ 7 * B + 2 ≤ q)
        (fun _ c _ ↦ c.output = ys.toArray) () := by
    obtain ⟨hy', σ, hw, _⟩ := hr
    have he : d.stacks (data b 0) = payload ys ++ [] := by
      rw [hw, contents_data, ha, ← payload_eq_encodeTree, List.append_nil]
    have hs := spec_output d (data b 0) ys [] 0 he
    constructor
    rintro c q ⟨rfl, hq⟩
    apply (Triple.entails_wp_of_post hs ?_) _ q ⟨rfl, by omega⟩
    rintro a c q ⟨rfl, _⟩
    simp [hy']
  have hn' := Nat.mul_le_mul_right (stepTime k B) hn
  unfold program
  vcgen [hi, hl, ho]
  all_goals simp_all [timeBound, c, d, e, B, Controller.run]
  all_goals omega

/-- Compile the complete raw-bit computation to its native stack controller. -/
def compiler (M : TreeMachine Id k Q) := (program M).compile

/-- The time bound controls the size of all stacks in both banks and scratch space. -/
def spaceBound (k n t : ℕ) : ℕ := (2 * k + 3) * timeBound k n t

/-- The complete stack program implements the original bit-string computation. -/
theorem computesInTimeAndSpace (M : TreeMachine Id k Q)
    {xs ys : List Bool} {t s : ℕ}
    (h : M.ComputesInTimeAndSpace (Tree.encodeBitList xs) (Tree.encodeBitList ys) t s) :
    (compiler M).ComputesInTimeAndSpace xs ys
      (timeBound k xs.length t) (spaceBound k xs.length t) := by
  simpa only [compiler, timeBound, spaceBound, card_work] using
    StackMachine.Program.computesInTimeAndSpace (program M) (spec_program M h)

end Complexity.TreeMachine.Simulation.BitList
