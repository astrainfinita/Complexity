/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TuringMachine.Program.Specification.Trace
public import Complexity.Models.TreeMachine.Simulation.Program.Correctness
public import Complexity.Models.TreeMachine.Simulation.BitList.Input
public import Complexity.Models.TreeMachine.Simulation.BitList.Output
public import Complexity.Models.TuringMachine.Program.Call.Buffered
public import Complexity.Models.TuringMachine.Program.Word.Configuration
public import Mathlib.Tactic.GCongr

/-! # Tree computations as computations on raw bit strings

The input list occupies one source register; all other registers start at `nil`.
The target controller constructs the simulator input in a work buffer, calls the
tree simulator, and decodes its buffered output back to the original list.
Neither input nor output of the complete machine carries a tree serialization layer.
-/

@[expose] public section

set_option experimental.vcgen true

namespace Complexity.TreeMachine.Simulation.BitList

open TM Std.WP

variable {k : ℕ} [NeZero k] {Q : Type} [FinEnum Q]

/-- Encode, simulate, and decode, with ordinary raw-bit external input and output. -/
def program (M : TreeMachine Id k Q) :
    TM.Program ((Fin (2 * k + 1)) ⊕ Bool) (Option Bool) Unit := do
  Input.program (Sum.inr false)
  TM.Program.Word.rewind (Sum.inr false)
  TM.Program.BufferedCall.program (Simulation.compiler M)
  TM.Program.Word.rewind (Sum.inr true)
  output (Sum.inr true)

/-- A single finite controller, independent of the input and the asserted resource bounds. -/
def compiler (M : TreeMachine Id k Q) :=
  TM.Program.compile (program M)

/-- A polynomial bound including construction, both buffer rewinds, and decoding. -/
def timeBound (k n t : ℕ) : ℕ :=
  Compiler.timeBound k (4 * n + 1) t + 200 * (n + k + t + 1)

/-- A conservative bound counting every visited work cell, including both buffers. -/
def spaceBound (k n t : ℕ) : ℕ := ((2 * k + 1) + 2) * (timeBound k n t + 1)

private theorem simulation_time_mono {k N N' t : ℕ} (h : N ≤ N') :
    Compiler.timeBound k N t ≤ Compiler.timeBound k N' t := by
  unfold Compiler.timeBound Program.stepTime
  gcongr

omit [FinEnum Q] in
private theorem output_length_le (M : TreeMachine Id k Q)
    {xs ys : List Bool} {t s : ℕ}
    (h : M.ComputesInTimeAndSpace (Tree.encodeBitList xs) (Tree.encodeBitList ys) t s) :
    ys.length ≤ 4 * xs.length + 1 + k + t := by
  have ho := h.space_of_time.output_size_le_space
  have hx := Tree.size_encodeBitList_le xs
  have hy := Tree.length_le_size_encodeBitList ys
  omega

private theorem spec_finish {κ : Type} [DecidableEq κ] {zs : Array (Option Bool)} (j : κ)
    (ys : List Bool) :
    Triple ((do
      TM.Program.Word.rewind j
      output j).verify (TM.Program.cfgSemantics zs))
      (fun c b ↦ c.workTapes j = IntMemory.ofArray ((payload ys).toArray.map some) ∧
        c.workPos j = ((payload ys).length : ℤ) ∧ c.output = #[] ∧
        (3 * (payload ys).length + 4) + (12 * ys.length + 2) ≤ b)
      (fun _ c _ ↦ c.output = ys.toArray.map some) () := by
  constructor
  rintro c b ⟨hw, hp, hy, hb⟩
  have h₁ := TM.Program.Word.spec_rewind_cfg_le c j (payload ys) (payload ys).length
    (12 * ys.length + 2)
    (by simpa [TM.Program.Word.tape, IntMemory.ofList] using hw) hp le_rfl
  let d := { c with workPos := Function.update c.workPos j 0 }
  have h₂ := spec_output d j ys 0 hw (by simp [d])
  obtain ⟨n₁, a₁, c₁, hn₁, he₁, rfl, hb₁⟩ := h₁.le_wp c b ⟨rfl, hb⟩
  obtain ⟨n₂, a₂, c₂, hn₂, he₂, rfl, _⟩ := h₂.le_wp d (b - n₁) ⟨rfl, by omega⟩
  refine ⟨n₁ + n₂, a₂, outputCfg d j ys, by omega,
    Complexity.Program.Exec.bind he₁ he₂, ?_⟩
  change c.output ++ ys.toArray.map some = ys.toArray.map some
  simp [hy]

/-- A bounded computation on list trees yields a bounded computation on the original
bit strings. The complete machine performs both encoding conversions itself. -/
theorem computesInTimeAndSpace (M : TreeMachine Id k Q)
    {xs ys : List Bool} {t s : ℕ}
    (h : M.ComputesInTimeAndSpace (Tree.encodeBitList xs) (Tree.encodeBitList ys) t s) :
    (compiler M).ComputesInTimeAndSpace (xs.map some) (ys.map some)
      (timeBound k xs.length t) (spaceBound k xs.length t) := by
  let j : (Fin (2 * k + 1)) ⊕ Bool := .inr false
  let l : (Fin (2 * k + 1)) ⊕ Bool := .inr true
  let c : TM.Cfg ((Fin (2 * k + 1)) ⊕ Bool) (Option Bool) Unit (Input.input xs) :=
    (TM.rawExecution (Input.input xs).toList).init ()
  let d := Input.result c j
  let e := { d with workPos := Function.update d.workPos j 0 }
  let u := Compiler.timeBound k (Tree.encodeBitList xs).size t
  let v := Compiler.spaceBound k (Tree.encodeBitList xs).size t
  let z := (3 * (payload ys).length + 4) + (12 * ys.length + 2)
  have hm : (Simulation.compiler M).ComputesInTimeAndSpace
      ((payload xs).map some) ((payload ys).map some)
      u v := by
    simpa only [TreeMachine.code,
      ← payload_eq_encodeTree xs, ← payload_eq_encodeTree ys] using
      Compiler.computesInTimeAndSpace M h
  have hj (q : Fin (2 * k + 1)) : Sum.inl q ≠ j := by
    simp [j]
  have hl : l ≠ j := by
    simp [j, l]
  have h₁ := Input.spec_program c j ((3 * (payload xs).length + 4) + u + z)
    (by rfl) (by rfl) (by rfl)
  have h₂ := TM.Program.Word.spec_rewind_cfg_le d j (payload xs) (payload xs).length (u + z)
    (by simp [d, Input.result, TM.Program.Word.tape, IntMemory.ofList])
    (by simp [d, Input.result]) le_rfl
  have h₃ := TM.Program.BufferedCall.spec_of_computes (Simulation.compiler M) e z hm
    (fun q ↦ by simp [e, d, Input.result, c, hj q])
    (fun q ↦ by simp [e, d, Input.result, c, hj q])
    (by
      change e.workTapes j = _
      simp [e, d, Input.result, TM.Program.Word.tape, IntMemory.ofList])
    (by change e.workPos j = 0; simp [e])
    (by change e.workTapes l = ∅; simp [e, d, Input.result, c, hl])
    (by change e.workPos l = 0; simp [e, d, Input.result, c, hl])
  have h₄ := spec_finish (zs := Input.input xs) l ys
  dsimp only [j, l] at h₁ h₂ h₃ h₄
  have hs : Triple ((program M).verify (TM.Program.cfgSemantics (Input.input xs)))
      (fun a b ↦ a = c ∧ (7 * xs.length + 3) +
        (3 * (payload xs).length + 4) + u + z ≤ b)
      (fun _ a _ ↦ a.output = ys.toArray.map some) () := by
    unfold program
    vcgen [h₁, h₂, h₃, h₄]
    all_goals simp_all [TM.Program.Word.tape, IntMemory.ofList, e, d, Input.result, c,
      TM.Cfg.setWorkPos, z, j, l] <;> omega
  have hb : (7 * xs.length + 3) +
      (3 * (payload xs).length + 4) + u + z ≤ timeBound k xs.length t := by
    have h₁ := length_payload_le xs
    have h₂ := length_payload_le ys
    have h₃ := output_length_le M h
    have h₄ : u ≤ Compiler.timeBound k (4 * xs.length + 1) t :=
      simulation_time_mono (Tree.size_encodeBitList_le xs)
    unfold timeBound z
    omega
  simpa only [compiler, spaceBound, Input.input, Array.toList_map, List.toList_toArray,
    Fintype.card_sum, Fintype.card_fin, Fintype.card_bool] using
    TM.Program.cfg_computesInTimeAndSpace hs ⟨rfl, hb⟩

end Complexity.TreeMachine.Simulation.BitList
