/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Simulation.Program.Compiler
public import Complexity.Models.TreeMachine.Simulation.Program.Representation
public import Complexity.Models.TuringMachine.Program.Word.IO
public import Complexity.Control.Program.Bound

/-! # Initializing a register bank from one input tree -/

@[expose] public section

set_option experimental.vcgen true

namespace Complexity.TreeMachine.Simulation.Program

open Compiler TM.Program.Word Std.WP

variable {k : ℕ}

/-- The designated register contains the input; other source registers contain `nil`.
The spare bank remains empty, every work head is at zero, and the input is consumed. -/
def loadedCfg (i : Fin k) (x : Tree) :
    TM.Cfg (Fin (2 * k + 1)) (Option Bool) Unit (TreeMachine.code x).toArray where
  state := ()
  inputPos := Fin.last ((TreeMachine.code x).toArray.size + 1)
  workTapes := tapes false (fun j ↦ BitList.encodeTree (TreeMachine.input i x j)) (fun _ ↦ [])
  workPos := fun _ ↦ 0
  output := #[]

private theorem loaded_boot (i : Fin k) (x : Tree) :
    loaded (apply (boot i)
      ((TM.rawExecution (TreeMachine.code x)).init ()))
      (data false i) (BitList.encodeTree x)
      (Fin.last ((TreeMachine.code x).toArray.size + 1)) = loadedCfg i x := by
  have he (b : Bool) : (∅ : IntMemory (Option Bool)).set 0 (some b) =
      IntMemory.ofList [some b] := by
    simpa using IntMemory.set_ofList_length ([] : List (Option Bool)) (some b)
  apply TM.Cfg.ext
  · rfl
  · rfl
  · funext j
    rcases data_or_counter false j with ⟨l, rfl⟩ | ⟨l, rfl⟩ | rfl
    · by_cases h : l = i
      · subst l
        simp [loadedCfg]
      · have hd : data false l ≠ data false i := fun h' ↦ h (data_injective false h')
        have hval : (data false l).val < k := l.isLt
        simp [loadedCfg, boot, data_ne_counter,
          hd, hval, h, he, tape]
    · have hd := (data_ne_other false i l).symm
      simp only [loaded_workTapes, Function.update_of_ne hd, loadedCfg, tapes_other]
      have hval : ¬(data true l).val < k := by change ¬k + l.val < k; omega
      simp [boot, data_ne_counter, hval]
    · simp [loadedCfg, (data_ne_counter false i).symm, boot, he]
  · rfl
  · rfl

/-- A single parallel initialization action followed by loading the external tree. -/
theorem spec_init (i : Fin k) (x : Tree) (q : ℕ) :
    Triple ((init i).verify (TM.Program.cfgSemantics (TreeMachine.code x).toArray))
      (fun s t ↦ s = (TM.rawExecution (TreeMachine.code x)).init () ∧ (6 * x.size + 7) + q ≤ t)
      (fun _ s t ↦ s = loadedCfg i x ∧ q ≤ t) () := by
  let d := apply (boot i)
    ((TM.rawExecution (κ := Fin (2 * k + 1)) (TreeMachine.code x)).init ())
  have h := Program.spec_exact_budget_le
    (fun z ↦ spec_load_cfg d (data false i) (BitList.encodeTree x) z
      (by simp [TreeMachine.code]) rfl
      (by simp [d, boot, data_ne_counter]) rfl)
    (m := 6 * x.size + 6) (by simp) q
  have hl : Triple
      ((load (data false i)).verify (TM.Program.cfgSemantics (TreeMachine.code x).toArray))
      (fun s t ↦ s = d ∧ (6 * x.size + 6) + q ≤ t)
      (fun _ s t ↦ s = loadedCfg i x ∧ q ≤ t) () :=
    ⟨h.entails_wp_of_post (by
      rintro a s t ⟨hs, ht⟩
      exact ⟨hs.trans (loaded_boot i x), ht⟩)⟩
  unfold init
  vcgen [hl]
  all_goals simp_all [d]
  all_goals omega

end Complexity.TreeMachine.Simulation.Program
