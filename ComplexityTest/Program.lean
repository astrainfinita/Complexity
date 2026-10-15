/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Models.TuringMachine.Program.Specification.History

set_option experimental.vcgen true

open Complexity (TM)
open Complexity.Controller (History)
open Complexity.TM
open Std.WP

namespace ProgramTest

-- The read result chooses a finite continuation. The program contains no input-length counter.
def eraseAfterRead : TM.Program (Fin 1) Bool Unit := do
  Program.write 0 true
  let a ← Program.read 0
  Program.emit a
  Program.move 0 .pos
  Program.write 0 true
  Program.write 0 default
  Program.move 0 .neg
  Program.write 0 default

def start : History (Cfg (Fin 1) Bool Unit #[]) (Action (Fin 1) Bool Unit) :=
  History.nil ((rawExecution []).init ())

-- Both cells are blank at the end, but both remain part of the visited footprint.
def finish : Cfg (Fin 1) Bool Unit #[] :=
  { (rawExecution []).init () with output := #[true] }

theorem finish_space {s : History (Cfg (Fin 1) Bool Unit #[]) (Action (Fin 1) Bool Unit)}
    (h : s.visited = fun _ ↦ ⟨(0, 1), by decide⟩) : s.space = 2 := by
  simp [History.space, h]

theorem eraseAfterRead_spec :
    Triple (eraseAfterRead.verify (Program.semantics #[])) (fun s b ↦ s = start ∧ b = 8)
      (fun _ s b ↦ s.last = finish ∧ s.visited = (fun _ ↦ ⟨(0, 1), by decide⟩) ∧ b = 0) () := by
  unfold eraseAfterRead
  vcgen
  all_goals simp_all [Program.idle, start,
    Cfg.workSymbols, SignType.cast, finish, Fin.eq_zero]
  constructor
  · ext i j <;> simp [Fin.eq_zero]
    by_cases h : (0 : ℤ) = j <;> by_cases h' : (1 : ℤ) = j <;> simp [h, h']
  · rfl

theorem eraseAfterRead_computesWithin :
    eraseAfterRead.compile.ComputesWithin [] [true] 8 2 := by
  apply Program.computesWithin (P := fun s b ↦ s = start ∧ b = 8)
    (hp := ⟨rfl, rfl⟩)
  constructor
  apply Triple.entails_wp_of_post eraseAfterRead_spec
  intro a s b h
  rcases h with ⟨hl, hv, _⟩
  exact ⟨by rw [hl]; rfl, (finish_space hv).le⟩
end ProgramTest
