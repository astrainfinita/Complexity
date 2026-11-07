/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Tactic.TreeProgram.Translation

/-! # Implementations of basic Boolean and list tests

A translation unfolds only the definitions it translates. These core operations are referenced
by other definitions, so their implementations are selected here once.
-/

@[expose] public section

open Complexity TreeProgram

namespace Complexity.TreeProgram.Source

open Internal (HasProgramInO)

-- The implementations stated with the rules, registered once `program` is defined.
attribute [scoped program] List.hasProgramIn_reverse List.hasProgramIn_append Prod.hasProgramIn_fst
  Prod.hasProgramIn_snd Sigma.hasProgramIn_fst Sigma.hasProgramIn_snd BitList.hasProgramIn_increment

theorem _root_.Bool.hasProgramIn_not :
    HasProgramIn Bool.not hole(⊢ program) IsO(fun _ => 1) IsO(fun _ => 1) := by
  abstract_hole program using programNot
  refine HasProgramInO.toHasProgramIn ?_
  fill_hole program in
    exact .of_encode (by intro x; cases x <;> rfl)
      (by source_fun_prop :
        HasProgramInO (fun x => match x with | false => true | true => false) _
          (fun _ => 1) (fun _ => 1))

theorem hasProgramIn_boolAnd : HasProgramIn (fun x : Bool × Bool => x.1 && x.2) hole(⊢ program)
    IsO(fun _ => 1) IsO(fun _ => 1) := by
  abstract_hole program using programBoolAnd
  refine HasProgramInO.toHasProgramIn ?_
  fill_hole program in
    exact .of_encode (by rintro ⟨a, b⟩; cases a <;> cases b <;> rfl)
      (by source_fun_prop :
        HasProgramInO (fun x : Bool × Bool => match x.1 with | false => false | true => x.2) _
          (fun _ => 1) (fun _ => 1))

theorem hasProgramIn_boolOr : HasProgramIn (fun x : Bool × Bool => x.1 || x.2) hole(⊢ program)
    IsO(fun _ => 1) IsO(fun _ => 1) := by
  abstract_hole program using programBoolOr
  refine HasProgramInO.toHasProgramIn ?_
  fill_hole program in
    exact .of_encode (by rintro ⟨a, b⟩; cases a <;> cases b <;> rfl)
      (by source_fun_prop :
        HasProgramInO (fun x : Bool × Bool => match x.1 with | false => x.2 | true => true) _
          (fun _ => 1) (fun _ => 1))

attribute [local program] Bool.hasProgramIn_not in
theorem hasProgramIn_boolXor : HasProgramIn (fun x : Bool × Bool => xor x.1 x.2) hole(⊢ program)
    IsO(fun _ => 1) IsO(fun _ => 1) := by
  abstract_hole program using programBoolXor
  refine HasProgramInO.toHasProgramIn ?_
  fill_hole program in
    exact .of_encode (by rintro ⟨a, b⟩; cases a <;> cases b <;> rfl)
      (by source_fun_prop :
        HasProgramInO (fun x : Bool × Bool => match x.1 with | false => x.2 | true => !x.2) _
          (fun _ => 1) (fun _ => 1))

theorem hasProgramIn_boolBeq : HasProgramIn (fun x : Bool × Bool => x.1 == x.2) hole(⊢ program)
    IsO(fun _ => 1) IsO(fun _ => 1) := by
  abstract_hole program using programBoolBeq
  refine HasProgramInO.toHasProgramIn ?_
  fill_hole program in
    exact (HasProgramInO.of_encode (by rintro ⟨a, b⟩; cases a <;> cases b <;> rfl)
      (hasProgramIn_boolXor.toHasProgramInO.comp Bool.hasProgramIn_not.toHasProgramInO)).mono
        (Dominated.const 2)
      ((Dominated.refl _).max_same (Dominated.refl _))

/-- Testing a list for emptiness inspects its root. -/
theorem _root_.List.hasProgramIn_isEmpty {α : Type*} [UniqueEncoding Tree α] :
    HasProgramIn (List.isEmpty : List α → Bool) hole(⊢ program) IsO(fun _ => 1)
      IsO(fun xs => ⌜xs⌝ₜ.size) := by
  abstract_hole program using programIsEmpty
  fill_hole program in source_fun_prop

attribute [scoped program] Bool.hasProgramIn_not hasProgramIn_boolAnd hasProgramIn_boolOr
  hasProgramIn_boolXor hasProgramIn_boolBeq List.hasProgramIn_isEmpty

end Complexity.TreeProgram.Source
