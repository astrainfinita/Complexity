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

/-- A Boolean result has a constant-size code. -/
theorem dominated_size_encode_bool {α : Type*} [UniqueEncoding Tree α] (f : α → Bool) :
    Dominated (fun x => max ⌜x⌝ₜ.size ⌜f x⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) :=
  (Dominated.refl _).max_same ((Dominated.const_of_pos 3 fun _ => Tree.size_pos _).mono_left
    fun _ => size_encode_bool_le _)

theorem _root_.Bool.hasProgram_not :
    HasProgram Bool.not hole(⊢ program) (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programNot
  fill_hole program in
    exact .of_encode (by intro x; cases x <;> rfl)
      (by source_cases; exact dominated_size_encode_bool _ :
        HasProgram (fun x => match x with | false => true | true => false) _
          (fun _ => 1) (fun x => ⌜x⌝ₜ.size))

theorem hasProgram_boolAnd : HasProgram (fun x : Bool × Bool => x.1 && x.2) hole(⊢ program)
    (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programBoolAnd
  fill_hole program in
    exact .of_encode (by rintro ⟨a, b⟩; cases a <;> cases b <;> rfl)
      (by source_cases; exact dominated_size_encode_bool _ :
        HasProgram (fun x : Bool × Bool => match x.1 with | false => false | true => x.2) _
          (fun _ => 1) (fun x => ⌜x⌝ₜ.size))

theorem hasProgram_boolOr : HasProgram (fun x : Bool × Bool => x.1 || x.2) hole(⊢ program)
    (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programBoolOr
  fill_hole program in
    exact .of_encode (by rintro ⟨a, b⟩; cases a <;> cases b <;> rfl)
      (by source_cases; exact dominated_size_encode_bool _ :
        HasProgram (fun x : Bool × Bool => match x.1 with | false => x.2 | true => true) _
          (fun _ => 1) (fun x => ⌜x⌝ₜ.size))

theorem hasProgram_boolXor : HasProgram (fun x : Bool × Bool => xor x.1 x.2) hole(⊢ program)
    (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programBoolXor
  fill_hole program in
    exact .of_encode (by rintro ⟨a, b⟩; cases a <;> cases b <;> rfl)
      (by source_cases; exact dominated_size_encode_bool _ :
        HasProgram (fun x : Bool × Bool => match x.1 with | false => x.2 | true => !x.2) _
          (fun _ => 1) (fun x => ⌜x⌝ₜ.size))

theorem hasProgram_boolBeq : HasProgram (fun x : Bool × Bool => x.1 == x.2) hole(⊢ program)
    (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programBoolBeq
  fill_hole program in
    exact (HasProgram.of_encode (by rintro ⟨a, b⟩; cases a <;> cases b <;> rfl)
      (hasProgram_boolXor.comp Bool.hasProgram_not)).mono (Dominated.const 2)
      (dominated_size_encode_bool _)

/-- Testing a list for emptiness inspects its root. -/
theorem _root_.List.hasProgram_isEmpty {α : Type*} [UniqueEncoding Tree α] :
    HasProgram (List.isEmpty : List α → Bool) hole(⊢ program) (fun _ => 1)
      (fun xs => ⌜xs⌝ₜ.size) := by
  abstract_hole program using programIsEmpty
  fill_hole program in source_fun_prop
  all_goals dominated

attribute [scoped fun_prop] Bool.hasProgram_not hasProgram_boolAnd hasProgram_boolOr
  hasProgram_boolXor hasProgram_boolBeq List.hasProgram_isEmpty

end Complexity.TreeProgram.Source
