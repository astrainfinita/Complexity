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

def Implementation.boolNot : Implementation Bool.not (fun _ => 1) (fun x => ⌜x⌝ₜ.size) :=
  .ofEncode (by intro x; cases x <;> rfl)
    (by source_cases; exact dominated_size_encode_bool _ :
      Implementation (fun x => match x with | false => true | true => false)
        (fun _ => 1) (fun x => ⌜x⌝ₜ.size))

def Implementation.boolAnd :
    Implementation (fun x : Bool × Bool => x.1 && x.2) (fun _ => 1) (fun x => ⌜x⌝ₜ.size) :=
  .ofEncode (by rintro ⟨a, b⟩; cases a <;> cases b <;> rfl)
    (by source_cases; exact dominated_size_encode_bool _ :
      Implementation (fun x : Bool × Bool => match x.1 with | false => false | true => x.2)
        (fun _ => 1) (fun x => ⌜x⌝ₜ.size))

def Implementation.boolOr :
    Implementation (fun x : Bool × Bool => x.1 || x.2) (fun _ => 1) (fun x => ⌜x⌝ₜ.size) :=
  .ofEncode (by rintro ⟨a, b⟩; cases a <;> cases b <;> rfl)
    (by source_cases; exact dominated_size_encode_bool _ :
      Implementation (fun x : Bool × Bool => match x.1 with | false => x.2 | true => true)
        (fun _ => 1) (fun x => ⌜x⌝ₜ.size))

def Implementation.boolXor :
    Implementation (fun x : Bool × Bool => xor x.1 x.2) (fun _ => 1) (fun x => ⌜x⌝ₜ.size) :=
  .ofEncode (by rintro ⟨a, b⟩; cases a <;> cases b <;> rfl)
    (by source_cases; exact dominated_size_encode_bool _ :
      Implementation (fun x : Bool × Bool => match x.1 with | false => x.2 | true => !x.2)
        (fun _ => 1) (fun x => ⌜x⌝ₜ.size))

def Implementation.boolBeq :
    Implementation (fun x : Bool × Bool => x.1 == x.2) (fun _ => 1) (fun x => ⌜x⌝ₜ.size) :=
  (Implementation.ofEncode (by rintro ⟨a, b⟩; cases a <;> cases b <;> rfl)
    (Implementation.boolXor.comp Implementation.boolNot)).mono (Dominated.const 2)
    (dominated_size_encode_bool _)

/-- Testing a list for emptiness inspects its root. -/
def Implementation.listIsEmpty {α : Type*} [UniqueEncoding Tree α] :
    Implementation (List.isEmpty : List α → Bool) (fun _ => 1) (fun xs => ⌜xs⌝ₜ.size) := by
  source_fun_prop
  all_goals dominated

attribute [scoped fun_prop] Implementation.boolNot Implementation.boolAnd Implementation.boolOr
  Implementation.boolXor Implementation.boolBeq Implementation.listIsEmpty

end Complexity.TreeProgram.Source
