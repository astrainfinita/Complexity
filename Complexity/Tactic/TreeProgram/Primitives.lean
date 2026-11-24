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

Two further facts are not selected implementations. Testing a tree's root is built from the
emptiness test (`Tree.hasProgramIn_root`) but is not registered with `program`; this is the current
state, not a decision. Root tests at fixed paths of the input's code select one of several programs
(`exists_hasProgramInO_dispatch`), a rule rather than an implementation of a function.
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

/-- Testing a tree's root is testing the list of its spine for emptiness. -/
theorem _root_.Complexity.Tree.hasProgramIn_root :
    HasProgramIn Tree.root hole(⊢ program) IsO(fun _ => 1) IsO(fun t => ⌜t⌝ₜ.size) := by
  abstract_hole program using programRoot
  refine HasProgramInO.toHasProgramIn ?_
  fill_hole program in
    exact ((List.hasProgramIn_isEmpty (α := Tree)).toHasProgramInO.map_input Tree.spine
      Tree.encode_spine |>.comp Bool.hasProgramIn_not.toHasProgramInO |>.congr
      (funext fun t => (Tree.root_eq_not_isEmpty_spine t).symm)).mono
      (Dominated.const_of_pos 2 fun _ => Nat.one_pos)
      ((Dominated.of_le fun t => by rw [Tree.encode_spine]).max_same
        (Dominated.one fun t => Tree.size_pos _))

/-- Root tests at fixed paths of the input's code select one of the given programs. -/
theorem exists_hasProgramInO_dispatch {α β : Type*} [UniqueEncoding Tree α]
    [UniqueEncoding Tree β] (paths : List (List Bool)) (G : List Bool → α → β)
    (hG : ∀ l, ∃ q, HasProgramInO (G l) q (fun _ => 1) (fun x => ⌜x⌝ₜ.size)) :
    ∃ q, HasProgramInO (fun x => G (paths.map fun p => (⌜x⌝ₜ.subtree p).root) x) q
      (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  induction paths generalizing G with
  | nil => exact hG []
  | cons p ps ih =>
    obtain ⟨qt, ht⟩ := ih (fun l => G (true :: l)) (fun l => hG _)
    obtain ⟨qf, hf⟩ := ih (fun l => G (false :: l)) (fun l => hG _)
    have hc := (HasProgramInO.subtree (α := α) (f := fun x => ⌜x⌝ₜ.subtree p) p
      (fun _ => rfl)).comp Tree.hasProgramIn_root.toHasProgramInO
    refine ⟨_, ((hc.ite ht hf).congr ?_).mono ?_ ?_⟩
    · funext x
      simp only [Function.comp_apply, List.map_cons]
      by_cases h : (⌜x⌝ₜ.subtree p).root = true
      · rw [ite_eq_left h, h]
      · rw [ite_eq_right h, Bool.eq_false_of_ne_true h]
    · exact Dominated.of_le_mul 4 fun x => by split <;> simp
    · refine Dominated.of_le fun x => ?_
      have := Tree.size_subtree_le ⌜x⌝ₜ p
      simp only [Tree.encode_self, Function.comp_apply]
      split <;> omega

end Complexity.TreeProgram.Source
