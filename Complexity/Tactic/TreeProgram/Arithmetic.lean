/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Tactic.TreeProgram.TailRecursion

/-! # Source specifications for binary natural-number operations -/

@[expose] public section

open Complexity TreeProgram
namespace Complexity.TreeProgram.Source

-- Binary operations reuse the source-loop compiler and the existing carry implementation.
theorem _root_.Nat.hasProgram_bits :
    HasProgram Nat.bits (fun v => pure v) (fun _ => 0) (fun _ => 0) :=
  .of_encode (g := id) (fun _ => rfl) HasProgram.identity

def borrowContinues (x : List Bool × List Bool) : Bool :=
  match x.1 with | false :: _ => true | _ => false

def borrowStep (x : List Bool × List Bool) : List Bool × List Bool :=
  match x.1 with | _ :: xs => (xs, true :: x.2) | [] => x

def borrowFinish (x : List Bool × List Bool) : List Bool :=
  x.2.reverse ++ match x.1 with
    | true :: xs => if xs.isEmpty then [] else false :: xs
    | _ => []

theorem hasProgram_borrowContinues :
    HasProgram borrowContinues hole(⊢ program) (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programBorrowContinues
  fill_hole program in source_fun_prop

theorem hasProgram_borrowStep :
    HasProgram borrowStep hole(⊢ program) (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programBorrowStep
  fill_hole program in source_fun_prop

def borrow (x : List Bool × List Bool) := x.2.reverse ++ BitList.decrement x.1

theorem hasProgram_borrowFinish :
    HasProgram borrowFinish hole(⊢ program) (fun x => ⌜x⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programBorrowFinish
  fill_hole program in source_fun_prop


attribute [scoped fun_prop] hasProgram_borrowContinues hasProgram_borrowStep
  hasProgram_borrowFinish

def borrowInvariant (x y : List Bool × List Bool) : Prop :=
  y.1.length + y.2.length ≤ x.1.length + x.2.length

theorem borrowInvariant_size : Dominated
    (fun z : {p : (List Bool × List Bool) × (List Bool × List Bool) //
      borrowInvariant p.1 p.2} => ⌜z.1.2⌝ₜ.size) (fun z => ⌜z.1.1⌝ₜ.size) := by
  dominated [borrowInvariant, size_encode_list_bool_le]

/-- The loop consumes callback growth specifications; no overall credit constant is supplied. -/
theorem hasProgram_borrow :
    HasProgram borrow hole(⊢ program) (fun x => ⌜x⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programBorrow
  fill_hole program in
    source_fun_prop using loop (test := borrowContinues) (next := borrowStep)
      (finish := borrowFinish) (invariant := borrowInvariant) (measure := fun x => x.1.length)
      (step := fun _ => 1) (stop := fun x => ⌜x⌝ₜ.size) (space := fun x => ⌜x⌝ₜ.size)
  case equation =>
    rintro ⟨xs, acc⟩
    cases xs with
    | nil => simp [borrow, borrowContinues, borrowFinish, BitList.decrement]
    | cons b bs => cases b <;> simp [borrow, borrowContinues, borrowStep, borrowFinish,
        BitList.decrement, List.reverse_cons, List.append_assoc]
  case initial => exact fun _ => le_rfl
  case next_state =>
    rintro ⟨xs, acc⟩ ⟨ys, buf⟩ hi ht
    cases ys <;> simp_all [borrowContinues, borrowStep, borrowInvariant]
    omega
  case decreases =>
    rintro x ⟨ys, buf⟩ _ ht
    cases ys <;> simp_all [borrowContinues, borrowStep]
  case input_size => exact borrowInvariant_size
  case check_peak => exact borrowInvariant_size
  case step_peak => exact borrowInvariant_size
  case stop_peak => exact borrowInvariant_size
  case stop_time => exact borrowInvariant_size
  case step_pos => exact fun _ => Nat.zero_lt_one
  case stop_pos => exact fun _ => Tree.size_pos _

theorem _root_.Complexity.BitList.hasProgram_decrement :
    HasProgram BitList.decrement hole(⊢ program) (fun xs => ⌜xs⌝ₜ.size) (fun xs => ⌜xs⌝ₜ.size) := by
  abstract_hole program using programDecrement
  have hb := hasProgram_borrow
  fill_hole program in source_fun_prop via (fun xs => borrow (xs, []))
  case source_eq => funext xs; simp [borrow]

theorem _root_.Nat.hasProgram_pred :
    HasProgram Nat.pred hole(⊢ program) (fun n => ⌜n⌝ₜ.size) (fun n => ⌜n⌝ₜ.size) := by
  abstract_hole program using programPred
  fill_hole program in
    exact (HasProgram.of_encode (by intro n; simp [Nat.pred_eq_sub_one, encode_nat_tree])
      (Nat.hasProgram_bits.comp BitList.hasProgram_decrement)).mono
      (Dominated.of_le fun n => by simp [size_encode_bits])
      (Dominated.of_le fun n => by simp [size_encode_bits])

attribute [scoped fun_prop] Nat.hasProgram_bits BitList.hasProgram_decrement
  Nat.hasProgram_pred

def addContinues (x : Bool × List Bool × List Bool × List Bool) : Bool :=
  !x.2.1.isEmpty && !x.2.2.1.isEmpty

def addStep (x : Bool × List Bool × List Bool × List Bool) :=
  match x with
  | (c, a :: xs, b :: ys, acc) =>
      ((a && b) || (c && (a || b)), xs, ys, (xor (xor a b) c) :: acc)
  | _ => x

def carryFinish (x : Bool × List Bool) :=
  if x.1 then BitList.increment x.2 else x.2

theorem hasProgram_carryFinish :
    HasProgram carryFinish hole(⊢ program) (fun x => ⌜x⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programCarryFinish
  fill_hole program in source_fun_prop


attribute [local fun_prop] hasProgram_carryFinish


def addFinish (x : Bool × List Bool × List Bool × List Bool) :=
  let rest := if x.2.1.isEmpty then x.2.2.1 else x.2.1
  x.2.2.2.reverse ++ carryFinish (x.1, rest)

def addResult (x : Bool × List Bool × List Bool × List Bool) :=
  x.2.2.2.reverse ++ BitList.addCarry x.1 x.2.1 x.2.2.1

theorem hasProgram_addContinues :
    HasProgram addContinues hole(⊢ program) (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programAddContinues
  have hb (f : Bool × List Bool × List Bool × List Bool → Bool) :
      Dominated (fun x => ⌜f x⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) :=
    (Dominated.const_of_pos 3 fun _ => Tree.size_pos _).mono_left fun x => size_encode_bool_le _
  fill_hole program in source_fun_prop


attribute [local fun_prop] hasProgram_addContinues


theorem hasProgram_addStep :
    HasProgram addStep hole(⊢ program) (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programAddStep
  fill_hole program in source_fun_prop


attribute [local fun_prop] hasProgram_addStep


theorem hasProgram_addFinish :
    HasProgram addFinish hole(⊢ program) (fun x => ⌜x⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programAddFinish
  have hcarryInput : Dominated
      (fun x : Bool × List Bool × List Bool × List Bool =>
        ⌜(x.1, if x.2.1.isEmpty then x.2.2.1 else x.2.1)⌝ₜ.size)
      (fun x => ⌜x⌝ₜ.size) := by
    apply Dominated.of_le
    rintro ⟨c, xs, ys, acc⟩
    simp only [size_encode_prod]
    split <;> omega
  have hcarry := (hasProgram_carryFinish.size_encode.comp
    (fun x : Bool × List Bool × List Bool × List Bool =>
      (x.1, if x.2.1.isEmpty then x.2.2.1 else x.2.1))).trans
      (hcarryInput.max_same hcarryInput)
  fill_hole program in source_fun_prop


attribute [local fun_prop] hasProgram_addFinish


def addCount (x : Bool × List Bool × List Bool × List Bool) : ℕ :=
  x.2.1.length + x.2.2.1.length + x.2.2.2.length

theorem addCount_size_growth : Dominated
    (fun z : {p : (Bool × List Bool × List Bool × List Bool) ×
      (Bool × List Bool × List Bool × List Bool) // addCount p.2 ≤ addCount p.1} => ⌜z.1.2⌝ₜ.size)
    (fun z => ⌜z.1.1⌝ₜ.size) := by
  dominated [addCount, size_encode_list_bool_le]

theorem hasProgram_addResult :
    HasProgram addResult hole(⊢ program) (fun x => ⌜x⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programAddResult
  fill_hole program in
    source_fun_prop using loop (test := addContinues) (next := addStep) (finish := addFinish)
      (invariant := fun x y => addCount y ≤ addCount x) (measure := fun x => x.2.1.length)
      (step := fun _ => 1) (stop := fun x => ⌜x⌝ₜ.size) (space := fun x => ⌜x⌝ₜ.size)
  case equation =>
    rintro ⟨c, xs, ys, acc⟩
    cases xs <;> cases ys <;> simp [addResult, addContinues, addStep, addFinish,
      carryFinish, BitList.addCarry, List.reverse_cons, List.append_assoc]
  case initial => exact fun _ => le_rfl
  case next_state =>
    rintro x ⟨c, xs, ys, acc⟩ hi ht
    cases xs <;> cases ys <;> simp_all [addContinues, addStep, addCount]
    omega
  case decreases =>
    rintro x ⟨c, xs, ys, acc⟩ _ ht
    cases xs <;> cases ys <;> simp_all [addContinues, addStep]
  case input_size => exact addCount_size_growth
  case check_peak => exact addCount_size_growth
  case step_peak => exact addCount_size_growth
  case stop_peak => exact addCount_size_growth
  case stop_time => exact addCount_size_growth
  case step_pos => exact fun _ => Nat.zero_lt_one
  case stop_pos => exact fun _ => Tree.size_pos _

theorem hasProgram_add :
    HasProgram (fun x : ℕ × ℕ => x.1 + x.2) hole(⊢ program)
      (fun x => ⌜x⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programAdd
  have hadd := hasProgram_addResult
  fill_hole program in
    exact HasProgram.of_encode (g := fun x : ℕ × ℕ => addResult (false, x.1.bits, x.2.bits, []))
      (by rintro ⟨m, n⟩; simp [addResult, BitList.addCarry_bits, encode_nat_tree])
      (by source_fun_prop)

def leContinues (x : Bool × List Bool × List Bool) :=
  !(x.2.1.isEmpty && x.2.2.isEmpty)

def leStep (x : Bool × List Bool × List Bool) :=
  match x with
  | (c, [], b :: ys) => (b || c, [], ys)
  | (c, a :: xs, []) => (!a && c, xs, [])
  | (c, a :: xs, b :: ys) => ((if a == b then c else b), xs, ys)
  | _ => x

def leResult (x : Bool × List Bool × List Bool) := BitList.leAux x.1 x.2.1 x.2.2

theorem hasProgram_leContinues :
    HasProgram leContinues hole(⊢ program) (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programLeContinues
  have hb (f : Bool × List Bool × List Bool → Bool) :
      Dominated (fun x => ⌜f x⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) :=
    (Dominated.const_of_pos 3 fun _ => Tree.size_pos _).mono_left fun x => size_encode_bool_le _
  fill_hole program in source_fun_prop


attribute [local fun_prop] hasProgram_leContinues


theorem hasProgram_leStep :
    HasProgram leStep hole(⊢ program) (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programLeStep
  fill_hole program in source_fun_prop


attribute [local fun_prop] hasProgram_leStep


def compareCount (x : Bool × List Bool × List Bool) : ℕ :=
  x.2.1.length + x.2.2.length

theorem compareCount_size_growth : Dominated
    (fun z : {p : (Bool × List Bool × List Bool) × (Bool × List Bool × List Bool) //
      compareCount p.2 ≤ compareCount p.1} => ⌜z.1.2⌝ₜ.size) (fun z => ⌜z.1.1⌝ₜ.size) := by
  dominated [compareCount, size_encode_list_bool_le]

theorem hasProgram_leResult :
    HasProgram leResult hole(⊢ program) (fun x => ⌜x⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programLeResult
  fill_hole program in
    source_fun_prop using loop (test := leContinues) (next := leStep) (finish := Prod.fst)
      (invariant := fun x y => compareCount y ≤ compareCount x) (measure := compareCount)
      (step := fun _ => 1) (stop := fun _ => 1) (space := fun x => ⌜x⌝ₜ.size)
  case equation =>
    rintro ⟨c, xs, ys⟩
    cases xs <;> cases ys <;> simp [leContinues, leStep, leResult, BitList.leAux]
  case initial => exact fun _ => le_rfl
  case next_state =>
    rintro x ⟨c, xs, ys⟩ hi ht
    cases xs <;> cases ys <;> simp_all [leContinues, leStep, compareCount]
    all_goals omega
  case decreases =>
    rintro x ⟨c, xs, ys⟩ _ ht
    cases xs <;> cases ys <;> simp_all [leContinues, leStep, compareCount]
    all_goals omega
  case input_size => exact compareCount_size_growth
  case check_peak => exact compareCount_size_growth
  case step_peak => exact compareCount_size_growth
  case stop_peak => exact compareCount_size_growth
  case step_pos => exact fun _ => Nat.zero_lt_one
  case stop_pos => exact fun _ => Nat.zero_lt_one
  case time => dominated [compareCount]

theorem hasProgram_ble :
    HasProgram (fun x : ℕ × ℕ => Nat.ble x.1 x.2) hole(⊢ program) (fun x => ⌜x⌝ₜ.size)
      (fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programBle
  have hle := hasProgram_leResult
  fill_hole program in
    refine HasProgram.of_encode (g := fun x : ℕ × ℕ => leResult (true, x.1.bits, x.2.bits)) ?_
      (by source_fun_prop)
  rintro ⟨m, n⟩
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp [leResult, BitList.leAux_eq]

theorem hasProgram_lt :
    HasProgram (fun x : ℕ × ℕ => decide (x.1 < x.2)) hole(⊢ program) (fun x => ⌜x⌝ₜ.size)
      (fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programLt
  have hle := hasProgram_leResult
  fill_hole program in
    refine HasProgram.of_encode (g := fun x : ℕ × ℕ => leResult (false, x.1.bits, x.2.bits)) ?_
      (by source_fun_prop)
  rintro ⟨m, n⟩
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp [leResult, BitList.leAux_eq]

attribute [scoped fun_prop] hasProgram_add hasProgram_ble hasProgram_lt

/-- Addition of one by the program of the addition; its growth is stated once here. -/
theorem hasProgram_addOne :
    HasProgram (fun n : ℕ => n + 1) hole(⊢ program) (fun n => ⌜n⌝ₜ.size)
      (fun n => ⌜n⌝ₜ.size) := by
  abstract_hole program using programAddOne
  fill_hole program in source_fun_prop

theorem _root_.Nat.hasProgram_succ :
    HasProgram Nat.succ programAddOne (fun n => ⌜n⌝ₜ.size) (fun n => ⌜n⌝ₜ.size) :=
  hasProgram_addOne

attribute [scoped fun_prop] hasProgram_addOne Nat.hasProgram_succ

theorem hasProgram_natBeq :
    HasProgram (fun x : ℕ × ℕ => Nat.beq x.1 x.2) hole(⊢ program) (fun x => ⌜x⌝ₜ.size)
      (fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programNatBeq
  fill_hole program in source_fun_prop via (fun x : ℕ × ℕ => Nat.ble x.1 x.2 && Nat.ble x.2 x.1)
  case source_eq =>
    funext ⟨m, n⟩
    apply Bool.eq_iff_iff.mpr
    simp [Nat.le_antisymm_iff]

attribute [scoped fun_prop] hasProgram_natBeq

end Complexity.TreeProgram.Source
