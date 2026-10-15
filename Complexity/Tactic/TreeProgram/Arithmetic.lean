/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Tactic.TreeProgram.TailRecursion

/-! # Source specifications for Boolean and binary natural-number operations -/

@[expose] public section

open Complexity TreeProgram
namespace Complexity.TreeProgram.Source

-- Binary operations reuse the source-loop compiler and the existing carry implementation.
@[source_bounds↓] def Implementation.bits : Implementation Nat.bits :=
  .ofEncode (g := id) (fun _ => rfl) Implementation.identity

def borrowContinues (x : List Bool × List Bool) : Bool :=
  match x.1 with | false :: _ => true | _ => false

def borrowStep (x : List Bool × List Bool) : List Bool × List Bool :=
  match x.1 with | _ :: xs => (xs, true :: x.2) | [] => x

def borrowFinish (x : List Bool × List Bool) : List Bool :=
  x.2.reverse ++ match x.1 with
    | true :: xs => if xs.isEmpty then [] else false :: xs
    | _ => []

@[source_bounds↓] def borrowContinuesImplementation : Implementation borrowContinues := by
  source_cases

@[source_bounds↓] def borrowStepImplementation : Implementation borrowStep := by source_cases

@[source_bounds↓] def borrowFinishImplementation : Implementation borrowFinish := by source_fun_prop

def borrow (x : List Bool × List Bool) := x.2.reverse ++ BitList.decrement x.1

@[source_growth] theorem borrowContinues_growth : borrowContinuesImplementation.HasGrowth
    (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  · exact Dominated.const _
  · exact (Dominated.refl _).max_same
      ((Dominated.const_of_pos 3 fun _ => Tree.size_pos _).mono_left
        fun x => size_encode_bool_le (borrowContinues x))

@[source_growth] theorem borrowStep_growth : borrowStepImplementation.HasGrowth
    (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  · exact Dominated.const _
  · apply (Dominated.refl _).max_same
    apply ((Dominated.refl _).add_same
      (Dominated.const_of_pos 5 fun _ => Tree.size_pos _)).mono_left
    rintro ⟨xs, acc⟩
    cases xs <;> simp [borrowStep]
    omega

@[source_growth] theorem borrowFinish_growth : borrowFinishImplementation.HasGrowth
    (fun x => ⌜x⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  all_goals
    apply Dominated.of_cover
      (fun acc : List Bool => ([], acc))
      (fun z : Bool × List Bool × List Bool => (z.1 :: z.2.1, z.2.2))
      (by
        rintro ⟨xs, acc⟩
        cases xs with
        | nil => exact Or.inl ⟨acc, rfl⟩
        | cons b xs => exact Or.inr ⟨(b, xs, acc), rfl⟩)
    case' hv =>
      apply Dominated.of_cover
        (fun z : List Bool × List Bool => (false, z)) (fun z => (true, z))
        (by rintro ⟨b, z⟩; cases b <;> simp)
  all_goals
    simp only [Function.comp_def, iteBounds_time, iteBounds_peak, ite_self,
      size_encode_prod, encode_list_cons, encode_list_nil, size_encode_unit,
      encode_bool_false, encode_bool_true, List.length_reverse, size_encode_reverse,
      Dominated.add_iff, Dominated.max_iff, Dominated.const_mul_left_iff, Nat.ofNat_pos]
    repeat' apply And.intro
    all_goals first
      | exact Dominated.of_le (fun _ => by omega)
      | exact Dominated.const_of_pos _ (fun _ => by omega)
      | apply Dominated.of_le
        intro x
        first
        | have := length_le_codeSize x; omega
        | have := length_le_codeSize x.1; omega
        | have := length_le_codeSize x.2; omega
      | apply Dominated.of_le
        intro x
        first
        | have := size_encode_bool_le x.1.isEmpty; omega
        | split <;> (try simp only [encode_list_nil, encode_list_cons, size_encode_prod,
            encode_bool_false, size_encode_unit]) <;> omega


attribute [scoped fun_prop] borrowContinuesImplementation borrowStepImplementation
  borrowFinishImplementation

def borrowInvariant (x y : List Bool × List Bool) : Prop :=
  y.1.length + y.2.length ≤ x.1.length + x.2.length

theorem borrowInvariant_size : Dominated
    (fun z : {p : (List Bool × List Bool) × (List Bool × List Bool) //
      borrowInvariant p.1 p.2} => ⌜z.1.2⌝ₜ.size) (fun z => ⌜z.1.1⌝ₜ.size) := by
  apply Dominated.of_le_mul 4
  rintro ⟨⟨⟨xs, acc⟩, ⟨ys, buf⟩⟩, h⟩
  have h₁ : ⌜ys⌝ₜ.size ≤ 4 * ys.length + 1 := Tree.size_encodeBitList_le _
  have h₂ : ⌜buf⌝ₜ.size ≤ 4 * buf.length + 1 := Tree.size_encodeBitList_le _
  have hx₁ := length_le_codeSize xs
  have hx₂ := length_le_codeSize acc
  simp only [size_encode_prod] at *
  change ys.length + buf.length ≤ xs.length + acc.length at h
  omega

/-- The loop consumes callback growth specifications; no overall credit constant is supplied. -/
noncomputable def borrowImplementation : Implementation borrow := by
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
  case step_time => exact Dominated.refl _
  case check_time => exact Dominated.refl _
  case stop_time => exact borrowInvariant_size
  case step_pos => exact fun _ => Nat.zero_lt_one
  case stop_pos => exact fun _ => Tree.size_pos _

@[source_growth] theorem borrow_growth : borrowImplementation.HasGrowth
    (fun x => ⌜x⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  · simp only [Nat.mul_one, Dominated.add_iff]
    have h : Dominated (fun x : List Bool × List Bool => x.1.length)
        (fun x => ⌜x⌝ₜ.size) := Dominated.of_le fun x =>
      (length_le_codeSize x.1).trans (size_encode_fst_le x)
    exact ⟨⟨Dominated.const_of_pos _ (fun _ => Tree.size_pos _),
      ⟨h, Dominated.refl _⟩⟩, Dominated.const_of_pos _ (fun _ => Tree.size_pos _)⟩
  · exact Dominated.refl _

@[source_bounds↓] noncomputable def Implementation.decrement :
    Implementation BitList.decrement := by
  let hb := borrowImplementation
  let h : Implementation (fun xs => borrow (xs, [])) := by source_fun_prop
  exact Implementation.ofEncode (by intro xs; simp [borrow]) h

@[source_growth] theorem Implementation.hasGrowth_decrement : decrement.HasGrowth
    (fun xs => ⌜xs⌝ₜ.size) (fun xs => ⌜xs⌝ₜ.size) := by
  source_fun_prop
  all_goals
    simp only [size_encode_prod, encode_list_nil, size_encode_unit,
      Dominated.add_iff,
      Dominated.max_iff, Nat.zero_add]
    repeat' apply And.intro
    all_goals first
      | exact Dominated.refl _
      | exact Dominated.zero
      | exact Dominated.const_of_pos _ (fun _ => Tree.size_pos _)

@[source_bounds↓] noncomputable def Implementation.pred : Implementation Nat.pred :=
  .ofEncode (by intro n; simp [Nat.pred_eq_sub_one])
    (Implementation.bits.comp Implementation.decrement)

@[source_growth] theorem Implementation.hasGrowth_pred : pred.HasGrowth
    (fun n => ⌜n⌝ₜ.size) (fun n => ⌜n⌝ₜ.size) := by
  source_fun_prop
  all_goals simpa only [Function.comp_apply, encode_nat_tree, Nat.zero_add,
    max_eq_right (Nat.zero_le _)] using
    (Dominated.refl (fun n : ℕ => ⌜n⌝ₜ.size))

@[source_bounds↓] def Implementation.boolNot : Implementation Bool.not := by
  let h : Implementation (fun x => match x with | false => true | true => false) := by source_cases
  exact (Implementation.ofEncode (by intro x; cases x <;> rfl) h)

@[source_growth] theorem Implementation.hasGrowth_boolNot : boolNot.HasGrowth
    (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  · exact Dominated.const _
  · exact (Dominated.refl _).max_same
      ((Dominated.const_of_pos 3 fun _ => Tree.size_pos _).mono_left
        fun x => size_encode_bool_le _)

@[source_bounds↓] def Implementation.boolAnd :
    Implementation (fun x : Bool × Bool => x.1 && x.2) := by
  let h : Implementation (fun x : Bool × Bool => match x.1 with | false => false | true => x.2) :=
    by source_cases
  exact (Implementation.ofEncode (by rintro ⟨a, b⟩; cases a <;> cases b <;> rfl) h)

@[source_growth] theorem Implementation.hasGrowth_boolAnd : boolAnd.HasGrowth
    (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  · exact Dominated.const _
  · exact (Dominated.refl _).max_same
      ((Dominated.const_of_pos 3 fun _ => Tree.size_pos _).mono_left
        fun x => size_encode_bool_le _)

@[source_bounds↓] def Implementation.boolOr :
    Implementation (fun x : Bool × Bool => x.1 || x.2) := by
  let h : Implementation (fun x : Bool × Bool => match x.1 with | false => x.2 | true => true) :=
    by source_cases
  exact (Implementation.ofEncode (by rintro ⟨a, b⟩; cases a <;> cases b <;> rfl) h)

@[source_growth] theorem Implementation.hasGrowth_boolOr : boolOr.HasGrowth
    (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  · exact Dominated.const _
  · exact (Dominated.refl _).max_same
      ((Dominated.const_of_pos 3 fun _ => Tree.size_pos _).mono_left
        fun x => size_encode_bool_le _)

@[source_bounds↓] def Implementation.boolXor :
    Implementation (fun x : Bool × Bool => xor x.1 x.2) := by
  let h : Implementation (fun x : Bool × Bool => match x.1 with | false => x.2 | true => !x.2) :=
    by source_cases
  exact (Implementation.ofEncode (by rintro ⟨a, b⟩; cases a <;> cases b <;> rfl) h)

@[source_growth] theorem Implementation.hasGrowth_boolXor : boolXor.HasGrowth
    (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  · exact Dominated.const _
  · exact (Dominated.refl _).max_same
      ((Dominated.const_of_pos 3 fun _ => Tree.size_pos _).mono_left
        fun x => size_encode_bool_le _)

@[source_bounds↓] def Implementation.boolBeq :
    Implementation (fun x : Bool × Bool => x.1 == x.2) :=
  Implementation.ofEncode (by rintro ⟨a, b⟩; cases a <;> cases b <;> rfl)
    (Implementation.boolXor.comp Implementation.boolNot)

attribute [scoped fun_prop] Implementation.bits Implementation.decrement Implementation.pred
  Implementation.boolNot Implementation.boolAnd Implementation.boolOr Implementation.boolXor
  Implementation.boolBeq

def addContinues (x : Bool × List Bool × List Bool × List Bool) : Bool :=
  !x.2.1.isEmpty && !x.2.2.1.isEmpty

def addStep (x : Bool × List Bool × List Bool × List Bool) :=
  match x with
  | (c, a :: xs, b :: ys, acc) =>
      ((a && b) || (c && (a || b)), xs, ys, (xor (xor a b) c) :: acc)
  | _ => x

def carryFinish (x : Bool × List Bool) :=
  if x.1 then BitList.increment x.2 else x.2

@[source_bounds↓] def carryFinishImplementation : Implementation carryFinish := by source_fun_prop

@[source_growth] theorem carryFinish_growth : carryFinishImplementation.HasGrowth
    (fun x => ⌜x⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  all_goals
    apply Dominated.of_cover (fun xs : List Bool => (false, xs)) (fun xs => (true, xs))
      (by rintro ⟨c, xs⟩; cases c <;> simp)
    all_goals
      simp only [Function.comp_def, Bool.false_eq_true, ↓reduceIte, size_encode_prod,
        encode_bool_false, encode_bool_true, size_encode_unit, Dominated.add_iff,
        Dominated.max_iff]
      repeat' apply And.intro
      all_goals exact Dominated.of_le (fun _ => by omega)


attribute [local fun_prop] carryFinishImplementation


def addFinish (x : Bool × List Bool × List Bool × List Bool) :=
  let rest := if x.2.1.isEmpty then x.2.2.1 else x.2.1
  x.2.2.2.reverse ++ carryFinish (x.1, rest)

def addResult (x : Bool × List Bool × List Bool × List Bool) :=
  x.2.2.2.reverse ++ BitList.addCarry x.1 x.2.1 x.2.2.1

@[source_bounds↓] def addContinuesImplementation : Implementation addContinues := by source_fun_prop

@[source_growth] theorem addContinues_growth : addContinuesImplementation.HasGrowth
    (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  have hb (f : Bool × List Bool × List Bool × List Bool → Bool) :
      Dominated (fun x => ⌜f x⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) :=
    (Dominated.const_of_pos 3 fun _ => Tree.size_pos _).mono_left fun x => size_encode_bool_le _
  source_fun_prop
  · exact Dominated.const _
  · simp only [size_encode_prod, Dominated.max_iff, Dominated.add_iff]
    repeat' apply And.intro
    all_goals first
    | exact Dominated.refl _
    | exact hb _
    | exact Dominated.const_of_pos _ (fun _ => Tree.size_pos _)


attribute [local fun_prop] addContinuesImplementation


@[source_bounds↓] def addStepImplementation : Implementation addStep := by source_calls

@[source_growth] theorem addStep_growth : addStepImplementation.HasGrowth
    (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  all_goals
    apply Dominated.of_cover
      (fun z : Bool × List Bool × List Bool => (z.1, [], z.2.1, z.2.2))
      (fun z : Bool × Bool × List Bool × List Bool × List Bool =>
        (z.1, z.2.1 :: z.2.2.1, z.2.2.2.1, z.2.2.2.2))
      (by
        rintro ⟨c, xs, ys, acc⟩
        cases xs with
        | nil => exact Or.inl ⟨(c, ys, acc), rfl⟩
        | cons a xs => exact Or.inr ⟨(c, a, xs, ys, acc), rfl⟩)
    case' hv =>
      apply Dominated.of_cover
        (fun z : Bool × Bool × List Bool × List Bool => (z.1, z.2.1, z.2.2.1, [], z.2.2.2))
        (fun z : Bool × Bool × List Bool × Bool × List Bool × List Bool =>
          (z.1, z.2.1, z.2.2.1, z.2.2.2.1 :: z.2.2.2.2.1, z.2.2.2.2.2))
        (by
          rintro ⟨c, a, xs, ys, acc⟩
          cases ys with
          | nil => exact Or.inl ⟨(c, a, xs, acc), rfl⟩
          | cons b ys => exact Or.inr ⟨(c, a, xs, b, ys, acc), rfl⟩)
  all_goals
    simp only [Function.comp_def, source_bounds, addStep, size_encode_prod, encode_list_cons,
      encode_list_nil, size_encode_unit, Dominated.add_iff, Dominated.max_iff]
    repeat' apply And.intro
    all_goals first
      | exact Dominated.const _
      | exact Dominated.of_le (fun _ => by omega)
      | exact Dominated.const_of_pos _ (fun _ => by omega)
      | apply (Dominated.const_of_pos 3 (fun _ => by omega)).mono_left
        intro x
        exact size_encode_bool_le _


attribute [local fun_prop] addStepImplementation


@[source_bounds↓] def addFinishImplementation : Implementation addFinish := by source_fun_prop

@[source_growth] theorem addFinish_growth : addFinishImplementation.HasGrowth
    (fun x => ⌜x⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) := by
  have hcarryInput : Dominated
      (fun x : Bool × List Bool × List Bool × List Bool =>
        ⌜(x.1, if x.2.1.isEmpty then x.2.2.1 else x.2.1)⌝ₜ.size)
      (fun x => ⌜x⌝ₜ.size) := by
    apply Dominated.of_le
    rintro ⟨c, xs, ys, acc⟩
    simp only [size_encode_prod]
    split <;> omega
  have hcarry := (carryFinish_growth.size_encode.comp
    (fun x : Bool × List Bool × List Bool × List Bool =>
      (x.1, if x.2.1.isEmpty then x.2.2.1 else x.2.1))).trans
      (hcarryInput.max_same hcarryInput)
  source_fun_prop
  all_goals
    simp only [Function.comp_apply, List.length_reverse, size_encode_prod,
      Dominated.add_iff, Dominated.max_iff, Dominated.const_mul_left_iff, Nat.ofNat_pos]
    repeat' apply And.intro
    all_goals first
    | exact hcarry
    | exact Dominated.const_of_pos _ (fun _ => Tree.size_pos _)
    | apply Dominated.of_le
      rintro ⟨c, xs, ys, acc⟩
      have ha := length_le_codeSize acc
      have hb := size_encode_bool_le xs.isEmpty
      simp only [size_encode_prod, size_encode_reverse]
      first | omega | split <;> omega


attribute [local fun_prop] addFinishImplementation


def addCount (x : Bool × List Bool × List Bool × List Bool) : ℕ :=
  x.2.1.length + x.2.2.1.length + x.2.2.2.length

theorem addCount_size (x y : Bool × List Bool × List Bool × List Bool)
    (h : addCount y ≤ addCount x) : ⌜y⌝ₜ.size ≤ 4 * ⌜x⌝ₜ.size + 10 := by
  rcases x with ⟨c, xs, ys, acc⟩
  rcases y with ⟨d, us, vs, buf⟩
  have h₁ : ⌜us⌝ₜ.size ≤ 4 * us.length + 1 := Tree.size_encodeBitList_le _
  have h₂ : ⌜vs⌝ₜ.size ≤ 4 * vs.length + 1 := Tree.size_encodeBitList_le _
  have h₃ : ⌜buf⌝ₜ.size ≤ 4 * buf.length + 1 := Tree.size_encodeBitList_le _
  have hx := length_le_codeSize xs
  have hy := length_le_codeSize ys
  have ha := length_le_codeSize acc
  have hd := size_encode_bool_le d
  simp only [addCount, size_encode_prod] at *
  omega

theorem addCount_size_growth : Dominated
    (fun z : {p : (Bool × List Bool × List Bool × List Bool) ×
      (Bool × List Bool × List Bool × List Bool) // addCount p.2 ≤ addCount p.1} => ⌜z.1.2⌝ₜ.size)
    (fun z => ⌜z.1.1⌝ₜ.size) :=
  (((Dominated.refl _).const_mul_left 4).add_same
    (Dominated.const_of_pos 10 fun _ => Tree.size_pos _)).mono_left
      fun z => addCount_size _ _ z.2

noncomputable def addResultImplementation : Implementation addResult := by
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
  case step_time => exact Dominated.refl _
  case check_time => exact Dominated.refl _
  case stop_time => exact addCount_size_growth
  case step_pos => exact fun _ => Nat.zero_lt_one
  case stop_pos => exact fun _ => Tree.size_pos _

@[source_growth] theorem addResult_growth : addResultImplementation.HasGrowth
    (fun x => ⌜x⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  · simp only [Nat.mul_one, Dominated.add_iff]
    have h : Dominated (fun x : Bool × List Bool × List Bool × List Bool => x.2.1.length)
        (fun x => ⌜x⌝ₜ.size) := Dominated.of_le fun x =>
      (length_le_codeSize x.2.1).trans ((size_encode_fst_le x.2).trans (size_encode_snd_le x))
    exact ⟨⟨Dominated.const_of_pos _ (fun _ => Tree.size_pos _),
      ⟨h, Dominated.refl _⟩⟩, Dominated.const_of_pos _ (fun _ => Tree.size_pos _)⟩
  · exact Dominated.refl _

@[source_bounds↓] noncomputable def Implementation.add :
    Implementation (fun x : ℕ × ℕ => x.1 + x.2) := by
  let hadd := addResultImplementation
  apply Implementation.ofEncode (g :=
    fun x : ℕ × ℕ => addResult (false, x.1.bits, x.2.bits, []))
  · rintro ⟨m, n⟩; simp [addResult, BitList.addCarry_bits]
  · source_fun_prop

@[source_growth] theorem Implementation.hasGrowth_add : add.HasGrowth
    (fun x => ⌜x⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  all_goals
    simp only [size_encode_prod, encode_list_nil, encode_bool_false,
      size_encode_unit, Nat.add_zero,
      Dominated.add_iff, Dominated.max_iff]
    repeat' apply And.intro
    all_goals first
      | exact Dominated.zero
      | exact Dominated.const_of_pos _ (fun _ => Tree.size_pos _)
      | exact Dominated.of_le (fun x => by
          try simp only [← encode_nat_tree]
          first | exact size_encode_fst_le x | exact size_encode_snd_le x | exact le_rfl)

def leContinues (x : Bool × List Bool × List Bool) :=
  !(x.2.1.isEmpty && x.2.2.isEmpty)

def leStep (x : Bool × List Bool × List Bool) :=
  match x with
  | (c, [], b :: ys) => (b || c, [], ys)
  | (c, a :: xs, []) => (!a && c, xs, [])
  | (c, a :: xs, b :: ys) => ((if a == b then c else b), xs, ys)
  | _ => x

def leResult (x : Bool × List Bool × List Bool) := BitList.leAux x.1 x.2.1 x.2.2

@[source_bounds↓] def leContinuesImplementation : Implementation leContinues := by source_fun_prop

@[source_growth] theorem leContinues_growth : leContinuesImplementation.HasGrowth
    (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  have hb (f : Bool × List Bool × List Bool → Bool) :
      Dominated (fun x => ⌜f x⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) :=
    (Dominated.const_of_pos 3 fun _ => Tree.size_pos _).mono_left fun x => size_encode_bool_le _
  source_fun_prop
  · exact Dominated.const _
  · simp only [size_encode_prod, Dominated.max_iff, Dominated.add_iff]
    repeat' apply And.intro
    all_goals first
    | exact Dominated.refl _
    | exact hb _
    | exact Dominated.const_of_pos _ (fun _ => Tree.size_pos _)


attribute [local fun_prop] leContinuesImplementation


@[source_bounds↓] def leStepImplementation : Implementation leStep := by source_calls

@[source_growth] theorem leStep_growth : leStepImplementation.HasGrowth
    (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  all_goals
    apply Dominated.of_cover
      (fun z : Bool × List Bool => (z.1, [], z.2))
      (fun z : Bool × Bool × List Bool × List Bool => (z.1, z.2.1 :: z.2.2.1, z.2.2.2))
      (by
        rintro ⟨c, xs, ys⟩
        cases xs with
        | nil => exact Or.inl ⟨(c, ys), rfl⟩
        | cons a xs => exact Or.inr ⟨(c, a, xs, ys), rfl⟩)
    all_goals first
    | apply Dominated.of_cover
        (fun c : Bool => (c, [])) (fun z : Bool × Bool × List Bool => (z.1, z.2.1 :: z.2.2))
        (by
          rintro ⟨c, ys⟩
          cases ys with
          | nil => exact Or.inl ⟨c, rfl⟩
          | cons b ys => exact Or.inr ⟨(c, b, ys), rfl⟩)
    | apply Dominated.of_cover
        (fun z : Bool × Bool × List Bool => (z.1, z.2.1, z.2.2, []))
        (fun z : Bool × Bool × List Bool × Bool × List Bool =>
          (z.1, z.2.1, z.2.2.1, z.2.2.2.1 :: z.2.2.2.2))
        (by
          rintro ⟨c, a, xs, ys⟩
          cases ys with
          | nil => exact Or.inl ⟨(c, a, xs), rfl⟩
          | cons b ys => exact Or.inr ⟨(c, a, xs, b, ys), rfl⟩)
  all_goals
    simp only [Function.comp_def, source_bounds, leStep, iteBounds,
      size_encode_prod, encode_list_cons, encode_list_nil, size_encode_unit,
      Dominated.add_iff, Dominated.max_iff]
    repeat' apply And.intro
    all_goals first
      | exact Dominated.const _
      | exact Dominated.of_le (fun _ => by omega)
      | exact Dominated.const_of_pos _ (fun _ => by omega)
      | apply (Dominated.const_of_pos 3 (fun _ => by omega)).mono_left
        intro x
        exact size_encode_bool_le _
      | convert (Dominated.const _).ite (Dominated.const _)
          (fun x : Bool × Bool × List Bool × Bool × List Bool =>
            (x.2.1 == x.2.2.2.1) = true) using 1 <;> simp only [ite_self]
      | apply Dominated.of_le
        intro x
        split <;> omega


attribute [local fun_prop] leStepImplementation


def compareCount (x : Bool × List Bool × List Bool) : ℕ :=
  x.2.1.length + x.2.2.length

theorem compareCount_size (x y : Bool × List Bool × List Bool)
    (h : compareCount y ≤ compareCount x) : ⌜y⌝ₜ.size ≤ 4 * ⌜x⌝ₜ.size + 10 := by
  rcases x with ⟨c, xs, ys⟩
  rcases y with ⟨d, us, vs⟩
  have h₁ : ⌜us⌝ₜ.size ≤ 4 * us.length + 1 := Tree.size_encodeBitList_le _
  have h₂ : ⌜vs⌝ₜ.size ≤ 4 * vs.length + 1 := Tree.size_encodeBitList_le _
  have hx := length_le_codeSize xs
  have hy := length_le_codeSize ys
  have hd := size_encode_bool_le d
  simp only [compareCount, size_encode_prod] at *
  omega

theorem compareCount_size_growth : Dominated
    (fun z : {p : (Bool × List Bool × List Bool) × (Bool × List Bool × List Bool) //
      compareCount p.2 ≤ compareCount p.1} => ⌜z.1.2⌝ₜ.size) (fun z => ⌜z.1.1⌝ₜ.size) :=
  (((Dominated.refl _).const_mul_left 4).add_same
    (Dominated.const_of_pos 10 fun _ => Tree.size_pos _)).mono_left
      fun z => compareCount_size _ _ z.2

noncomputable def leResultImplementation : Implementation leResult := by
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
  case step_time => exact Dominated.refl _
  case check_time => exact Dominated.refl _
  case stop_time => exact Dominated.refl _
  all_goals exact fun _ => Nat.zero_lt_one

@[source_growth] theorem leResult_growth : leResultImplementation.HasGrowth
    (fun x => ⌜x⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  · simp only [Nat.mul_one, Dominated.add_iff]
    have h : Dominated compareCount (fun x => ⌜x⌝ₜ.size) := Dominated.of_le fun x => by
      rcases x with ⟨c, xs, ys⟩
      have := length_le_codeSize xs
      have := length_le_codeSize ys
      dsimp only [compareCount]
      simp only [size_encode_prod]
      omega
    exact ⟨⟨Dominated.const_of_pos _ (fun _ => Tree.size_pos _),
      ⟨h, Dominated.const_of_pos _ (fun _ => Tree.size_pos _)⟩⟩,
      Dominated.const_of_pos _ (fun _ => Tree.size_pos _)⟩
  · exact Dominated.refl _

noncomputable def compareImplementation (c : Bool) :
    Implementation (fun x : ℕ × ℕ => leResult (c, x.1.bits, x.2.bits)) := by
  let hle := leResultImplementation
  cases c <;> source_fun_prop

@[source_growth] theorem compare_growth (c : Bool) : (compareImplementation c).HasGrowth
    (fun x => ⌜x⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) := by
  cases c <;> source_fun_prop
  all_goals
    simp only [Function.comp_apply, size_encode_prod, encode_bool_false, encode_bool_true,
      size_encode_unit, Nat.add_zero,
      Dominated.add_iff, Dominated.max_iff]
    repeat' apply And.intro
    all_goals first
      | exact Dominated.zero
      | exact Dominated.const_of_pos _ (fun _ => Tree.size_pos _)
      | exact Dominated.of_le (fun x => by
          try simp only [← encode_nat_tree]
          first | exact size_encode_fst_le x | exact size_encode_snd_le x | exact le_rfl)

@[source_bounds↓] noncomputable def Implementation.ble :
    Implementation (fun x : ℕ × ℕ => Nat.ble x.1 x.2) := by
  apply Implementation.ofEncode (hg := compareImplementation true)
  rintro ⟨m, n⟩
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp [leResult, BitList.leAux_eq]

@[source_bounds↓] noncomputable def Implementation.lt :
    Implementation (fun x : ℕ × ℕ => decide (x.1 < x.2)) := by
  apply Implementation.ofEncode (hg := compareImplementation false)
  rintro ⟨m, n⟩
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp [leResult, BitList.leAux_eq]

@[source_growth] theorem Implementation.hasGrowth_ble : ble.HasGrowth
    (fun x => ⌜x⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop <;> exact Dominated.refl _

@[source_growth] theorem Implementation.hasGrowth_lt : lt.HasGrowth
    (fun x => ⌜x⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop <;> exact Dominated.refl _

attribute [scoped fun_prop] Implementation.add Implementation.ble Implementation.lt

@[source_bounds↓] noncomputable def Implementation.natBeq :
    Implementation (fun x : ℕ × ℕ => Nat.beq x.1 x.2) := by
  apply Implementation.ofEncode (g := fun x : ℕ × ℕ => Nat.ble x.1 x.2 && Nat.ble x.2 x.1)
  · rintro ⟨m, n⟩
    congr 1
    apply Bool.eq_iff_iff.mpr
    simp [Nat.le_antisymm_iff]
  · source_fun_prop

attribute [scoped fun_prop] Implementation.natBeq

end Complexity.TreeProgram.Source
