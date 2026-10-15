/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Tactic.TreeProgram.Iteration
public import Complexity.Tactic.TreeProgram.TailRecursion

/-! # Source specifications for binary arithmetic and finite tables -/

@[expose] public section

open Complexity TreeProgram

namespace Complexity.TreeProgram.Source

def lookupContinues {α : Type*} (x : ℕ × List α) : Bool :=
  match x.2 with | [] => false | _ :: _ => !x.1.bits.isEmpty

def lookupStep {α : Type*} (x : ℕ × List α) := (x.1.pred, x.2.tail)

@[source_bounds↓] noncomputable def lookupCheckImplementation {α : Type*}
    [UniqueEncoding Tree α] : Implementation (lookupContinues (α := α)) := by source_fun_prop

@[source_growth] theorem lookupCheck_growth {α : Type*} [UniqueEncoding Tree α] :
    (lookupCheckImplementation (α := α)).HasGrowth (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  all_goals
    apply Dominated.of_cover (fun n : ℕ => (n, []))
      (fun x : ℕ × α × List α => (x.1, x.2.1 :: x.2.2))
      (by
        rintro ⟨n, xs⟩
        cases xs with
        | nil => exact Or.inl ⟨n, rfl⟩
        | cons a xs => exact Or.inr ⟨(n, a, xs), rfl⟩)
    all_goals
      simp only [Function.comp_def, size_encode_prod, encode_list_nil, encode_list_cons,
        encode_bool_false, size_encode_unit, ← encode_nat_tree, Dominated.add_iff,
        Dominated.max_iff]
      repeat' apply And.intro
      all_goals first
      | exact Dominated.const _
      | exact Dominated.of_le (fun _ => by omega)
      | exact Dominated.const_of_pos _ (fun _ => by omega)
      | exact Implementation.hasGrowth_boolNot.1.comp _
      | apply (Implementation.hasGrowth_boolNot.2.comp _).trans
        exact (Dominated.const_of_pos 3 (fun _ => by omega)).mono_left
          fun _ => size_encode_bool_le _
      | apply (Dominated.const_of_pos 3 (fun _ => by omega)).mono_left
        intro x
        exact size_encode_bool_le _

@[source_bounds↓] noncomputable def lookupStepImplementation {α : Type*}
    [UniqueEncoding Tree α] : Implementation (lookupStep (α := α)) := by source_fun_prop

@[source_growth] theorem lookupStep_growth {α : Type*} [UniqueEncoding Tree α] :
    (lookupStepImplementation (α := α)).HasGrowth
      (fun x => ⌜x.1⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  · simp only [Dominated.add_iff]
    repeat' apply And.intro
    all_goals first
      | exact Dominated.refl _
      | exact Dominated.const_of_pos _ (fun x => Tree.size_pos ⌜x.1⌝ₜ)
  · have hp := Implementation.hasGrowth_pred.size_encode
    have hpred := hp.comp (fun x : ℕ × List α => x.1)
    have hinput : Dominated (fun x : ℕ × List α => ⌜x.1⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) :=
      Dominated.of_le size_encode_fst_le
    have htail : Dominated (fun x : ℕ × List α => ⌜x.2.tail⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) :=
      Dominated.of_le fun x => (show ⌜x.2.tail⌝ₜ.size ≤ ⌜x.2⌝ₜ.size by
        cases x.2 <;> simp).trans (size_encode_snd_le x)
    simp only [size_encode_prod, Dominated.max_iff, Dominated.add_iff]
    repeat' apply And.intro
    all_goals first
      | exact Dominated.refl _
      | exact hinput
      | exact htail
      | exact hpred.trans (hinput.max_same hinput)
      | exact Dominated.const_of_pos _ (fun _ => Tree.size_pos _)

@[source_bounds↓] noncomputable def lookupFinishImplementation {α : Type*}
    [UniqueEncoding Tree α] : Implementation (fun x : ℕ × List α => x.2.head?) := by source_fun_prop

@[source_growth] theorem lookupFinish_growth {α : Type*} [UniqueEncoding Tree α] :
    (lookupFinishImplementation (α := α)).HasGrowth (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  · exact Dominated.const _
  · apply Dominated.of_le
    rintro ⟨n, xs⟩
    cases xs <;> simp only [size_encode_prod, encode_list_nil, encode_list_cons,
      encode_option_none, encode_option_some, size_encode_unit] <;> omega

def lookupInvariant {α : Type*} [UniqueEncoding Tree α] (x y : ℕ × List α) :=
  y.1.bits.length ≤ x.1.bits.length ∧ ⌜y.2⌝ₜ.size ≤ ⌜x.2⌝ₜ.size ∧ y.2[y.1]? = x.2[x.1]?

theorem lookup_size {α : Type*} [UniqueEncoding Tree α] :
    Dominated (fun z : {p : (ℕ × List α) × (ℕ × List α) // lookupInvariant p.1 p.2} =>
      ⌜z.1.2⌝ₜ.size) (fun z => ⌜z.1.1⌝ₜ.size) := by
  apply ((Dominated.refl _).const_mul_left 4).add_same
    (Dominated.const_of_pos 2 fun _ => Tree.size_pos _) |>.mono_left
  intro z
  rcases z with ⟨⟨⟨n, xs⟩, ⟨m, ys⟩⟩, hi⟩
  have hm : ⌜m⌝ₜ.size ≤ 4 * m.bits.length + 1 := Tree.size_encodeBitList_le m.bits
  have hb := hi.1
  have hl := hi.2.1
  have hn := length_le_codeSize n.bits
  simp only [size_encode_prod, encode_nat_tree] at *
  omega

/-- Indexed lookup uses selected callbacks and one invariant-family growth specification. -/
@[source_bounds↓] noncomputable def Implementation.lookup {α : Type*}
    [UniqueEncoding Tree α] : Implementation (fun x : ℕ × List α => x.2[x.1]?) := by
  refine Implementation.tailLoop lookupCheckImplementation lookupStepImplementation
    lookupFinishImplementation ⟨fun _ => 1, fun x => ⌜x⌝ₜ.size⟩
    ⟨fun x => ⌜x.1⌝ₜ.size, fun x => ⌜x⌝ₜ.size⟩ ⟨fun _ => 1, fun x => ⌜x⌝ₜ.size⟩
    lookupCheck_growth lookupStep_growth lookupFinish_growth lookupInvariant
    (fun x => x.2.length) (fun x => ⌜x⌝ₜ.size) (fun _ => 1) (fun x => ⌜x⌝ₜ.size)
    ?equation ?initial ?next_state ?decreases ?input_size ?check_peak ?step_peak ?stop_peak
    ?step_time ?check_time ?stop_time ?step_pos ?stop_pos
  case equation =>
    rintro ⟨n, xs⟩
    cases xs with
    | nil => simp [lookupContinues]
    | cons a xs =>
      by_cases hn : n = 0
      · simp [lookupContinues, hn]
      · have hbits : n.bits ≠ [] := by
          intro h; have := BitList.toNat_bits n; simp [h, BitList.toNat] at this; omega
        simp [lookupContinues, lookupStep, List.getElem?_cons, hn, hbits, Nat.pred_eq_sub_one]
  case initial => exact fun _ => ⟨le_rfl, le_rfl, rfl⟩
  case next_state =>
    rintro x ⟨m, ys⟩ hi ht
    cases ys with
    | nil => simp [lookupContinues] at ht
    | cons a ys =>
      have hm : m ≠ 0 := by intro hm; subst m; simp [lookupContinues] at ht
      have hp : m.pred.bits.length ≤ m.bits.length := by
        simpa [Nat.pred_eq_sub_one] using BitList.length_decrement_le m.bits
      refine ⟨hp.trans hi.1, ?_, ?_⟩
      · exact (show ⌜ys⌝ₜ.size ≤ ⌜a :: ys⌝ₜ.size by simp).trans hi.2.1
      · simpa [lookupStep, List.getElem?_cons, hm, Nat.pred_eq_sub_one] using hi.2.2
  case decreases =>
    rintro x ⟨m, ys⟩ hi ht
    cases ys <;> simp_all [lookupContinues, lookupStep]
  case input_size => exact lookup_size
  case check_peak => exact lookup_size
  case step_peak => exact lookup_size
  case stop_peak => exact lookup_size
  case step_time => exact lookup_size.mono_left fun z => size_encode_fst_le z.1.2
  case check_time => exact Dominated.one fun _ => Tree.size_pos _
  case stop_time => exact Dominated.refl _
  case step_pos => exact fun _ => Tree.size_pos _
  case stop_pos => exact fun _ => Nat.zero_lt_one

@[source_growth] theorem Implementation.hasGrowth_lookup {α : Type*} [UniqueEncoding Tree α] :
    (Implementation.lookup (α := α)).HasGrowth
      (fun x => ⌜x⌝ₜ.size ^ 2) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  · have hlen : Dominated (fun x : ℕ × List α => x.2.length) (fun x => ⌜x⌝ₜ.size) :=
      Dominated.of_le fun x => (length_le_codeSize x.2).trans (size_encode_snd_le x)
    have hmul := hlen.mul (Dominated.refl (fun x : ℕ × List α => ⌜x⌝ₜ.size))
    simp only [Dominated.add_iff]
    repeat' apply And.intro
    all_goals first
      | exact hmul.mono fun _ => by rw [pow_two]
      | exact Dominated.const_of_pos _ (fun _ => Nat.pow_pos (Tree.size_pos _))
  · exact Dominated.refl _

@[source_bounds↓] noncomputable def Implementation.getElem? {α β : Type*}
    [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {f : α → List β} {i : α → ℕ} (hf : Implementation f) (hi : Implementation i) :
    Implementation (fun x => (f x)[i x]?) := (hi.pair hf).comp Implementation.lookup

attribute [scoped fun_prop] Implementation.getElem?

@[source_bounds↓] def Implementation.encodeTree {α : Type*} [UniqueEncoding Tree α] :
    Implementation (encode Tree : α → Tree) :=
  .ofEncode (g := id) (fun _ => rfl) Implementation.identity

attribute [scoped fun_prop] Implementation.encodeTree

/-- Reading a represented table reuses its code; construction remains a separate premise. -/
@[source_bounds↓] def Implementation.ofFn {α β : Type*}
    [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {n : α → ℕ} {f : (x : α) → Fin (n x) → β}
    (hf : Implementation (fun x => ⌜f x⌝ₜ)) : Implementation (fun x => List.ofFn (f x)) :=
  .ofEncode (g := fun x => ⌜f x⌝ₜ) (fun _ => rfl) hf

attribute [scoped fun_prop] Implementation.ofFn

/-- Remove a successful optional result while retaining the selected computation. -/
@[source_bounds↓] noncomputable def Implementation.ofSome {α β : Type*}
    [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {f : α → β} {g : α → Option β} (hg : Implementation g)
    (hfg : ∀ x, g x = some (f x)) : Implementation f := by
  let hc : Implementation
      (fun x : Option β => match x with | none => (.nil : Tree) | some a => ⌜a⌝ₜ) := by
    source_fun_prop
  exact .ofEncode (fun x => by simp [hfg]) (hg.comp hc)

/-- Removing a known successful result adds one fixed operation and retains the selected call. -/
theorem Implementation.HasGrowth.ofSome {α β : Type*}
    [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {f : α → β} {g : α → Option β} {hg : Implementation g} {t p : α → ℕ}
    (h : hg.HasGrowth t p) (hfg : ∀ x, g x = some (f x)) :
    (hg.ofSome hfg).HasGrowth (fun x => t x + 1)
      (fun x => max (p x) ⌜g x⌝ₜ.size) := by
  let hc : Implementation
      (fun x : Option β => match x with | none => (.nil : Tree) | some a => ⌜a⌝ₜ) := by
    source_fun_prop
  have hgc : hc.HasGrowth (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
    source_fun_prop
    · exact Dominated.const _
    · apply (Dominated.refl _).max_same
      apply Dominated.of_le
      intro x
      cases x <;> simp
  exact (h.comp hgc).ofEncode (fun x => by simp [hfg])

@[source_bounds↓] noncomputable def Implementation.finApply {α : Type*} [UniqueEncoding Tree α] :
    Implementation (fun x : Σ n, (Fin n → α) × Fin n => x.2.1 x.2.2) :=
  .ofSome (by source_fun_prop : Implementation (fun x : Σ n, (Fin n → α) × Fin n =>
    (List.ofFn x.2.1)[x.2.2.val]?)) (by rintro ⟨n, f, i⟩; simp)

@[source_bounds↓] noncomputable def Implementation.finApplyFixed {α : Type*}
    [UniqueEncoding Tree α] (n : ℕ) : Implementation (fun x : (Fin n → α) × Fin n => x.1 x.2) :=
  .ofSome (by source_fun_prop : Implementation (fun x : (Fin n → α) × Fin n =>
    (List.ofFn x.1)[x.2.val]?)) (by rintro ⟨f, i⟩; simp)

@[source_bounds↓] noncomputable def Implementation.finValApplyPacked :
    Implementation (fun x : Σ n, Σ k, (Fin n → Fin k) × Fin n => (x.2.2.1 x.2.2.2).val) :=
  .ofSome (by source_fun_prop : Implementation
    (fun x : Σ n, Σ k, (Fin n → Fin k) × Fin n =>
      (List.ofFn (Fin.val ∘ x.2.2.1))[x.2.2.2.val]?)) (by rintro ⟨n, k, f, i⟩; simp)

attribute [scoped fun_prop] Implementation.finApply Implementation.finApplyFixed
  Implementation.finValApplyPacked

@[source_growth] theorem Implementation.hasGrowth_finApply {α : Type*} [UniqueEncoding Tree α] :
    (Implementation.finApply (α := α)).HasGrowth
      (fun x => ⌜x⌝ₜ.size ^ 2) (fun x => ⌜x⌝ₜ.size) := by
  have hget : Dominated
      (fun x : Σ n, (Fin n → α) × Fin n => ⌜(List.ofFn x.2.1)[x.2.2.val]?⌝ₜ.size)
      (fun x => ⌜x⌝ₜ.size) := by
    apply Dominated.of_le
    rintro ⟨n, f, i⟩
    have hsize := size_encode_fin_apply_le f i
    have he : (List.ofFn f)[i.val]? = some (f i) := by simp
    simp only [he, encode_option_some, Sigma.encode_mk, size_encode_prod, size_encode_unit]
    have hn := Tree.size_pos ⌜n⌝ₜ
    have hi := Tree.size_pos ⌜i⌝ₜ
    omega
  unfold Implementation.finApply
  refine (Implementation.HasGrowth.ofSome
    (t := fun x => ⌜x⌝ₜ.size ^ 2) (p := fun x => ⌜x⌝ₜ.size) ?_ _).mono ?_ ?_
  · source_fun_prop
    all_goals
      simp only [Dominated.add_iff, Dominated.max_iff]
      repeat' apply And.intro
      all_goals first
      | exact Dominated.const_of_pos _ (fun _ => Nat.pow_pos (Tree.size_pos _))
      | exact Dominated.const_of_pos _ (fun _ => Tree.size_pos _)
      | apply Dominated.of_le
        rintro ⟨n, f, i⟩
        simp only [Sigma.encode_mk, size_encode_prod, encode_fin, encode_fin_function,
          Tree.encode_self]
        omega
      | apply Dominated.pow
        apply Dominated.of_le
        rintro ⟨n, f, i⟩
        simp only [Sigma.encode_mk, size_encode_prod, encode_fin, encode_fin_function]
        omega
  · exact (Dominated.refl _).add_same
      (Dominated.const_of_pos _ fun _ => Nat.pow_pos (Tree.size_pos _))
  · exact (Dominated.refl _).max_same hget

@[source] theorem finApply_ftisp {α : Type*} [UniqueEncoding Tree α] :
    (fun x : Σ n, (Fin n → α) × Fin n => x.2.1 x.2.2) ∈
      FTISP .tree (fun n => n ^ 2) (fun n => n ^ 1) :=
  (by simpa only [pow_one] using Implementation.hasGrowth_finApply (α := α) :
    Implementation.finApply.HasGrowth
      (fun x => ⌜x⌝ₜ.size ^ 2) (fun x => ⌜x⌝ₜ.size ^ 1)).mem_ftisp_pow
      (by decide)

def rangeContinues (x : ℕ × List ℕ) : Bool := !x.1.bits.isEmpty

def rangeStep (x : ℕ × List ℕ) : ℕ × List ℕ :=
  let n := x.1.pred
  (n, n :: x.2)

@[source_bounds↓] noncomputable def rangeCheckImplementation :
    Implementation rangeContinues := by source_fun_prop

@[source_growth] theorem rangeCheck_growth : rangeCheckImplementation.HasGrowth
    (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  constructor
  · apply Dominated.of_le_mul 10
    rintro ⟨n, xs⟩
    cases h : n.bits <;> simp [rangeCheckImplementation, source_bounds]
  · apply Dominated.of_le_mul 7
    rintro ⟨n, xs⟩
    have := Tree.size_pos ⌜n⌝ₜ
    cases h : n.bits <;> simp [rangeCheckImplementation, source_bounds, h] <;> omega

@[source_bounds↓] noncomputable def rangeStepImplementation :
    Implementation rangeStep := by source_fun_prop

@[source_growth] theorem rangeStep_growth : rangeStepImplementation.HasGrowth
    (fun x => ⌜x.1⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  · simp only [Dominated.add_iff]
    repeat' apply And.intro
    all_goals first
      | exact Dominated.refl _
      | exact Dominated.const_of_pos _ (fun x => Tree.size_pos ⌜x.1⌝ₜ)
  · have hp := Implementation.hasGrowth_pred.size_encode
    have hpred := hp.comp (fun x : ℕ × List ℕ => x.1)
    have hinput : Dominated (fun x : ℕ × List ℕ => ⌜x.1⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) :=
      Dominated.of_le size_encode_fst_le
    have hacc : Dominated (fun x : ℕ × List ℕ => ⌜x.2⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) :=
      Dominated.of_le size_encode_snd_le
    simp only [encode_list_cons, size_encode_prod, Dominated.max_iff, Dominated.add_iff]
    repeat' apply And.intro
    all_goals first
      | exact Dominated.refl _
      | exact hinput
      | exact hacc
      | exact hpred.trans (hinput.max_same hinput)
      | exact Dominated.const_of_pos _ (fun _ => Tree.size_pos _)

def rangeLoop (x : ℕ × List ℕ) := List.range x.1 ++ x.2

def rangeInvariant (x y : ℕ × List ℕ) :=
  y.1 ≤ x.1 ∧ List.range y.1 ++ y.2 = List.range x.1 ++ x.2

theorem range_size :
    Dominated (fun z : {p : (ℕ × List ℕ) × (ℕ × List ℕ) // rangeInvariant p.1 p.2} =>
      ⌜z.1.2⌝ₜ.size) (fun z => (z.1.1.1 + 1) ^ 2 + ⌜z.1.1.2⌝ₜ.size) := by
  apply (((Dominated.refl (fun z :
    {p : (ℕ × List ℕ) × (ℕ × List ℕ) // rangeInvariant p.1 p.2} =>
      (z.1.1.1 + 1) ^ 2)).const_mul_left 10).add (Dominated.refl _)).mono_left
  intro z
  obtain ⟨⟨x, y⟩, hi⟩ := z
  have hn := size_encode_nat_le y.1
  have hr := size_encode_range_le x.1
  have hx := size_encode_list_append (List.range x.1) x.2
  have hy := size_encode_list_append (List.range y.1) y.2
  have he := congrArg (fun z : List ℕ => ⌜z⌝ₜ.size) hi.2
  have hp := Tree.size_pos ⌜List.range y.1⌝ₜ
  have hle := hi.1
  rcases y with ⟨n, acc⟩
  dsimp only at *
  simp only [size_encode_prod]
  nlinarith

@[source_bounds↓] noncomputable def rangeLoopImplementation : Implementation rangeLoop := by
  refine Implementation.tailLoop rangeCheckImplementation rangeStepImplementation
    Implementation.snd ⟨fun _ => 1, fun x => ⌜x⌝ₜ.size⟩
    ⟨fun x => ⌜x.1⌝ₜ.size, fun x => ⌜x⌝ₜ.size⟩ ⟨fun _ => 1, fun x => ⌜x⌝ₜ.size⟩
    rangeCheck_growth rangeStep_growth
    (Implementation.HasGrowth.of_bounds _ Implementation.bounds_snd
      (Dominated.const 1) (Dominated.refl _))
    rangeInvariant Prod.fst (fun x => x.1 + 1) (fun _ => 1)
    (fun x => (x.1 + 1) ^ 2 + ⌜x.2⌝ₜ.size)
    ?equation ?initial ?next_state ?decreases ?input_size ?check_peak ?step_peak ?stop_peak
    ?step_time ?check_time ?stop_time ?step_pos ?stop_pos
  case equation =>
    rintro ⟨n, xs⟩
    cases n with
    | zero => simp [rangeLoop, rangeContinues]
    | succ n =>
      have hbits : (n + 1).bits ≠ [] := by
        intro h; have := BitList.toNat_bits (n + 1); simp [h, BitList.toNat] at this
      simp [rangeLoop, rangeContinues, rangeStep, List.range_succ, List.append_assoc, hbits]
  case initial => exact fun _ => ⟨le_rfl, rfl⟩
  case next_state =>
    rintro x ⟨n, acc⟩ hi ht
    have hn : n ≠ 0 := by intro h; subst n; simp [rangeContinues] at ht
    refine ⟨(Nat.pred_le n).trans hi.1, ?_⟩
    rcases Nat.exists_eq_succ_of_ne_zero hn with ⟨k, rfl⟩
    simpa [rangeStep, List.range_succ, List.append_assoc] using hi.2
  case decreases =>
    rintro x ⟨n, acc⟩ hi ht
    have hn : n ≠ 0 := by intro h; subst n; simp [rangeContinues] at ht
    exact Nat.pred_lt hn
  case input_size => exact range_size
  case check_peak => exact range_size
  case step_peak => exact range_size
  case stop_peak => exact range_size
  case step_time =>
    apply Dominated.of_le_mul 4
    intro z
    have := size_encode_nat_le z.1.2.1
    have := z.2.1
    change ⌜z.1.2.1⌝ₜ.size ≤ 4 * (z.1.1.1 + 1)
    omega
  case check_time => exact Dominated.one fun _ => Nat.succ_pos _
  case stop_time => exact Dominated.refl _
  case step_pos => exact fun _ => Nat.succ_pos _
  case stop_pos => exact fun _ => Nat.zero_lt_one

@[source_growth] theorem rangeLoop_growth : rangeLoopImplementation.HasGrowth
    (fun x => (x.1 + 1) ^ 2) (fun x => (x.1 + 1) ^ 2 + ⌜x.2⌝ₜ.size) := by
  source_fun_prop
  · simp only [Dominated.add_iff]
    repeat' apply And.intro
    all_goals first
      | exact Dominated.of_le fun x => by nlinarith
      | exact Dominated.const_of_pos _ (fun x => Nat.pow_pos (Nat.succ_pos x.1))
  · exact Dominated.refl _

/-- Enumeration depends on the numerical length, not only its binary encoding size. -/
@[source_bounds↓] noncomputable def Implementation.range : Implementation List.range := by
  let hr := rangeLoopImplementation
  exact .ofEncode (by intro n; simp [rangeLoop])
    (by source_fun_prop : Implementation (fun n => rangeLoop (n, [])))

attribute [scoped fun_prop] Implementation.range

@[source_growth] theorem Implementation.hasGrowth_range : Implementation.range.HasGrowth
    (fun n => (n + 1) ^ 2) (fun n => (n + 1) ^ 2) := by
  source_fun_prop
  all_goals
    simp only [Dominated.add_iff, Dominated.max_iff]
    repeat' apply And.intro
    all_goals first
    | exact Dominated.refl _
    | exact Dominated.const_of_pos _ (fun n => Nat.pow_pos (Nat.succ_pos n))
    | apply Dominated.of_le_mul 6
      intro n
      have := size_encode_nat_le n
      try simp only [size_encode_prod, encode_list_nil, size_encode_unit] at *
      nlinarith

@[source_bounds↓] noncomputable def lengthStepImplementation {α : Type*}
    [UniqueEncoding Tree α] : Implementation (fun x : ℕ × α => x.1 + 1) := by source_fun_prop

@[source_growth] theorem lengthStep_growth {α : Type*} [UniqueEncoding Tree α] :
    (lengthStepImplementation (α := α)).HasGrowth
      (fun x => ⌜x.1⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  · exact (Dominated.const_of_pos 1 fun x : ℕ × α => Tree.size_pos ⌜x.1⌝ₜ).add_same
      (Dominated.refl _)
  · exact (Dominated.refl _).max_same (Dominated.of_le size_encode_fst_le)

@[source_bounds↓] noncomputable def lengthInitialImplementation {α : Type*}
    [UniqueEncoding Tree α] : Implementation (fun xs : List α => (0, xs)) := by source_fun_prop

@[source_growth] theorem lengthInitial_growth {α : Type*} [UniqueEncoding Tree α] :
    (lengthInitialImplementation (α := α)).HasGrowth
      (fun _ => 1) (fun xs => ⌜xs⌝ₜ.size) := by
  source_fun_prop
  · exact Dominated.const _
  · simp only [Dominated.max_iff, Dominated.add_iff, size_encode_prod]
    repeat' apply And.intro
    all_goals first
      | exact Dominated.refl _
      | exact Dominated.zero
      | exact Dominated.const_of_pos _ (fun _ => Tree.size_pos _)

/-- Count with the existing binary successor and retain its structural fold budget. -/
noncomputable def Implementation.length {α : Type*} [UniqueEncoding Tree α] :
    Implementation (List.length : List α → ℕ) :=
  .ofEncode (by simp) (lengthInitialImplementation.comp
    ((lengthStepImplementation (α := α)).foldl (f := fun n (_ : α) => n + 1)))

@[simp, source_bounds↓] theorem Implementation.bounds_length {α : Type*} [UniqueEncoding Tree α] :
    (Implementation.length (α := α)).bounds = compBounds (fun xs => (0, xs))
      lengthInitialImplementation.bounds
        ((lengthStepImplementation (α := α)).foldl (f := fun n (_ : α) => n + 1)).bounds := by
  rw [Implementation.length, Implementation.bounds_ofEncode, Implementation.bounds_comp]

attribute [scoped fun_prop] Implementation.length

@[source_growth] theorem Implementation.hasGrowth_length {α : Type*} [UniqueEncoding Tree α] :
    (Implementation.length (α := α)).HasGrowth
      (fun xs => ⌜xs⌝ₜ.size ^ 2) (fun xs => ⌜xs⌝ₜ.size) := by
  let I (xs rest : List α) (acc : ℕ) :=
    acc + rest.length ≤ xs.length ∧ ⌜rest⌝ₜ.size ≤ ⌜xs⌝ₜ.size
  have hs : Dominated (fun z : {z : List α × List α × ℕ // I z.1 z.2.1 z.2.2} =>
      ⌜(z.1.2.2, z.1.2.1)⌝ₜ.size) (fun z => ⌜z.1.1⌝ₜ.size) := by
    apply Dominated.of_le_mul 7
    rintro ⟨⟨xs, rest, acc⟩, ha, hr⟩
    have hacc := size_encode_nat_le acc
    have hlen := length_le_codeSize xs
    have hpos := Tree.size_pos ⌜xs⌝ₜ
    change acc + rest.length ≤ xs.length at ha
    change ⌜rest⌝ₜ.size ≤ ⌜xs⌝ₜ.size at hr
    simp only [size_encode_prod]
    omega
  have ht : Dominated
      (fun z : {z : List α × α × List α × ℕ // I z.1 (z.2.1 :: z.2.2.1) z.2.2.2} =>
        ⌜z.1.2.2.2⌝ₜ.size) (fun z => ⌜z.1.1⌝ₜ.size) := by
    apply Dominated.of_le_mul 5
    intro z
    have hacc := size_encode_nat_le z.1.2.2.2
    have hlen := length_le_codeSize z.1.1
    have hpos := Tree.size_pos ⌜z.1.1⌝ₜ
    have hi := z.2.1
    omega
  have hp : Dominated
      (fun z : {z : List α × α × List α × ℕ // I z.1 (z.2.1 :: z.2.2.1) z.2.2.2} =>
        ⌜(z.1.2.2.2, z.1.2.1)⌝ₜ.size) (fun z => ⌜z.1.1⌝ₜ.size) :=
    (hs.comp (fun z : {z : List α × α × List α × ℕ //
        I z.1 (z.2.1 :: z.2.2.1) z.2.2.2} =>
          ⟨(z.1.1, z.1.2.1 :: z.1.2.2.1, z.1.2.2.2), z.2⟩)).mono_left
      (fun z => by simp only [Function.comp_apply, size_encode_prod, encode_list_cons]; omega)
  have hfold := (lengthStep_growth (α := α)).foldl_of_invariant
    (f := fun n (_ : α) => n + 1) I id (fun _ => 0)
    (fun xs => ⌜xs⌝ₜ.size) (fun xs => ⌜xs⌝ₜ.size) (fun _ => ⟨by simp, le_rfl⟩)
    (by
      intro xs a rest acc hi
      refine ⟨by have := hi.1; simp only [List.length_cons] at *; omega, ?_⟩
      exact (show ⌜rest⌝ₜ.size ≤ ⌜a :: rest⌝ₜ.size by simp).trans hi.2)
    hs ht hp
  apply HasGrowth.of_bounds _ bounds_length
  · have hN : Dominated (List.length : List α → ℕ) (fun xs => ⌜xs⌝ₜ.size) :=
      Dominated.of_le length_le_codeSize
    have htime : Dominated (fun xs : List α => xs.length * ⌜xs⌝ₜ.size + xs.length + 1)
        (fun xs => ⌜xs⌝ₜ.size ^ 2) := by
      simp only [Dominated.add_iff]
      exact ⟨⟨(hN.mul (Dominated.refl _)).mono (fun _ => by rw [pow_two]),
        hN.le_pow (by decide)⟩, Dominated.const_of_pos _ fun _ => Nat.pow_pos (Tree.size_pos _)⟩
    exact (lengthInitial_growth.1.trans
      (Dominated.const_of_pos _ fun _ => Nat.pow_pos (Tree.size_pos _))).add_same
      (hfold.1.trans htime)
  · exact lengthInitial_growth.2.max_same hfold.2

/-- Construct a represented tuple using one selected callback for every environment and index. -/
@[source_bounds↓] noncomputable def Implementation.finFunction {ρ : Type*} {β : ρ → Type*}
    [UniqueEncoding Tree ρ] [∀ e, UniqueEncoding Tree (β e)]
    {n : ρ → ℕ} {f : (e : ρ) → Fin (n e) → β e}
    (hn : Implementation n) (hf : Implementation (fun p : Σ e, Fin (n e) => ⌜f p.1 p.2⌝ₜ)) :
    Implementation (fun e => ⌜f e⌝ₜ) := by
  let he : Implementation (fun e => (⟨e, List.finRange (n e)⟩ : Σ e, List (Fin (n e)))) :=
    .ofEncode (g := fun e => (e, List.range (n e)))
      (fun e => by simp only [Sigma.encode_mk, encode_prod, encode_finRange])
      (Implementation.identity.pair (hn.comp Implementation.range))
  let hm := he.mapDependentWith (f := fun e i => ⌜f e i⌝ₜ) hf
  exact .ofEncode (g := fun e => (List.finRange (n e)).map (fun i => ⌜f e i⌝ₜ))
    (fun e => by rw [← List.ofFn_eq_map, Tree.encode_self, encode_fin_function_codes]) hm

/-- Tabulation combines selected enumeration and callback specifications before summing.
The callback coefficient is shared by every environment and index. -/
theorem Implementation.HasGrowth.finFunction {ρ : Type*} {β : ρ → Type*}
    [UniqueEncoding Tree ρ] [∀ e, UniqueEncoding Tree (β e)]
    {n : ρ → ℕ} {f : (e : ρ) → Fin (n e) → β e}
    {hn : Implementation n} {hf : Implementation (fun p : Σ e, Fin (n e) => ⌜f p.1 p.2⌝ₜ)}
    {tn pn : ρ → ℕ} {tf pf : (Σ e, Fin (n e)) → ℕ}
    (gn : hn.HasGrowth tn pn) (gf : hf.HasGrowth tf pf) :
    (Implementation.finFunction hn hf).HasGrowth
      (fun e => (tn e + (n e + 1) ^ 2 + 1) +
        (((List.finRange (n e)).map (fun i => tf ⟨e, i⟩)).sum + n e + 1))
      (fun e => max (max (pn e) ((n e + 1) ^ 2))
        (max ⌜(e, List.range (n e))⌝ₜ.size (max (⌜f e⌝ₜ.size + 1)
          ((List.finRange (n e)).foldr (fun i s => max (pf ⟨e, i⟩) s) 0)))) := by
  have heq (e : ρ) : ⌜(⟨e, List.finRange (n e)⟩ : Σ e, List (Fin (n e)))⌝ₜ =
      ⌜(e, List.range (n e))⌝ₜ := by simp only [Sigma.encode_mk, encode_prod, encode_finRange]
  have hi := (Implementation.HasGrowth.refl (Implementation.identity (α := ρ))).pair
    (gn.comp Implementation.hasGrowth_range)
  have he := hi.ofEncode heq
  have hm := he.mapDependentWith (gf := gf) (f := fun e i => ⌜f e i⌝ₜ)
  apply (hm.ofEncode (fun e => by
    rw [← List.ofFn_eq_map, Tree.encode_self, encode_fin_function_codes])).mono
  · apply Dominated.of_le
    intro e
    simp only [Implementation.bounds_identity, Nat.zero_add, List.length_finRange]
    omega
  · apply Dominated.of_le
    intro e
    simp only [Implementation.bounds_identity, Function.comp_apply,
      Nat.zero_max, ← List.ofFn_eq_map,
      encode_fin_function_codes, heq, id_eq]
    omega


end Complexity.TreeProgram.Source

namespace tabulate

-- Enumeration is an optional library rule, after stored-field extraction and lookup.
attribute [scoped source_fallback] Complexity.TreeProgram.Source.Implementation.finFunction

open Lean Meta Mathlib.Meta.FunProp in
run_elab do
  addTheorem ``Complexity.TreeProgram.Source.Implementation.finFunction .scoped 50

end tabulate

namespace Complexity.TreeProgram.Source

/-- Evaluate the index and table once, then reuse the represented-list lookup. -/
@[source_bounds↓] noncomputable def Implementation.finApplyEncoded {ρ : Type*} {β : ρ → Type*}
    [UniqueEncoding Tree ρ] [∀ e, UniqueEncoding Tree (β e)]
    {n : ρ → ℕ} {f : (e : ρ) → Fin (n e) → β e} {i : (e : ρ) → Fin (n e)}
    (hf : Implementation (fun e => ⌜f e⌝ₜ)) (hi : Implementation (fun e => (i e).val)) :
    Implementation (fun e => ⌜f e (i e)⌝ₜ) := by
  let ht : Implementation (fun e => List.ofFn (fun i => ⌜f e i⌝ₜ)) :=
    .ofEncode (fun e => (encode_fin_function_codes _).trans (Tree.encode_self _).symm) hf
  exact ((hi.pair ht).comp Implementation.lookup).ofSome (by intro e; simp)

/-- A represented lookup combines the selected table and index calls with its saved lookup
specification. Successful-result packaging is handled once by this rule. -/
theorem Implementation.HasGrowth.finApplyEncoded {ρ : Type*} {β : ρ → Type*}
    [UniqueEncoding Tree ρ] [∀ e, UniqueEncoding Tree (β e)]
    {n : ρ → ℕ} {f : (e : ρ) → Fin (n e) → β e} {i : (e : ρ) → Fin (n e)}
    {hf : Implementation (fun e => ⌜f e⌝ₜ)} {hi : Implementation (fun e => (i e).val)}
    {tf pf ti pi : ρ → ℕ} (gf : hf.HasGrowth tf pf) (gi : hi.HasGrowth ti pi) :
    (Implementation.finApplyEncoded hf hi).HasGrowth
      (fun e => ti e + (tf e + 1) + ⌜((i e).val, ⌜f e⌝ₜ)⌝ₜ.size ^ 2 + 1)
      (fun e => max (pi e) (max (pf e) ⌜((i e).val, ⌜f e⌝ₜ)⌝ₜ.size)) := by
  have gt := gf.ofEncode (fun e =>
    (encode_fin_function_codes _).trans (Tree.encode_self _).symm)
  have gl := (gi.pair gt).comp Implementation.hasGrowth_lookup
  apply (gl.ofSome (by intro e; simp)).mono
  · apply Dominated.of_le
    intro e
    simp only [size_encode_prod, Tree.encode_self, encode_fin_function_codes]
    exact le_rfl
  · apply Dominated.of_le
    intro e
    have hv := size_encode_fin_apply_le (f e) (i e)
    have hi := Tree.size_pos ⌜(i e).val⌝ₜ
    simp only [Function.comp_apply, List.getElem?_ofFn, Fin.isLt, dite_true, Fin.eta,
      encode_option_some, size_encode_prod, Tree.encode_self, size_encode_unit,
      encode_fin_function_codes]
    omega

@[source_bounds↓] noncomputable def Implementation.finValApply {ρ : Type*} [UniqueEncoding Tree ρ]
    {n k : ρ → ℕ} {f : (e : ρ) → Fin (n e) → Fin (k e)} {i : (e : ρ) → Fin (n e)}
    (hf : Implementation (fun e => ⌜f e⌝ₜ)) (hi : Implementation (fun e => (i e).val)) :
    Implementation (fun e => (f e (i e)).val) :=
  .ofEncode (fun _ => (encode_fin _).symm.trans (Tree.encode_self _).symm)
    (Implementation.finApplyEncoded hf hi)

/-- Reading a finite-valued table retains the encoded lookup's selected program and budget. -/
theorem Implementation.HasGrowth.finValApply {ρ : Type*} [UniqueEncoding Tree ρ]
    {n k : ρ → ℕ} {f : (e : ρ) → Fin (n e) → Fin (k e)} {i : (e : ρ) → Fin (n e)}
    {hf : Implementation (fun e => ⌜f e⌝ₜ)} {hi : Implementation (fun e => (i e).val)}
    {tf pf ti pi : ρ → ℕ} (gf : hf.HasGrowth tf pf) (gi : hi.HasGrowth ti pi) :
    (Implementation.finValApply hf hi).HasGrowth
      (fun e => ti e + (tf e + 1) + ⌜((i e).val, ⌜f e⌝ₜ)⌝ₜ.size ^ 2 + 1)
      (fun e => max (pi e) (max (pf e) ⌜((i e).val, ⌜f e⌝ₜ)⌝ₜ.size)) :=
  (gf.finApplyEncoded gi).ofEncode
    (fun _ => (encode_fin _).symm.trans (Tree.encode_self _).symm)

/-- Extend a represented table without re-enumerating its indices. -/
@[source_bounds↓] noncomputable def Implementation.finSnoc {ρ : Type*} {α : ρ → Type*}
    [UniqueEncoding Tree ρ] [∀ e, UniqueEncoding Tree (α e)]
    {n : ρ → ℕ} {f : (e : ρ) → Fin (n e) → α e} {a : (e : ρ) → α e}
    (hf : Implementation (fun e => ⌜f e⌝ₜ)) (ha : Implementation (fun e => ⌜a e⌝ₜ)) :
    Implementation (fun e => ⌜Fin.snoc (α := fun _ => α e) (f e) (a e)⌝ₜ) := by
  let ht : Implementation (fun e => List.ofFn (fun i => ⌜f e i⌝ₜ)) :=
    .ofEncode (fun e => (encode_fin_function_codes _).trans (Tree.encode_self _).symm) hf
  let hs : Implementation (fun t : Tree => [t]) := by source_fun_prop
  refine .ofEncode ?_ (ht.append (ha.comp hs))
  intro e
  rw [Tree.encode_self, encode_fin_snoc]
  simpa only [List.map_append, List.map_cons, List.map_nil, List.map_ofFn, Function.comp_def] using
    (encode_list_map_of_encode (encode Tree) (fun _ => Tree.encode_self _)
      (List.ofFn (f e) ++ [a e])).symm

/-- Concatenate represented tables using the existing list append implementation. -/
@[source_bounds↓] def Implementation.finAppend {ρ : Type*} {α : ρ → Type*}
    [UniqueEncoding Tree ρ] [∀ e, UniqueEncoding Tree (α e)]
    {n m : ρ → ℕ} {f : (e : ρ) → Fin (n e) → α e}
    {g : (e : ρ) → Fin (m e) → α e}
    (hf : Implementation (fun e => ⌜f e⌝ₜ)) (hg : Implementation (fun e => ⌜g e⌝ₜ)) :
    Implementation (fun e => ⌜Fin.append (f e) (g e)⌝ₜ) := by
  let hf' : Implementation (fun e => List.ofFn (fun i => ⌜f e i⌝ₜ)) :=
    .ofEncode (fun e => (encode_fin_function_codes _).trans (Tree.encode_self _).symm) hf
  let hg' : Implementation (fun e => List.ofFn (fun i => ⌜g e i⌝ₜ)) :=
    .ofEncode (fun e => (encode_fin_function_codes _).trans (Tree.encode_self _).symm) hg
  refine Implementation.ofEncode
    (g := fun e => List.ofFn (fun i => ⌜f e i⌝ₜ) ++ List.ofFn (fun i => ⌜g e i⌝ₜ))
    ?_ (hf'.append hg')
  intro e
  rw [Tree.encode_self, encode_fin_function, List.ofFn_fin_append]
  simpa only [List.map_append, List.map_ofFn, Function.comp_def] using
    (encode_list_map_of_encode (encode Tree) (fun _ => Tree.encode_self _)
      (List.ofFn (f e) ++ List.ofFn (g e))).symm

-- Known operations reuse their certificates before unfolding. General lookup remains a
-- fallback after stored-field extraction; new tables still require explicit guidance.
attribute [scoped fun_prop] Implementation.finSnoc Implementation.finAppend
attribute [scoped source_fallback] Implementation.finApplyEncoded Implementation.finValApply

open Lean Meta Mathlib.Meta.FunProp in
run_elab do
  addTheorem ``Implementation.finApplyEncoded .scoped 100
  addTheorem ``Implementation.finValApply .scoped 100

abbrev FinCompInput := Σ n, Σ k, Σ m, (Fin n → Fin k) × (Fin k → Fin m)

@[source_bounds↓] noncomputable def finCompCountImplementation :
    Implementation (fun x : FinCompInput => x.1) := by source_fun_prop

@[source_growth] theorem finCompCount_growth : finCompCountImplementation.HasGrowth
    (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  · exact Dominated.const _
  · apply (Dominated.refl _).max_same
    apply Dominated.of_le
    rintro ⟨n, k, m, f, g⟩
    simp only [Sigma.encode_mk, size_encode_prod]
    omega

@[source_bounds↓] noncomputable def finCompStepImplementation :
    Implementation (fun z : Σ x : FinCompInput, Fin x.1 =>
      ⌜z.1.2.2.2.2 (z.1.2.2.2.1 z.2)⌝ₜ) := by source_fun_prop

@[source_growth] theorem finCompStep_growth : finCompStepImplementation.HasGrowth
    (fun z => ⌜z.1⌝ₜ.size ^ 2) (fun z => ⌜z.1⌝ₜ.size ^ 2) := by
  have hsize : Dominated (fun z : Σ x : FinCompInput, Fin x.1 => ⌜z⌝ₜ.size)
      (fun z => ⌜z.1⌝ₜ.size) := by
    apply Dominated.of_le_mul 7
    rintro ⟨⟨n, k, m, f, g⟩, i⟩
    have hi := size_encode_nat_le i.val
    have hn := card_le_size_encode_fin_function f
    have hlt := i.isLt
    dsimp only at *
    simp only [Sigma.encode_mk, size_encode_prod, encode_fin]
    omega
  have hfirst : Dominated (fun z : Σ x : FinCompInput, Fin x.1 =>
      ⌜(z.2.val, ⌜z.1.2.2.2.1⌝ₜ)⌝ₜ.size) (fun z => ⌜z.1⌝ₜ.size) := by
    apply hsize.mono_left
    rintro ⟨⟨n, k, m, f, g⟩, i⟩
    simp only [Sigma.encode_mk, size_encode_prod, Tree.encode_self, encode_fin]
    omega
  have hsecond : Dominated (fun z : Σ x : FinCompInput, Fin x.1 =>
      ⌜((z.1.2.2.2.1 z.2).val, ⌜z.1.2.2.2.2⌝ₜ)⌝ₜ.size) (fun z => ⌜z.1⌝ₜ.size) := by
    apply Dominated.of_le
    rintro ⟨⟨n, k, m, f, g⟩, i⟩
    have hf := size_encode_fin_apply_le f i
    simp only [Sigma.encode_mk, size_encode_prod, Tree.encode_self, encode_fin] at *
    omega
  source_fun_prop
  all_goals
    simp only [Dominated.add_iff, Dominated.max_iff]
    repeat' apply And.intro
    all_goals first
    | exact Dominated.const_of_pos _ (fun z => Nat.pow_pos (Tree.size_pos ⌜z.1⌝ₜ))
    | exact hsize.le_pow (by decide)
    | exact hfirst.pow 2
    | exact hsecond.pow 2
    | exact hfirst.le_pow (by decide)
    | exact hsecond.le_pow (by decide)
    | apply (hsize.le_pow (by decide)).mono_left
      rintro ⟨⟨n, k, m, f, g⟩, i⟩
      simp only [Sigma.encode_mk, size_encode_prod, Tree.encode_self, encode_fin]
      omega

/-- Stored table composition directly enumerates its selected lookup callback. -/
@[source_bounds↓] noncomputable def finCompImplementation :
    Implementation (fun x : FinCompInput => ⌜x.2.2.2.2 ∘ x.2.2.2.1⌝ₜ) :=
  Implementation.finFunction finCompCountImplementation finCompStepImplementation

@[source_growth] theorem finComp_growth : finCompImplementation.HasGrowth
    (fun x => ⌜x⌝ₜ.size ^ 3) (fun x => ⌜x⌝ₜ.size ^ 2) := by
  have hn : Dominated (fun x : FinCompInput => x.1) (fun x => ⌜x⌝ₜ.size) :=
    Dominated.of_le fun x => by
      rcases x with ⟨n, k, m, f, g⟩
      exact (card_le_size_encode_fin_function f).trans (by simp; omega)
  have hsum := Dominated.sum_finRange (n := fun x : FinCompInput => x.1)
    (a := fun x _ => ⌜x⌝ₜ.size ^ 2) (b := fun x => ⌜x⌝ₜ.size ^ 2)
    (Dominated.refl (fun z : Σ x : FinCompInput, Fin x.1 => ⌜z.1⌝ₜ.size ^ 2))
  have htime := hsum.trans (hn.mul (Dominated.refl _))
  have hout : Dominated (fun x : FinCompInput => ⌜x.2.2.2.2 ∘ x.2.2.2.1⌝ₜ.size)
      (fun x => ⌜x⌝ₜ.size ^ 2) := by
    apply Dominated.of_le_mul 4
    rintro ⟨n, k, m, f, g⟩
    have hn := card_le_size_encode_fin_function f
    have hout := size_encode_fin_function_le (g ∘ f) ⌜g⌝ₜ.size
      (fun i => size_encode_fin_apply_le g (f i))
    let N := ⌜(⟨n, k, m, f, g⟩ : FinCompInput)⌝ₜ.size
    have hf : ⌜f⌝ₜ.size ≤ N := by simp [N]; omega
    have hg : ⌜g⌝ₜ.size ≤ N := by simp [N]; omega
    have hN := Tree.size_pos ⌜(⟨n, k, m, f, g⟩ : FinCompInput)⌝ₜ
    change _ ≤ 4 * N ^ 2
    have hprod := Nat.mul_le_mul (hn.trans hf) (Nat.add_le_add_right hg 1)
    nlinarith
  have hr : Dominated (fun x : FinCompInput => ⌜List.range x.1⌝ₜ.size)
      (fun x => ⌜x⌝ₜ.size ^ 2) :=
    (((Dominated.refl _).const_mul_left 3).mono_left
      (fun x : FinCompInput => size_encode_range_le x.1)).trans
        ((hn.add_same (Dominated.one fun _ => Tree.size_pos _)).pow 2)
  have hprep : Dominated (fun x : FinCompInput => ⌜(x, List.range x.1)⌝ₜ.size)
      (fun x => ⌜x⌝ₜ.size ^ 2) := by
    simpa only [size_encode_prod] using
      ((Dominated.const_of_pos 1 fun _ => Nat.pow_pos (Tree.size_pos _)).add_same
        ((Dominated.refl (fun x : FinCompInput => ⌜x⌝ₜ.size)).le_pow (by decide))).add_same hr
  -- Fix the dependent codomain before elaborating the callback growth proof.
  have growth := Implementation.HasGrowth.finFunction
    (β := fun x : FinCompInput => Fin x.2.2.1) (n := fun x => x.1)
    (f := fun x i => x.2.2.2.2 (x.2.2.2.1 i))
    (hn := finCompCountImplementation) (hf := finCompStepImplementation)
    finCompCount_growth finCompStep_growth
  apply growth.mono
  all_goals
    simp only [Dominated.add_iff, Dominated.max_iff]
    repeat' apply And.intro
    all_goals first
    | exact Dominated.const_of_pos _ (fun _ => Nat.pow_pos (Tree.size_pos _))
    | exact htime.mono (fun x => by ring_nf; exact le_rfl)
    | exact hout
    | exact hprep
    | exact hn.le_pow (by decide)
    | exact (Dominated.refl (fun x : FinCompInput => ⌜x⌝ₜ.size)).le_pow (by decide)
    | exact ((hn.add_same (Dominated.one fun _ => Tree.size_pos _)).pow 2).mono_pow
        (by decide) (fun _ => Tree.size_pos _)
    | apply Dominated.foldr_max_le
      exact Dominated.refl _

/-- Reuse the existing table-composition backend while retaining the caller's program. -/
@[source_bounds↓] noncomputable def Implementation.finComp {ρ : Type*} [UniqueEncoding Tree ρ]
    {n k m : ρ → ℕ} {f : (e : ρ) → Fin (n e) → Fin (k e)}
    {g : (e : ρ) → Fin (k e) → Fin (m e)}
    (h : Implementation (fun e => (⟨n e, k e, m e, f e, g e⟩ :
      Σ n, Σ k, Σ m, (Fin n → Fin k) × (Fin k → Fin m)))) :
    Implementation (fun e => ⌜g e ∘ f e⌝ₜ) :=
  h.comp finCompImplementation

namespace Implementation

@[source_bounds↓] noncomputable def listNonempty {α : Type*} [UniqueEncoding Tree α] :
    Implementation (fun xs : List α => !xs.isEmpty) := by source_fun_prop

@[source_bounds↓] noncomputable def listTail {α : Type*} [UniqueEncoding Tree α] :
    Implementation (List.tail : List α → List α) := by source_fun_prop

@[source_growth] theorem hasGrowth_listNonempty {α : Type*} [UniqueEncoding Tree α] :
    (listNonempty (α := α)).HasGrowth (fun _ => 1) (fun xs => ⌜xs⌝ₜ.size) := by
  constructor
  · apply Dominated.of_le_mul 10
    intro xs
    cases xs <;> simp only [listNonempty, source_bounds] <;> omega
  · apply Dominated.of_le_mul 10
    intro xs
    have := Tree.size_pos ⌜xs⌝ₜ
    cases xs <;> simp only [listNonempty, source_bounds, encode_list_nil,
      encode_list_cons, size_encode_prod, size_encode_unit, List.isEmpty_nil,
      List.isEmpty_cons, encode_bool_true, encode_bool_false] at * <;> omega

@[source_growth] theorem hasGrowth_listTail {α : Type*} [UniqueEncoding Tree α] :
    (listTail (α := α)).HasGrowth (fun _ => 1) (fun xs => ⌜xs⌝ₜ.size) := by
  constructor
  · apply Dominated.of_le_mul 10
    intro xs
    cases xs <;> simp only [listTail, source_bounds] <;> omega
  · apply Dominated.of_le_mul 10
    intro xs
    have := Tree.size_pos ⌜xs⌝ₜ
    cases xs <;> simp only [listTail, source_bounds, encode_list_nil,
      encode_list_cons, size_encode_prod, size_encode_unit] at * <;> omega

end Implementation

attribute [scoped fun_prop] Implementation.listNonempty Implementation.listTail


end Complexity.TreeProgram.Source

namespace Complexity.TreeProgram.Source

noncomputable def Implementation.prepend {α : Type*} [UniqueEncoding Tree α] :
    Implementation (Function.uncurry (fun acc : List α => fun x => x :: acc)) := by
  source_fun_prop

@[source_growth] theorem prepend_growth {α : Type*} [UniqueEncoding Tree α] :
    (Implementation.prepend (α := α)).HasGrowth (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  · exact Dominated.const_of_pos _ (fun _ => Nat.zero_lt_one)
  · apply Dominated.of_le
    rintro ⟨acc, x⟩
    simp only [size_encode_prod]
    omega

@[scoped fun_prop] noncomputable def Implementation.prependFold {α : Type*}
    [UniqueEncoding Tree α] :
    Implementation (fun x : List α × List α => x.2.foldl (fun acc a => a :: acc) x.1) :=
  Implementation.prepend.foldl

@[source_growth] theorem prependFold_growth {α : Type*} [UniqueEncoding Tree α] :
    (Implementation.prependFold (α := α)).HasGrowth
      (fun x => x.2.length + 1) (fun x => ⌜x⌝ₜ.size) := prepend_growth.foldl_prepend

end Complexity.TreeProgram.Source
