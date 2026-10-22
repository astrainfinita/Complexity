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

def lookupCheckImplementation {α : Type*} [UniqueEncoding Tree α] :
    Implementation (lookupContinues (α := α)) (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  all_goals dominated

def lookupStepImplementation {α : Type*} [UniqueEncoding Tree α] :
    Implementation (lookupStep (α := α)) (fun x => ⌜x.1⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) := by
  have := Implementation.pred.size_encode.comp (fun x : ℕ × List α => x.1)
  source_fun_prop
  all_goals dominated

def lookupFinishImplementation {α : Type*} [UniqueEncoding Tree α] :
    Implementation (fun x : ℕ × List α => x.2.head?) (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  all_goals dominated

def lookupInvariant {α : Type*} [UniqueEncoding Tree α] (x y : ℕ × List α) :=
  y.1.bits.length ≤ x.1.bits.length ∧ ⌜y.2⌝ₜ.size ≤ ⌜x.2⌝ₜ.size ∧ y.2[y.1]? = x.2[x.1]?

theorem lookup_size {α : Type*} [UniqueEncoding Tree α] :
    Dominated (fun z : {p : (ℕ × List α) × (ℕ × List α) // lookupInvariant p.1 p.2} =>
      ⌜z.1.2⌝ₜ.size) (fun z => ⌜z.1.1⌝ₜ.size) := by
  dominated [lookupInvariant, size_encode_nat_le_length_bits]

/-- Indexed lookup uses selected callbacks and one invariant-family growth specification. -/
def Implementation.lookup {α : Type*} [UniqueEncoding Tree α] :
    Implementation (fun x : ℕ × List α => x.2[x.1]?) (fun x => ⌜x⌝ₜ.size ^ 2)
      (fun x => ⌜x⌝ₜ.size) := by
  refine (Implementation.tailLoop lookupCheckImplementation lookupStepImplementation
    lookupFinishImplementation lookupInvariant
    (fun x => x.2.length) (fun x => ⌜x⌝ₜ.size) (fun _ => 1) (fun x => ⌜x⌝ₜ.size)
    ?equation ?initial ?next_state ?decreases ?input_size ?check_peak ?step_peak ?stop_peak
    ?step_time ?check_time ?stop_time ?step_pos ?stop_pos).mono ?time (Dominated.refl _)
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
  case time => dominated

def Implementation.getElem? {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {f : α → List β} {i : α → ℕ} {tf pf ti pi : α → ℕ} (hf : Implementation f tf pf)
    (hi : Implementation i ti pi) :
    Implementation (fun x => (f x)[i x]?) (fun x => ti x + (tf x + 1) + ⌜(i x, f x)⌝ₜ.size ^ 2)
      (fun x => max (max (pi x) (max (pf x) ⌜(i x, f x)⌝ₜ.size)) ⌜(i x, f x)⌝ₜ.size) :=
  (hi.pair hf).comp Implementation.lookup

attribute [scoped fun_prop] Implementation.getElem?

def Implementation.encodeTree {α : Type*} [UniqueEncoding Tree α] :
    Implementation (encode Tree : α → Tree) (fun _ => 0) (fun _ => 0) :=
  .ofEncode (g := id) (fun _ => rfl) Implementation.identity

attribute [scoped fun_prop] Implementation.encodeTree

/-- Reading a represented table reuses its code; construction remains a separate premise. -/
def Implementation.ofFn {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {n : α → ℕ} {f : (x : α) → Fin (n x) → β} {t p : α → ℕ}
    (hf : Implementation (fun x => ⌜f x⌝ₜ) t p) :
    Implementation (fun x => List.ofFn (f x)) t p :=
  .ofEncode (g := fun x => ⌜f x⌝ₜ) (fun _ => rfl) hf

attribute [scoped fun_prop] Implementation.ofFn

/-- Read the value of a known successful optional result. -/
def Implementation.someValue {β : Type*} [UniqueEncoding Tree β] :
    Implementation (fun x : Option β => match x with | none => (.nil : Tree) | some a => ⌜a⌝ₜ)
      (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  all_goals dominated

/-- Removing a known successful result adds one fixed operation and retains the selected call. -/
def Implementation.ofSome {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {f : α → β} {g : α → Option β} {t p : α → ℕ} (hg : Implementation g t p)
    (hfg : ∀ x, g x = some (f x)) :
    Implementation f (fun x => t x + 1) (fun x => max (p x) ⌜g x⌝ₜ.size) :=
  .ofEncode (fun x => by simp [hfg]) (hg.comp Implementation.someValue)

def Implementation.finApply {α : Type*} [UniqueEncoding Tree α] :
    Implementation (fun x : Σ n, (Fin n → α) × Fin n => x.2.1 x.2.2) (fun x => ⌜x⌝ₜ.size ^ 2)
      (fun x => ⌜x⌝ₜ.size) := by
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
  refine (Implementation.ofSome
    (g := fun x : Σ n, (Fin n → α) × Fin n => (List.ofFn x.2.1)[x.2.2.val]?)
    (t := fun x => ⌜x⌝ₜ.size ^ 2) (p := fun x => ⌜x⌝ₜ.size) ?_ (by rintro ⟨n, f, i⟩; simp)).mono
    ?_ ?_
  · source_fun_prop
    all_goals dominated
  · exact (Dominated.refl _).add_same
      (Dominated.const_of_pos _ fun _ => Nat.pow_pos (Tree.size_pos _))
  · exact (Dominated.refl _).max_same hget

/-- A table whose length is fixed by the type is read like a runtime-length table. -/
def Implementation.finApplyFixed {α : Type*} [UniqueEncoding Tree α] (n : ℕ) :
    Implementation (fun x : (Fin n → α) × Fin n => x.1 x.2) (fun x => ⌜x⌝ₜ.size ^ 2)
      (fun x => ⌜x⌝ₜ.size) := by
  have hget : Dominated
      (fun x : (Fin n → α) × Fin n => ⌜(List.ofFn x.1)[x.2.val]?⌝ₜ.size)
      (fun x => ⌜x⌝ₜ.size) := by
    apply Dominated.of_le
    rintro ⟨f, i⟩
    have hsize := size_encode_fin_apply_le f i
    have he : (List.ofFn f)[i.val]? = some (f i) := by simp
    simp only [he, encode_option_some, size_encode_prod, size_encode_unit]
    have hi := Tree.size_pos ⌜i⌝ₜ
    omega
  refine (Implementation.ofSome
    (g := fun x : (Fin n → α) × Fin n => (List.ofFn x.1)[x.2.val]?)
    (t := fun x => ⌜x⌝ₜ.size ^ 2) (p := fun x => ⌜x⌝ₜ.size) ?_ (by rintro ⟨f, i⟩; simp)).mono
    ?_ ?_
  · source_fun_prop
    all_goals dominated
  · exact (Dominated.refl _).add_same
      (Dominated.const_of_pos _ fun _ => Nat.pow_pos (Tree.size_pos _))
  · exact (Dominated.refl _).max_same hget

attribute [scoped fun_prop] Implementation.finApply Implementation.finApplyFixed

theorem finApply_ftisp {α : Type*} [UniqueEncoding Tree α] :
    (fun x : Σ n, (Fin n → α) × Fin n => x.2.1 x.2.2) ∈
      FTISP .tree (fun n => n ^ 2) (fun n => n ^ 1) :=
  (Implementation.finApply.mono (Dominated.refl _)
    (Dominated.of_le fun _ => by rw [pow_one])).mem_ftisp_pow (by decide)

def rangeContinues (x : ℕ × List ℕ) : Bool := !x.1.bits.isEmpty

def rangeStep (x : ℕ × List ℕ) : ℕ × List ℕ :=
  let n := x.1.pred
  (n, n :: x.2)

def rangeCheckImplementation :
    Implementation rangeContinues (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  all_goals dominated

def rangeStepImplementation :
    Implementation rangeStep (fun x => ⌜x.1⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) := by
  have := Implementation.pred.size_encode.comp (fun x : ℕ × List ℕ => x.1)
  source_fun_prop
  all_goals dominated

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

def rangeLoopImplementation : Implementation rangeLoop (fun x => (x.1 + 1) ^ 2)
    (fun x => (x.1 + 1) ^ 2 + ⌜x.2⌝ₜ.size) := by
  refine (Implementation.tailLoop rangeCheckImplementation rangeStepImplementation
    Implementation.snd rangeInvariant Prod.fst (fun x => x.1 + 1) (fun _ => 1)
    (fun x => (x.1 + 1) ^ 2 + ⌜x.2⌝ₜ.size)
    ?equation ?initial ?next_state ?decreases ?input_size ?check_peak ?step_peak ?stop_peak
    ?step_time ?check_time ?stop_time ?step_pos ?stop_pos).mono ?time (Dominated.refl _)
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
  case step_time => dominated [rangeInvariant]
  case check_time => exact Dominated.one fun _ => Nat.succ_pos _
  case stop_time => exact Dominated.refl _
  case step_pos => exact fun _ => Nat.succ_pos _
  case stop_pos => exact fun _ => Nat.zero_lt_one
  case time => dominated

/-- Enumeration depends on the numerical length, not only its binary encoding size. -/
def Implementation.range :
    Implementation List.range (fun n => (n + 1) ^ 2) (fun n => (n + 1) ^ 2) := by
  let hr := rangeLoopImplementation
  source_fun_prop via (fun n => rangeLoop (n, []))
  case source_eq => funext n; simp [rangeLoop]
  all_goals dominated

attribute [scoped fun_prop] Implementation.range

def lengthStepImplementation {α : Type*} [UniqueEncoding Tree α] :
    Implementation (fun x : ℕ × α => x.1 + 1) (fun x => ⌜x.1⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  all_goals dominated

def lengthInitialImplementation {α : Type*} [UniqueEncoding Tree α] :
    Implementation (fun xs : List α => (0, xs)) (fun _ => 1) (fun xs => ⌜xs⌝ₜ.size) := by
  source_fun_prop
  all_goals dominated

/-- Count with the existing binary successor along a structural fold. -/
def Implementation.length {α : Type*} [UniqueEncoding Tree α] :
    Implementation (List.length : List α → ℕ) (fun xs => ⌜xs⌝ₜ.size ^ 2)
      (fun xs => ⌜xs⌝ₜ.size) := by
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
  have hfold := Dominated.foldl_of_invariant (f := fun n (_ : α) => n + 1)
    (t := fun x => ⌜x.1⌝ₜ.size) (p := fun x => ⌜x⌝ₜ.size) I (fun xs => xs) (fun _ => 0)
    (fun xs => ⌜xs⌝ₜ.size) (fun xs => ⌜xs⌝ₜ.size) (fun _ => ⟨by simp, le_rfl⟩)
    (by
      intro xs a rest acc hi
      refine ⟨by have := hi.1; simp only [List.length_cons] at *; omega, ?_⟩
      exact (show ⌜rest⌝ₜ.size ≤ ⌜a :: rest⌝ₜ.size by simp).trans hi.2)
    hs ht hp
  obtain ⟨htime, hpeak⟩ := hfold
  obtain ⟨-, hpeak⟩ := Dominated.max_iff.mp hpeak
  refine (Implementation.ofEncode (by simp) (lengthInitialImplementation.comp
    ((lengthStepImplementation (α := α)).foldl (f := fun n (_ : α) => n + 1)))).mono ?_ ?_
  all_goals dominated

attribute [scoped fun_prop] Implementation.length

/-- Construct a represented tuple using one selected callback for every environment and index.
Tabulation sums the callback growth; one coefficient covers every environment and index. -/
def Implementation.finFunction {ρ : Type*} {β : ρ → Type*}
    [UniqueEncoding Tree ρ] [∀ e, UniqueEncoding Tree (β e)]
    {n : ρ → ℕ} {f : (e : ρ) → Fin (n e) → β e} {tn pn : ρ → ℕ} {tf pf : (Σ e, Fin (n e)) → ℕ}
    (hn : Implementation n tn pn)
    (hf : Implementation (fun p : Σ e, Fin (n e) => ⌜f p.1 p.2⌝ₜ) tf pf) :
    Implementation (fun e => ⌜f e⌝ₜ)
      (fun e => (tn e + (n e + 1) ^ 2 + 1) +
        (((List.finRange (n e)).map (fun i => tf ⟨e, i⟩)).sum + n e + 1))
      (fun e => max (max (pn e) ((n e + 1) ^ 2))
        (max ⌜(e, List.range (n e))⌝ₜ.size (max (⌜f e⌝ₜ.size + 1)
          ((List.finRange (n e)).foldr (fun i s => max (pf ⟨e, i⟩) s) 0)))) := by
  have heq (e : ρ) : ⌜(⟨e, List.finRange (n e)⟩ : Σ e, List (Fin (n e)))⌝ₜ =
      ⌜(e, List.range (n e))⌝ₜ := by simp only [Sigma.encode_mk, encode_prod, encode_finRange]
  let he := Implementation.ofEncode heq
    (Implementation.identity.pair (hn.comp Implementation.range))
  refine (Implementation.ofEncode (g := fun e => (List.finRange (n e)).map (fun i => ⌜f e i⌝ₜ))
    (fun e => by rw [← List.ofFn_eq_map, Tree.encode_self, encode_fin_function_codes])
    (he.mapDependentWith (f := fun e i => ⌜f e i⌝ₜ) hf)).mono ?_ ?_
  · apply Dominated.of_le
    intro e
    simp only [Nat.zero_add, List.length_finRange]
    omega
  · apply Dominated.of_le
    intro e
    simp only [Nat.zero_max, ← List.ofFn_eq_map,
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
def Implementation.finApplyEncoded {ρ : Type*} {β : ρ → Type*}
    [UniqueEncoding Tree ρ] [∀ e, UniqueEncoding Tree (β e)]
    {n : ρ → ℕ} {f : (e : ρ) → Fin (n e) → β e} {i : (e : ρ) → Fin (n e)} {tf pf ti pi : ρ → ℕ}
    (hf : Implementation (fun e => ⌜f e⌝ₜ) tf pf)
    (hi : Implementation (fun e => (i e).val) ti pi) :
    Implementation (fun e => ⌜f e (i e)⌝ₜ)
      (fun e => ti e + (tf e + 1) + ⌜(i e, f e)⌝ₜ.size ^ 2 + 1)
      (fun e => max (pi e) (max (pf e) ⌜(i e, f e)⌝ₜ.size)) := by
  let ht : Implementation (fun e => List.ofFn (fun i => ⌜f e i⌝ₜ)) tf pf :=
    .ofEncode (fun e => (encode_fin_function_codes _).trans (Tree.encode_self _).symm) hf
  refine (((hi.pair ht).comp Implementation.lookup).ofSome (by intro e; simp)).mono ?_ ?_
  · apply Dominated.of_le
    intro e
    simp only [size_encode_prod, encode_fin_function_codes, encode_fin]
    exact le_rfl
  · apply Dominated.of_le
    intro e
    have hv := size_encode_fin_apply_le (f e) (i e)
    have hi := Tree.size_pos ⌜(i e).val⌝ₜ
    simp only [Function.comp_apply, List.getElem?_ofFn, Fin.isLt, dite_true, Fin.eta,
      encode_option_some, size_encode_prod, Tree.encode_self, size_encode_unit,
      encode_fin_function_codes, encode_fin]
    omega

/-- Reading a finite-valued table retains the encoded lookup's selected program and growth. -/
def Implementation.finValApply {ρ : Type*} [UniqueEncoding Tree ρ]
    {n k : ρ → ℕ} {f : (e : ρ) → Fin (n e) → Fin (k e)} {i : (e : ρ) → Fin (n e)}
    {tf pf ti pi : ρ → ℕ} (hf : Implementation (fun e => ⌜f e⌝ₜ) tf pf)
    (hi : Implementation (fun e => (i e).val) ti pi) :
    Implementation (fun e => (f e (i e)).val)
      (fun e => ti e + (tf e + 1) + ⌜(i e, f e)⌝ₜ.size ^ 2 + 1)
      (fun e => max (pi e) (max (pf e) ⌜(i e, f e)⌝ₜ.size)) :=
  .ofEncode (fun _ => (encode_fin _).symm.trans (Tree.encode_self _).symm)
    (Implementation.finApplyEncoded hf hi)

/-- A one-element list of an encoded value. -/
def Implementation.singleton : Implementation (fun t : Tree => [t]) (fun _ => 1)
    (fun t => ⌜t⌝ₜ.size) := by
  source_fun_prop
  all_goals dominated

/-- Extend a represented table without re-enumerating its indices. -/
def Implementation.finSnoc {ρ : Type*} {α : ρ → Type*}
    [UniqueEncoding Tree ρ] [∀ e, UniqueEncoding Tree (α e)]
    {n : ρ → ℕ} {f : (e : ρ) → Fin (n e) → α e} {a : (e : ρ) → α e} {tf pf ta pa : ρ → ℕ}
    (hf : Implementation (fun e => ⌜f e⌝ₜ) tf pf) (ha : Implementation (fun e => ⌜a e⌝ₜ) ta pa) :
    Implementation (fun e => ⌜Fin.snoc (α := fun _ => α e) (f e) (a e)⌝ₜ)
      (fun e => tf e + ta e + n e + 1)
      (fun e => max (pf e) (max (pa e) (⌜f e⌝ₜ.size + ⌜a e⌝ₜ.size))) := by
  let ht : Implementation (fun e => List.ofFn (fun i => ⌜f e i⌝ₜ)) tf pf :=
    .ofEncode (fun e => (encode_fin_function_codes _).trans (Tree.encode_self _).symm) hf
  refine (Implementation.ofEncode ?_ (ht.append (ha.comp Implementation.singleton))).mono ?_ ?_
  · intro e
    rw [Tree.encode_self, encode_fin_snoc]
    simpa only [List.map_append, List.map_cons, List.map_nil, List.map_ofFn,
      Function.comp_def] using
      (encode_list_map_of_encode (encode Tree) (fun _ => Tree.encode_self _)
        (List.ofFn (f e) ++ [a e])).symm
  · apply Dominated.of_le_mul 2
    intro e
    simp only [List.length_ofFn]
    omega
  · apply Dominated.of_le_mul 3
    intro e
    have := Tree.size_pos ⌜f e⌝ₜ
    have := Tree.size_pos ⌜a e⌝ₜ
    simp only [Function.comp_apply, Tree.encode_self, encode_fin_function_codes,
      encode_list_cons, encode_list_nil, size_encode_prod, size_encode_unit, max_le_iff]
    omega

/-- Concatenate represented tables using the existing list append implementation. -/
def Implementation.finAppend {ρ : Type*} {α : ρ → Type*}
    [UniqueEncoding Tree ρ] [∀ e, UniqueEncoding Tree (α e)]
    {n m : ρ → ℕ} {f : (e : ρ) → Fin (n e) → α e}
    {g : (e : ρ) → Fin (m e) → α e} {tf pf tg pg : ρ → ℕ}
    (hf : Implementation (fun e => ⌜f e⌝ₜ) tf pf) (hg : Implementation (fun e => ⌜g e⌝ₜ) tg pg) :
    Implementation (fun e => ⌜Fin.append (f e) (g e)⌝ₜ) (fun e => tf e + (tg e + (n e + 1)))
      (fun e => max (pf e) (max (pg e) (⌜f e⌝ₜ.size + ⌜g e⌝ₜ.size))) := by
  let hf' : Implementation (fun e => List.ofFn (fun i => ⌜f e i⌝ₜ)) tf pf :=
    .ofEncode (fun e => (encode_fin_function_codes _).trans (Tree.encode_self _).symm) hf
  let hg' : Implementation (fun e => List.ofFn (fun i => ⌜g e i⌝ₜ)) tg pg :=
    .ofEncode (fun e => (encode_fin_function_codes _).trans (Tree.encode_self _).symm) hg
  refine (Implementation.ofEncode
    (g := fun e => List.ofFn (fun i => ⌜f e i⌝ₜ) ++ List.ofFn (fun i => ⌜g e i⌝ₜ))
    ?_ (hf'.append hg')).mono (Dominated.of_le fun e => by simp only [List.length_ofFn, le_refl])
      (Dominated.of_le fun e => by simp only [encode_fin_function_codes, le_refl])
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

def finCompCountImplementation :
    Implementation (fun x : FinCompInput => x.1) (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  all_goals dominated

def finCompStepImplementation :
    Implementation (fun z : Σ x : FinCompInput, Fin x.1 => ⌜z.1.2.2.2.2 (z.1.2.2.2.1 z.2)⌝ₜ)
      (fun z => ⌜z.1⌝ₜ.size ^ 2) (fun z => ⌜z.1⌝ₜ.size ^ 2) := by
  source_fun_prop
  all_goals dominated

/-- Stored table composition directly enumerates its selected lookup callback. -/
def finCompImplementation : Implementation (fun x : FinCompInput => ⌜x.2.2.2.2 ∘ x.2.2.2.1⌝ₜ)
    (fun x => ⌜x⌝ₜ.size ^ 3) (fun x => ⌜x⌝ₜ.size ^ 2) := by
  refine (Implementation.finFunction (β := fun x : FinCompInput => Fin x.2.2.1)
    (n := fun x => x.1) (f := fun x => x.2.2.2.2 ∘ x.2.2.2.1)
    finCompCountImplementation finCompStepImplementation).mono ?_ ?_
  all_goals dominated

/-- Reuse the existing table-composition backend while retaining the caller's program. -/
def Implementation.finComp {ρ : Type*} [UniqueEncoding Tree ρ]
    {n k m : ρ → ℕ} {f : (e : ρ) → Fin (n e) → Fin (k e)}
    {g : (e : ρ) → Fin (k e) → Fin (m e)} {t p : ρ → ℕ}
    (h : Implementation (fun e => (⟨n e, k e, m e, f e, g e⟩ :
      Σ n, Σ k, Σ m, (Fin n → Fin k) × (Fin k → Fin m))) t p) :
    Implementation (fun e => ⌜g e ∘ f e⌝ₜ)
      (fun e => t e + ⌜(⟨n e, k e, m e, f e, g e⟩ : FinCompInput)⌝ₜ.size ^ 3)
      (fun e => max (p e) (⌜(⟨n e, k e, m e, f e, g e⟩ : FinCompInput)⌝ₜ.size ^ 2)) :=
  h.comp finCompImplementation

namespace Implementation

def listNonempty {α : Type*} [UniqueEncoding Tree α] :
    Implementation (fun xs : List α => !xs.isEmpty) (fun _ => 1) (fun xs => ⌜xs⌝ₜ.size) := by
  source_fun_prop
  all_goals dominated

def listTail {α : Type*} [UniqueEncoding Tree α] :
    Implementation (List.tail : List α → List α) (fun _ => 1) (fun xs => ⌜xs⌝ₜ.size) := by
  source_fun_prop
  all_goals dominated

end Implementation

attribute [scoped fun_prop] Implementation.listNonempty Implementation.listTail

def Implementation.prepend {α : Type*} [UniqueEncoding Tree α] :
    Implementation (Function.uncurry (fun acc : List α => fun x => x :: acc)) (fun _ => 1)
      (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  all_goals dominated

/-- Prepending charges each element once and stores only the final list. -/
@[scoped fun_prop] def Implementation.prependFold {α : Type*} [UniqueEncoding Tree α] :
    Implementation (fun x : List α × List α => x.2.foldl (fun acc a => a :: acc) x.1)
      (fun x => x.2.length + 1) (fun x => ⌜x⌝ₜ.size) :=
  Implementation.prepend.foldl.mono (by dominated [foldlTime_eq_sum (t := fun _ : α => 1)])
    (by dominated [foldlPeak_prepend])

end Complexity.TreeProgram.Source
