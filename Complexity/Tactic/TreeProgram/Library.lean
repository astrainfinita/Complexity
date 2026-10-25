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

def implementationLookupContinues {α : Type*} [UniqueEncoding Tree α] :
    Implementation (lookupContinues (α := α)) (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  all_goals dominated

def implementationLookupStep {α : Type*} [UniqueEncoding Tree α] :
    Implementation (lookupStep (α := α)) (fun x => ⌜x.1⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) := by
  have := Nat.implementationPred.size_encode.comp (fun x : ℕ × List α => x.1)
  source_fun_prop
  all_goals dominated

def implementationLookupFinish {α : Type*} [UniqueEncoding Tree α] :
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
def implementationLookup {α : Type*} [UniqueEncoding Tree α] :
    Implementation (fun x : ℕ × List α => x.2[x.1]?) (fun x => ⌜x⌝ₜ.size ^ 2)
      (fun x => ⌜x⌝ₜ.size) := by
  refine (Implementation.tailLoop implementationLookupContinues implementationLookupStep
    implementationLookupFinish lookupInvariant
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

theorem encode_option_codes {γ : Type*} [UniqueEncoding Tree γ] (o : Option γ) :
    ⌜o.map (encode Tree)⌝ₜ = ⌜o⌝ₜ := by
  cases o <;> simp only [Option.map_none, Option.map_some, encode_option_none, encode_option_some,
    encode_prod, Tree.encode_self]

/-- Look an index up in a list, on the codes of its entries. -/
def Implementation.getElem? {α : Type*} {β : α → Type*} [UniqueEncoding Tree α]
    [∀ x, UniqueEncoding Tree (β x)] {f : (x : α) → List (β x)} {i : α → ℕ} {tf pf ti pi : α → ℕ}
    (hf : Implementation f tf pf) (hi : Implementation i ti pi) :
    Implementation (fun x => (f x)[i x]?) (fun x => ti x + (tf x + 1) + ⌜(i x, f x)⌝ₜ.size ^ 2)
      (fun x => max (max (pi x) (max (pf x) ⌜(i x, f x)⌝ₜ.size)) ⌜(i x, f x)⌝ₜ.size) :=
  (((hi.pair hf.listCodes).comp implementationLookup).ofEncode fun x => by
      simp only [Function.comp_apply, List.getElem?_map, encode_option_codes]).mono
    (Dominated.of_le fun x => by simp only [size_encode_prod, encode_list_codes, le_refl])
    (Dominated.of_le fun x => by simp only [size_encode_prod, encode_list_codes, le_refl])

attribute [scoped fun_prop] Implementation.getElem?

/-- The code of a computed value is the value's own result. -/
def Implementation.encodeTree {α : Type*} {β : α → Type*} [UniqueEncoding Tree α]
    [∀ x, UniqueEncoding Tree (β x)] {v : (x : α) → β x} {t p : α → ℕ}
    (hv : Implementation v t p) : Implementation (fun x => ⌜v x⌝ₜ) t p :=
  hv.ofEncode fun _ => Tree.encode_self _

attribute [scoped fun_prop] Implementation.encodeTree

/-- Reading a represented table reuses its code; construction remains a separate premise. -/
def Implementation.ofFn {α : Type*} {β : α → Type*} [UniqueEncoding Tree α]
    [∀ x, UniqueEncoding Tree (β x)] {n : α → ℕ} {f : (x : α) → Fin (n x) → β x} {t p : α → ℕ}
    (hf : Implementation (fun x => ⌜f x⌝ₜ) t p) :
    Implementation (fun x => List.ofFn (f x)) t p :=
  .ofEncode (g := fun x => ⌜f x⌝ₜ) (fun _ => rfl) hf

attribute [scoped fun_prop] Implementation.ofFn

/-- Read the value of a known successful optional result. -/
def implementationSomeValue {β : Type*} [UniqueEncoding Tree β] :
    Implementation (fun x : Option β => match x with | none => (.nil : Tree) | some a => ⌜a⌝ₜ)
      (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  all_goals dominated

/-- Removing a known successful result adds one fixed operation and retains the selected call. -/
def Implementation.ofSome {α : Type*} {β : α → Type*} [UniqueEncoding Tree α]
    [∀ x, UniqueEncoding Tree (β x)] {f : (x : α) → β x} {g : (x : α) → Option (β x)}
    {t p : α → ℕ} (hg : Implementation g t p) (hfg : ∀ x, g x = some (f x)) :
    Implementation f (fun x => t x + 1) (fun x => max (p x) ⌜g x⌝ₜ.size) :=
  (((hg.ofEncode (f := fun x => (g x).map (encode Tree)) fun x => encode_option_codes _).comp
    implementationSomeValue).ofEncode fun x => by simp [hfg]).mono
    (Dominated.refl _) (Dominated.of_le fun x => by simp only [encode_option_codes, le_refl])

def rangeContinues (x : ℕ × List ℕ) : Bool := !x.1.bits.isEmpty

def rangeStep (x : ℕ × List ℕ) : ℕ × List ℕ :=
  let n := x.1.pred
  (n, n :: x.2)

def implementationRangeContinues :
    Implementation rangeContinues (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  all_goals dominated

def implementationRangeStep :
    Implementation rangeStep (fun x => ⌜x.1⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) := by
  have := Nat.implementationPred.size_encode.comp (fun x : ℕ × List ℕ => x.1)
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

def implementationRangeLoop : Implementation rangeLoop (fun x => (x.1 + 1) ^ 2)
    (fun x => (x.1 + 1) ^ 2 + ⌜x.2⌝ₜ.size) := by
  refine (Implementation.tailLoop implementationRangeContinues implementationRangeStep
    Prod.implementationSnd rangeInvariant Prod.fst (fun x => x.1 + 1) (fun _ => 1)
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
def _root_.List.implementationRange :
    Implementation List.range (fun n => (n + 1) ^ 2) (fun n => (n + 1) ^ 2) := by
  let hr := implementationRangeLoop
  source_fun_prop via (fun n => rangeLoop (n, []))
  case source_eq => funext n; simp [rangeLoop]
  all_goals dominated

attribute [scoped fun_prop] List.implementationRange

def implementationLengthStep {α : Type*} [UniqueEncoding Tree α] :
    Implementation (fun x : ℕ × α => x.1 + 1) (fun x => ⌜x.1⌝ₜ.size) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  all_goals dominated

def implementationLengthInitial {α : Type*} [UniqueEncoding Tree α] :
    Implementation (fun xs : List α => (0, xs)) (fun _ => 1) (fun xs => ⌜xs⌝ₜ.size) := by
  source_fun_prop
  all_goals dominated

/-- Count with the existing binary successor along a structural fold. -/
@[uniform_program] def _root_.List.implementationLength {α : Type*} [UniqueEncoding Tree α] :
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
  refine (Implementation.ofEncode (by simp) (implementationLengthInitial.comp
    ((implementationLengthStep (α := α)).foldl (f := fun n (_ : α) => n + 1)))).mono ?_ ?_
  all_goals dominated

attribute [scoped fun_prop] List.implementationLength

/-- Construct a represented tuple using one selected callback for every environment and index.
Tabulation sums the callback growth; one coefficient covers every environment and index. -/
def Implementation.finFunction {ρ : Type*} {β : ρ → Type*}
    [UniqueEncoding Tree ρ] [instβ : ∀ e, UniqueEncoding Tree (β e)]
    {n : ρ → ℕ} {f : (e : ρ) → Fin (n e) → β e} {tn pn : ρ → ℕ} {tf pf : (Σ e, Fin (n e)) → ℕ}
    (hn : Implementation n tn pn)
    (hf : Implementation (fun p : Σ e, Fin (n e) => f p.1 p.2) tf pf) :
    Implementation (fun e => ⌜f e⌝ₜ)
      (fun e => (tn e + (n e + 1) ^ 2 + 1) +
        (((List.finRange (n e)).map (fun i => tf ⟨e, i⟩)).sum + n e + 1))
      (fun e => max (max (pn e) ((n e + 1) ^ 2))
        (max ⌜(e, List.range (n e))⌝ₜ.size (max (⌜f e⌝ₜ.size + 1)
          ((List.finRange (n e)).foldr (fun i s => max (pf ⟨e, i⟩) s) 0)))) := by
  have heq (e : ρ) : ⌜(⟨e, List.finRange (n e)⟩ : Σ e, List (Fin (n e)))⌝ₜ =
      ⌜(e, List.range (n e))⌝ₜ := by simp only [Sigma.encode_mk, encode_prod, encode_finRange]
  let he := Implementation.ofEncode heq
    (Implementation.identity.pair (hn.comp List.implementationRange))
  refine (Implementation.ofEncode (g := fun e => (List.finRange (n e)).map (f e))
    (fun e => by rw [← List.ofFn_eq_map, Tree.encode_self, encode_fin_function])
    (he.mapDependentWith (f := f) hf)).mono ?_ ?_
  · apply Dominated.of_le
    intro e
    simp only [Nat.zero_add, List.length_finRange]
    omega
  · apply Dominated.of_le
    intro e
    simp only [Nat.zero_max, ← List.ofFn_eq_map, ← encode_fin_function, heq, id_eq]
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

/-- Reading a represented table evaluates the index and the table once, then looks the index up
in the table's code. -/
def Implementation.finApply {ρ : Type*} {β : ρ → Type*}
    [UniqueEncoding Tree ρ] [∀ e, UniqueEncoding Tree (β e)]
    {n : ρ → ℕ} {f : (e : ρ) → Fin (n e) → β e} {i : (e : ρ) → Fin (n e)} {tf pf ti pi : ρ → ℕ}
    (hf : Implementation (fun e => ⌜f e⌝ₜ) tf pf)
    (hi : Implementation (fun e => (i e).val) ti pi) :
    Implementation (fun e => f e (i e))
      (fun e => ti e + (tf e + 1) + ⌜(i e, f e)⌝ₜ.size ^ 2 + 1)
      (fun e => max (pi e) (max (pf e) ⌜(i e, f e)⌝ₜ.size)) := by
  let ht : Implementation (fun e => List.ofFn (fun i => ⌜f e i⌝ₜ)) tf pf :=
    .ofEncode (fun e => (encode_fin_function_codes _).trans (Tree.encode_self _).symm) hf
  refine ((((hi.pair ht).comp implementationLookup).ofSome (by intro e; simp)).ofEncode
    (fun e => (Tree.encode_self _).symm)).mono ?_ ?_
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

/-- A one-element list of an encoded value. -/
def implementationSingleton : Implementation (fun t : Tree => [t]) (fun _ => 1)
    (fun t => ⌜t⌝ₜ.size) := by
  source_fun_prop
  all_goals dominated

@[uniform_program] def _root_.List.implementationTail {α : Type*} [UniqueEncoding Tree α] :
    Implementation (List.tail : List α → List α) (fun _ => 1) (fun xs => ⌜xs⌝ₜ.size) := by
  source_fun_prop
  all_goals dominated

attribute [scoped fun_prop] List.implementationTail

section Index

/-! Operations on indices; an index is stored as its value. -/

variable {ρ : Type*} [UniqueEncoding Tree ρ] {k m : ρ → ℕ} {i : (e : ρ) → Fin (k e)}
  {t p : ρ → ℕ}

/-- The last index is stored as its value. -/
def Implementation.finLast (hk : Implementation k t p) :
    Implementation (fun e => Fin.last (k e)) t p :=
  hk.ofEncode fun _ => by rw [encode_fin, Fin.val_last]

/-- Casting an index up keeps its value. -/
def Implementation.finCastSucc (hi : Implementation i t p) :
    Implementation (fun e => (i e).castSucc) t p :=
  .ofEncode (f := fun e => (i e).castSucc) (g := i) (fun _ => rfl) hi

/-- Casting an index into a longer range keeps its value. -/
def Implementation.finCastAdd (hi : Implementation i t p) :
    Implementation (fun e => Fin.castAdd (m e) (i e)) t p :=
  .ofEncode (f := fun e => Fin.castAdd (m e) (i e)) (g := i) (fun _ => rfl) hi

/-- Shifting an index is an addition of its value. -/
def Implementation.finNatAdd (h : Implementation (fun e => m e + (i e).val) t p) :
    Implementation (fun e => Fin.natAdd (m e) (i e)) t p :=
  .ofEncode (f := fun e => Fin.natAdd (m e) (i e)) (g := fun e => m e + (i e).val)
    (fun _ => rfl) h

/-- The value of an index is stored as the index. -/
def Implementation.finVal (hi : Implementation i t p) :
    Implementation (fun e => (i e).val) t p :=
  .ofEncode (f := fun e => (i e).val) (g := i) (fun _ => rfl) hi

/-- The next index is a successor of the value. -/
def Implementation.finSucc (h : Implementation (fun e => (i e).val + 1) t p) :
    Implementation (fun e => (i e).succ) t p :=
  .ofEncode (f := fun e => (i e).succ) (g := fun e => (i e).val + 1) (fun _ => rfl) h

/-- The first index of a nonempty range is stored as zero, the empty tree. -/
def Implementation.finZero :
    Implementation (fun e => (0 : Fin (k e + 1))) (fun _ => 0) (fun _ => 0) :=
  .ofEncode (f := fun e => (0 : Fin (k e + 1))) (g := fun _ => ())
    (fun e => by rw [encode_fin, encode_unit]; simp; rfl) Implementation.unit

attribute [scoped fun_prop] Implementation.finVal Implementation.finSucc Implementation.finZero
  Implementation.finCastSucc Implementation.finCastAdd Implementation.finNatAdd
  Implementation.finLast

end Index

/-- Extend a represented table without re-enumerating its indices. -/
def Implementation.finSnoc {ρ : Type*} {α : ρ → Type*}
    [UniqueEncoding Tree ρ] [∀ e, UniqueEncoding Tree (α e)]
    {n : ρ → ℕ} {f : (e : ρ) → Fin (n e) → α e} {a : (e : ρ) → α e} {tf pf ta pa : ρ → ℕ}
    (hf : Implementation (fun e => ⌜f e⌝ₜ) tf pf) (ha : Implementation a ta pa) :
    Implementation (fun e => ⌜Fin.snoc (α := fun _ => α e) (f e) (a e)⌝ₜ)
      (fun e => tf e + ta e + n e + 1)
      (fun e => max (pf e) (max (pa e) (⌜f e⌝ₜ.size + ⌜a e⌝ₜ.size))) := by
  let ht : Implementation (fun e => List.ofFn (fun i => ⌜f e i⌝ₜ)) tf pf :=
    .ofEncode (fun e => (encode_fin_function_codes _).trans (Tree.encode_self _).symm) hf
  let hc : Implementation (fun e => ⌜a e⌝ₜ) ta pa := ha.ofEncode fun e => Tree.encode_self _
  refine (Implementation.ofEncode ?_ (ht.append (hc.comp implementationSingleton))).mono ?_ ?_
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

/-- Casting the entries of a table of indices up keeps its code. -/
def Implementation.finCastSuccComp {ρ : Type*} [UniqueEncoding Tree ρ] {n k : ρ → ℕ}
    {f : (e : ρ) → Fin (n e) → Fin (k e)} {t p : ρ → ℕ}
    (hf : Implementation (fun e => ⌜f e⌝ₜ) t p) :
    Implementation (fun e => ⌜Fin.castSucc ∘ f e⌝ₜ) t p :=
  hf.ofEncode fun e => by rw [Tree.encode_self, Tree.encode_self, encode_fin_castSucc]

/-- Erasing the bounds of a table of indices keeps its code. -/
def Implementation.finValComp {ρ : Type*} [UniqueEncoding Tree ρ] {n k : ρ → ℕ}
    {f : (e : ρ) → Fin (n e) → Fin (k e)} {t p : ρ → ℕ}
    (hf : Implementation (fun e => ⌜f e⌝ₜ) t p) :
    Implementation (fun e => ⌜Fin.val ∘ f e⌝ₜ) t p :=
  hf.ofEncode fun e => by
    rw [Tree.encode_self, Tree.encode_self]
    exact encode_fin_function_congr _ _ fun _ => rfl

-- Known operations reuse their certificates before unfolding.
attribute [scoped fun_prop] Implementation.finSnoc Implementation.finAppend
  Implementation.finCastSuccComp Implementation.finValComp

abbrev FinCompInput := Σ n, Σ k, Σ m, (Fin n → Fin k) × (Fin k → Fin m)

def implementationFinCompCount :
    Implementation (fun x : FinCompInput => x.1) (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  all_goals dominated

def implementationFinCompStep :
    Implementation (fun z : Σ x : FinCompInput, Fin x.1 => z.1.2.2.2.2 (z.1.2.2.2.1 z.2))
      (fun z => ⌜z.1⌝ₜ.size ^ 2) (fun z => ⌜z.1⌝ₜ.size ^ 2) := by
  source_fun_prop
  all_goals dominated

/-- Stored table composition directly enumerates its selected lookup callback. -/
def implementationFinComp : Implementation (fun x : FinCompInput => ⌜x.2.2.2.2 ∘ x.2.2.2.1⌝ₜ)
    (fun x => ⌜x⌝ₜ.size ^ 3) (fun x => ⌜x⌝ₜ.size ^ 2) := by
  refine (Implementation.finFunction (β := fun x : FinCompInput => Fin x.2.2.1)
    (instβ := fun _ => inferInstance) (n := fun x => x.1) (f := fun x => x.2.2.2.2 ∘ x.2.2.2.1)
    implementationFinCompCount implementationFinCompStep).mono ?_ ?_
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
  h.comp implementationFinComp

end Complexity.TreeProgram.Source
