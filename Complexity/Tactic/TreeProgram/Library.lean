/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Tactic.TreeProgram.Iteration

/-! # Source specifications for binary arithmetic and finite tables -/

@[expose] public section

open Complexity TreeProgram

namespace Complexity.TreeProgram.Source

private def lookupContinues {α : Type*} (x : ℕ × List α) : Bool :=
  match x.2 with | [] => false | _ :: _ => !x.1.bits.isEmpty

private def lookupStep {α : Type*} (x : ℕ × List α) := (x.1.pred, x.2.tail)

private theorem lookupContinues_realizes {α : Type*} [UniqueEncoding Tree α] :
    Realizes (lookupContinues (α := α)) ⟨fun _ => 20, fun x => 2 * ⌜x⌝ₜ.size + 5⟩ := by
  refine Realizes.mono (by source_fun_prop) ?_
  rintro ⟨n, xs⟩
  cases xs <;> cases h : n.bits <;> simp [h] <;> omega

private theorem lookupStep_realizes {α : Type*} [UniqueEncoding Tree α] :
    Realizes (lookupStep (α := α))
      ⟨fun x => 100 * ⌜x.1⌝ₜ.size + 410, fun x => 20 * ⌜x⌝ₜ.size + 50⟩ := by
  refine Realizes.mono (by source_fun_prop) ?_
  rintro ⟨n, xs⟩
  have hp := pred_realizes.size_le n
  cases xs <;> simp at * <;> omega

private theorem lookupFinish_realizes {α : Type*} [UniqueEncoding Tree α] :
    Realizes (fun x : ℕ × List α => x.2.head?)
      ⟨fun _ => 5, fun x => ⌜x⌝ₜ.size + 2⟩ := by
  source_cases

/-- A quadratic time and linear space allowance for indexed list lookup. -/
@[simps] def lookupBounds {α : Type*} [UniqueEncoding Tree α] : Bounds (ℕ × List α) :=
  ⟨fun x => 4000 * ⌜x⌝ₜ.size ^ 2, fun x => 100 * ⌜x⌝ₜ.size + 100⟩

theorem getElem?_realizes {α : Type*} [UniqueEncoding Tree α] :
    Realizes (fun x : ℕ × List α => x.2[x.1]?) lookupBounds := by
  let I (x y : ℕ × List α) :=
    y.1.bits.length ≤ x.1.bits.length ∧ ⌜y.2⌝ₜ.size ≤ ⌜x.2⌝ₜ.size ∧ y.2[y.1]? = x.2[x.1]?
  have sizeBound (x y) (h : I x y) : ⌜y⌝ₜ.size ≤ 4 * ⌜x⌝ₜ.size + 2 := by
    rcases x with ⟨n, xs⟩; rcases y with ⟨m, ys⟩
    have hbits : ⌜m⌝ₜ.size ≤ 4 * m.bits.length + 1 := Tree.size_encodeBitList_le _
    have hn := length_le_codeSize n.bits
    simp only [size_encode_prod, encode_nat_tree, I] at *
    omega
  apply (Realizes.loop lookupContinues_realizes lookupStep_realizes lookupFinish_realizes
    (fun x => x.2.length) I (fun x => 400 * ⌜x⌝ₜ.size + 610) (fun _ => 5)
    (fun x => 100 * ⌜x⌝ₜ.size + 100) ?_ ?_ ?_ ?_ ?_).mono
  · rintro ⟨n, xs⟩
    have hlen := length_le_codeSize xs
    have hn := Tree.size_pos ⌜(n, xs)⌝ₜ
    have hN : xs.length ≤ ⌜(n, xs)⌝ₜ.size := by simp; omega
    dsimp only [lookupBounds]
    constructor
    · nlinarith [Nat.mul_le_mul_left (800 * ⌜(n, xs)⌝ₜ.size + 1226) hN]
    · exact le_rfl
  · intro x; exact ⟨le_rfl, le_rfl, rfl⟩
  · intro x y hi; have := sizeBound x y hi; omega
  · intro x y hi; have := sizeBound x y hi; dsimp only; constructor <;> omega
  · rintro x ⟨m, ys⟩ hi ht
    cases ys with
    | nil => simp [lookupContinues] at ht
    | cons a ys =>
      have hm : m ≠ 0 := by intro hm; subst m; simp [lookupContinues] at ht
      have hp : m.pred.bits.length ≤ m.bits.length := by
        simpa [Nat.pred_eq_sub_one] using BitList.length_decrement_le m.bits
      have hsize := sizeBound x (m, a :: ys) hi
      refine ⟨?_, by dsimp only; omega, ⟨hp.trans hi.1, ?_, ?_⟩, by simp [lookupStep]⟩
      · simp only [size_encode_prod] at hsize
        dsimp only; omega
      · have := hi.2.1
        simpa only [lookupStep, List.tail_cons] using
          (show ⌜ys⌝ₜ.size ≤ ⌜a :: ys⌝ₜ.size by simp).trans this
      · simpa [lookupStep, List.getElem?_cons, hm, Nat.pred_eq_sub_one] using hi.2.2
  · rintro x ⟨m, ys⟩ hi ht
    have hsize := sizeBound x (m, ys) hi
    refine ⟨le_rfl, by dsimp only; omega, ?_⟩
    cases ys with
    | nil => simpa using hi.2.2
    | cons a ys =>
      have hbits : m.bits = [] := by simpa [lookupContinues] using ht
      have hm : m = 0 := by simpa [hbits, BitList.toNat] using (BitList.toNat_bits m).symm
      simpa [hm] using hi.2.2

theorem Realizes.getElem? {α β : Type*}
    [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {f : α → List β} {i : α → ℕ} {b c : Bounds α}
    (hf : Realizes f b) (hi : Realizes i c) :
    Realizes (fun x => (f x)[i x]?)
      (compBounds (fun x => (i x, f x)) (pairBounds i f c b) lookupBounds) :=
  (hi.pair hf).comp getElem?_realizes

attribute [scoped fun_prop] Realizes.getElem?

-- The lookup backend remains an existential proof in this migration slice; select its
-- program once at this declaration boundary, before composing caller implementations.
@[source_bounds↓] noncomputable def Implementation.lookup {α : Type*}
    [UniqueEncoding Tree α] : Implementation (fun x : ℕ × List α => x.2[x.1]?) :=
  getElem?_realizes.implementation

@[source_bounds↓] noncomputable def Implementation.getElem? {α β : Type*}
    [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {f : α → List β} {i : α → ℕ} (hf : Implementation f) (hi : Implementation i) :
    Implementation (fun x => (f x)[i x]?) := (hi.pair hf).comp Implementation.lookup

attribute [scoped fun_prop] Implementation.getElem?

@[scoped fun_prop] theorem encode_realizes {α : Type*} [UniqueEncoding Tree α] :
    Realizes (encode Tree : α → Tree) identityBounds := by
  apply Realizes.of_encode (g := id) (hg := identity_realizes)
  intro x; rfl

@[source_bounds↓] def Implementation.encodeTree {α : Type*} [UniqueEncoding Tree α] :
    Implementation (encode Tree : α → Tree) :=
  .ofEncode (g := id) (fun _ => rfl) Implementation.identity

attribute [scoped fun_prop] Implementation.encodeTree

/-- Reading a represented finite table reuses its code; constructing the table is a premise. -/
theorem Realizes.ofFn {α β : Type*}
    [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {n : α → ℕ} {f : (x : α) → Fin (n x) → β} {b : Bounds α}
    (hf : Realizes (fun x => ⌜f x⌝ₜ) b) : Realizes (fun x => List.ofFn (f x)) b := by
  exact Realizes.of_encode (fun _ => rfl) hf

attribute [scoped fun_prop] Realizes.ofFn

@[source_bounds↓] def Implementation.ofFn {α β : Type*}
    [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {n : α → ℕ} {f : (x : α) → Fin (n x) → β}
    (hf : Implementation (fun x => ⌜f x⌝ₜ)) : Implementation (fun x => List.ofFn (f x)) :=
  .ofEncode (g := fun x => ⌜f x⌝ₜ) (fun _ => rfl) hf

attribute [scoped fun_prop] Implementation.ofFn

/-- A successful optional computation supplies a total implementation without a default value. -/
theorem Realizes.of_some {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {f : α → β} {g : α → Option β} {b : Bounds α}
    (hfg : ∀ x, g x = some (f x)) (hg : Realizes g b) :
    Realizes f ⟨fun x => b.time x + 4, fun x => max ⌜x⌝ₜ.size (b.peak x)⟩ := by
  have hc : Realizes (fun x : Option β => match x with | none => (.nil : Tree) | some a => ⌜a⌝ₜ)
      ⟨fun _ => 4, fun x => ⌜x⌝ₜ.size⟩ := by
    refine Realizes.mono (by source_fun_prop) ?_
    intro x; cases x <;> simp
  apply Realizes.of_encode (g := fun x => match g x with | none => (.nil : Tree) | some a => ⌜a⌝ₜ)
  · intro x; simp [hfg]
  · apply (hg.comp hc).mono
    intro x
    have := hg.size_le x
    exact ⟨le_rfl, by dsimp only [compBounds]; omega⟩

@[scoped fun_prop] theorem finApply_realizes {α : Type*} [UniqueEncoding Tree α] :
    Realizes (fun x : Σ n, (Fin n → α) × Fin n => x.2.1 x.2.2)
      ⟨fun x => 4000 * ⌜x⌝ₜ.size ^ 2 + 20, fun x => 100 * ⌜x⌝ₜ.size + 100⟩ := by
  apply (Realizes.of_some (g := fun x => (List.ofFn x.2.1)[x.2.2.val]?)
    (by rintro ⟨n, f, i⟩; simp) (by source_fun_prop)).mono
  rintro ⟨n, f, i⟩
  have hsize : ⌜(i.val, List.ofFn f)⌝ₜ.size ≤ ⌜(⟨n, f, i⟩ : Σ n, (Fin n → α) × Fin n)⌝ₜ.size := by
    simp; omega
  have hpow := pow_le_pow_left' hsize 2
  simp only [size_encode_prod, UniqueEncoding.ofLeftInjection_encode, Sigma.encode_mk,
    encode_fin, UniqueEncoding.refl_encode, id_eq, compBounds_time, pairBounds_time,
    Nat.reduceAdd, lookupBounds_time, add_le_add_iff_right, compBounds_peak, pairBounds_peak,
    Nat.max_assoc, le_add_iff_nonneg_left, zero_le, sup_of_le_right, le_max_iff, Std.le_refl,
    true_or, or_true, lookupBounds_peak, sup_le_iff, Nat.ofNat_pos,
    mul_le_mul_iff_right₀] at hpow ⊢
  (repeat' apply And.intro) <;> nlinarith

theorem finApply_ftisp {α : Type*} [UniqueEncoding Tree α] :
    (fun x : Σ n, (Fin n → α) × Fin n => x.2.1 x.2.2) ∈
      FTISP .tree (fun n => n ^ 2) (fun n => n) := by
  obtain ⟨k, hk⟩ := (finApply_realizes (α := α)).computableInTimeAndSpace
    (time := fun n => 4000 * n ^ 2 + 24) (space := fun n => 100 * n + 102)
    (by intro x; simp; omega)
  refine ⟨_, _, hk, IsBigO.iff_exists_nat.mpr ⟨4024, 1, ?_⟩,
    IsBigO.iff_exists_nat.mpr ⟨202 * k, 1, ?_⟩⟩
  · intro n hn; nlinarith
  · intro n hn; nlinarith

@[scoped fun_prop] theorem finApply_fixed_realizes {α : Type*} [UniqueEncoding Tree α] (n : ℕ) :
    Realizes (fun x : (Fin n → α) × Fin n => x.1 x.2)
      ⟨fun x => 4000 * ⌜x⌝ₜ.size ^ 2 + 20, fun x => 100 * ⌜x⌝ₜ.size + 100⟩ := by
  apply (Realizes.of_some (g := fun x => (List.ofFn x.1)[x.2.val]?)
    (by rintro ⟨f, i⟩; simp) (by source_fun_prop)).mono
  rintro ⟨f, i⟩
  simp only [UniqueEncoding.ofLeftInjection_encode, compBounds_time, pairBounds_time,
    projectionBounds_time, add_zero, Nat.reduceAdd, lookupBounds_time,
    size_encode_prod, encode_fin, add_le_add_iff_right, compBounds_peak, pairBounds_peak,
    le_add_iff_nonneg_left, zero_le, sup_of_le_left, projectionBounds_peak,
    le_max_iff, Std.le_refl, true_or, sup_of_le_right, lookupBounds_peak, Nat.max_assoc,
    sup_le_iff, Nat.ofNat_pos, mul_le_mul_iff_right₀]
  (repeat' apply And.intro) <;> nlinarith

@[scoped fun_prop] theorem finValApply_realizes :
    Realizes (fun x : Σ n, Σ k, (Fin n → Fin k) × Fin n => (x.2.2.1 x.2.2.2).val)
      ⟨fun x => 4000 * ⌜x⌝ₜ.size ^ 2 + 20, fun x => 100 * ⌜x⌝ₜ.size + 100⟩ := by
  apply (Realizes.of_some (g := fun x => (List.ofFn (Fin.val ∘ x.2.2.1))[x.2.2.2.val]?)
    (by rintro ⟨n, k, f, i⟩; simp) (by source_fun_prop)).mono
  rintro ⟨n, k, f, i⟩
  have hsize : ⌜(i.val, List.ofFn (Fin.val ∘ f))⌝ₜ.size ≤
      ⌜(⟨n, k, f, i⟩ : Σ n, Σ k, (Fin n → Fin k) × Fin n)⌝ₜ.size := by
    simp; omega
  have hpow := pow_le_pow_left' hsize 2
  simp only [size_encode_prod, UniqueEncoding.ofLeftInjection_encode, encode_fin_values,
    Sigma.encode_mk, encode_fin, UniqueEncoding.refl_encode, id_eq, compBounds_time,
    pairBounds_time, Nat.reduceAdd, lookupBounds_time, add_le_add_iff_right, compBounds_peak,
    pairBounds_peak, Nat.max_assoc, le_add_iff_nonneg_left, zero_le, sup_of_le_right,
    le_max_iff, Std.le_refl, true_or, or_true, lookupBounds_peak, sup_le_iff, Nat.ofNat_pos,
    mul_le_mul_iff_right₀] at hpow ⊢
  (repeat' apply And.intro) <;> nlinarith


-- Saved compatibility leaves for finite application; callbacks remain implementations.
@[source_bounds↓] noncomputable def Implementation.finApply {α : Type*} [UniqueEncoding Tree α] :
    Implementation (fun x : Σ n, (Fin n → α) × Fin n => x.2.1 x.2.2) :=
  finApply_realizes.implementation

@[source_bounds↓] noncomputable def Implementation.finApplyFixed {α : Type*}
    [UniqueEncoding Tree α] (n : ℕ) : Implementation (fun x : (Fin n → α) × Fin n => x.1 x.2) :=
  (finApply_fixed_realizes n).implementation

@[source_bounds↓] noncomputable def Implementation.finValApplyPacked :
    Implementation (fun x : Σ n, Σ k, (Fin n → Fin k) × Fin n => (x.2.2.1 x.2.2.2).val) :=
  finValApply_realizes.implementation

attribute [scoped fun_prop] Implementation.finApply Implementation.finApplyFixed
  Implementation.finValApplyPacked

private def rangeContinues (x : ℕ × List ℕ) : Bool := !x.1.bits.isEmpty

private def rangeStep (x : ℕ × List ℕ) : ℕ × List ℕ :=
  let n := x.1.pred
  (n, n :: x.2)

private theorem rangeContinues_realizes :
    Realizes rangeContinues ⟨fun _ => 10, fun x => 2 * ⌜x⌝ₜ.size + 5⟩ := by
  refine Realizes.mono (by source_fun_prop) ?_
  rintro ⟨n, acc⟩
  cases h : n.bits <;> simp [h] <;> omega

private theorem rangeStep_realizes :
    Realizes rangeStep
      ⟨fun x => 300 * ⌜x.1⌝ₜ.size + 1300, fun x => 30 * ⌜x⌝ₜ.size + 150⟩ := by
  refine Realizes.mono (by source_fun_prop) ?_
  rintro ⟨n, acc⟩
  have h := pred_realizes.size_le n
  simp at *
  omega

private def rangeLoop (x : ℕ × List ℕ) := List.range x.1 ++ x.2

private theorem rangeLoop_realizes :
    Realizes rangeLoop
      ⟨fun x => 10000 * (x.1 + 1) ^ 2,
        fun x => 1000 * (x.1 + 1) ^ 2 + 100 * ⌜x.2⌝ₜ.size⟩ := by
  let I (x y : ℕ × List ℕ) := y.1 ≤ x.1 ∧ List.range y.1 ++ y.2 = List.range x.1 ++ x.2
  have sizeBound (x y) (h : I x y) :
      ⌜y⌝ₜ.size ≤ 10 * (x.1 + 1) ^ 2 + ⌜x.2⌝ₜ.size := by
    have hn := size_encode_nat_le y.1
    have hr := size_encode_range_le x.1
    have hx := size_encode_list_append (List.range x.1) x.2
    have hy := size_encode_list_append (List.range y.1) y.2
    have he := congrArg (fun z : List ℕ => ⌜z⌝ₜ.size) h.2
    have hp := Tree.size_pos ⌜List.range y.1⌝ₜ
    have hle := h.1
    rcases y with ⟨n, acc⟩
    simp only [size_encode_prod]
    nlinarith
  apply (Realizes.loop rangeContinues_realizes rangeStep_realizes snd_realizes
    Prod.fst I (fun x => 2000 * (x.1 + 1)) (fun _ => 1)
    (fun x => 1000 * (x.1 + 1) ^ 2 + 100 * ⌜x.2⌝ₜ.size) ?_ ?_ ?_ ?_ ?_).mono
  · intro x
    constructor <;> dsimp only
    · nlinarith
    · exact le_rfl
  · intro x; exact ⟨le_rfl, rfl⟩
  · intro x y hi; have := sizeBound x y hi; omega
  · intro x y hi
    have := sizeBound x y hi
    have : 0 < (x.1 + 1) ^ 2 := by positivity
    dsimp only
    constructor <;> omega
  · rintro x ⟨n, acc⟩ hi ht
    have hn : n ≠ 0 := by
      intro h; subst n; simp [rangeContinues] at ht
    have hs := sizeBound x (n, acc) hi
    have hcode := size_encode_nat_le n
    have hle := hi.1
    have : 0 < (x.1 + 1) ^ 2 := by positivity
    refine ⟨by dsimp only; nlinarith, by dsimp only; omega, ⟨?_, ?_⟩, ?_⟩
    · exact (Nat.pred_le n).trans hi.1
    · rcases Nat.exists_eq_succ_of_ne_zero hn with ⟨k, rfl⟩
      simpa [rangeStep, List.range_succ, List.append_assoc] using hi.2
    · simpa [rangeStep] using Nat.pred_lt hn
  · rintro x ⟨n, acc⟩ hi ht
    have hs := sizeBound x (n, acc) hi
    have hbits : n.bits = [] := by simpa [rangeContinues] using ht
    have hn : n = 0 := by simpa [hbits, BitList.toNat] using (BitList.toNat_bits n).symm
    refine ⟨le_rfl, by dsimp only [projectionBounds]; omega, ?_⟩
    simpa [hn, rangeLoop] using hi.2

/-- Enumeration costs depend on the numerical length, not its binary code size. -/
@[scoped fun_prop] theorem range_realizes :
    Realizes List.range ⟨fun n => 10000 * (n + 1) ^ 2 + 4,
      fun n => 1000 * (n + 1) ^ 2 + 100⟩ := by
  have h := rangeLoop_realizes
  let implementation := h.implementation
  apply Realizes.of_encode (g := fun n => rangeLoop (n, [])) (by simp [rangeLoop])
  refine Realizes.mono (by source_fun_prop) ?_
  intro n
  have hs : ⌜n⌝ₜ.size + 2 ≤ 1000 * (n + 1) ^ 2 + 100 := by
    nlinarith [size_encode_nat_le n]
  simp_all
  omega

@[source_bounds↓] noncomputable def Implementation.range : Implementation List.range :=
  range_realizes.implementation

attribute [scoped fun_prop] Implementation.range

/-- Count with the existing binary successor; this conservative bound needs no amortization. -/
def Implementation.length {α : Type*} [UniqueEncoding Tree α] :
    Implementation (List.length : List α → ℕ) := by
  let h : Implementation (fun xs : List α => xs.foldl (fun n _ => n + 1) 0) := by source_fun_prop
  refine (Implementation.ofEncode (by simp) h).rebudget
    ⟨fun xs => 1000 * (xs.length + 1) ^ 2, fun xs => 10 * ⌜xs⌝ₜ.size + 20⟩ ?_
  simp only [h, source_bounds]
  intro xs
  have hl := length_le_codeSize xs
  have hc := foldlCost_le (f := fun n (_ : α) => n + 1)
    (b := fun a x => ⟨1 + (28 * a.bits.length + 25), max ⌜(a, x)⌝ₜ.size (⌜a⌝ₜ.size + 5)⟩)
    (fun rest a => a + rest.length ≤ xs.length ∧ ⌜rest⌝ₜ.size ≤ ⌜xs⌝ₜ.size)
    (fun rest _ => (112 * xs.length + 54) * rest.length)
    (10 * ⌜xs⌝ₜ.size + 20) xs 0 ⟨by simp, le_rfl⟩ ?_ ?_
  · have ht : (112 * xs.length + 54) * xs.length + 13 * xs.length + 12 ≤
        1000 * (xs.length + 1) ^ 2 := by nlinarith
    simp_all
    omega
  · intro x rest a hi
    have ha := size_encode_nat_le a
    have hb := length_le_codeSize a.bits
    simp only [encode_list_cons, size_encode_prod, List.length_cons] at hi
    simp only [encode_nat_tree] at ha
    refine ⟨⟨by omega, by omega⟩, ?_, ?_, ?_⟩
    · simp only [List.length_cons]
      nlinarith
    · simp only [size_encode_prod, encode_nat_tree]; omega
    · simp only [size_encode_prod, encode_nat_tree, max_le_iff]; omega
  · intro a hi
    have ha := size_encode_nat_le a
    simp only [List.length_nil, Nat.add_zero] at hi
    omega

@[simp, source_bounds↓] theorem Implementation.bounds_length {α : Type*} [UniqueEncoding Tree α] :
    (Implementation.length (α := α)).bounds =
      ⟨fun xs => 1000 * (xs.length + 1) ^ 2, fun xs => 10 * ⌜xs⌝ₜ.size + 20⟩ := rfl

attribute [scoped fun_prop] Implementation.length

@[scoped fun_prop] theorem length_realizes {α : Type*} [UniqueEncoding Tree α] :
    Realizes (List.length : List α → ℕ)
      ⟨fun xs => 1000 * (xs.length + 1) ^ 2, fun xs => 10 * ⌜xs⌝ₜ.size + 20⟩ :=
  Implementation.length.realizes

private theorem enumerate_realizes {ρ : Type*} [UniqueEncoding Tree ρ]
    {n : ρ → ℕ} {b : Bounds ρ} (hn : Realizes n b) :
    Realizes (fun e => (⟨e, List.finRange (n e)⟩ : Σ e, List (Fin (n e))))
      (pairBounds id (fun e => List.range (n e)) identityBounds
        (compBounds n b ⟨fun n => 10000 * (n + 1) ^ 2 + 4,
          fun n => 1000 * (n + 1) ^ 2 + 100⟩)) := by
  apply Realizes.of_encode (g := fun e => (e, List.range (n e)))
  · intro e
    simp only [Sigma.encode_mk, encode_prod, encode_finRange]
  · exact identity_realizes.pair (hn.comp range_realizes)

/-- Enumerate indices, sum callback times, and retain the output and all intermediate peaks. -/
@[simps] def tabulateBounds {ρ : Type*} {β : ρ → Type*}
    [UniqueEncoding Tree ρ] [∀ e, UniqueEncoding Tree (β e)]
    (n : ρ → ℕ) (f : (e : ρ) → Fin (n e) → β e) (b : Bounds ρ)
    (c : Bounds (Σ e, Fin (n e))) : Bounds ρ :=
  let bi := pairBounds id (fun e => List.range (n e)) identityBounds
    (compBounds n b ⟨fun n => 10000 * (n + 1) ^ 2 + 4,
      fun n => 1000 * (n + 1) ^ 2 + 100⟩)
  ⟨fun e => bi.time e + ((List.finRange (n e)).map (fun i => c.time ⟨e, i⟩)).sum +
      27 * n e + 17,
    fun e => max (bi.peak e) (max ⌜(e, List.range (n e))⌝ₜ.size
      (max (⌜f e⌝ₜ.size + 1)
        ((List.finRange (n e)).foldr (fun i s => max (c.peak ⟨e, i⟩) s) 0)))⟩

/-- Construct a represented tuple using one callback program for every environment and index. -/
@[source_bounds↓] noncomputable def Implementation.finFunction {ρ : Type*} {β : ρ → Type*}
    [UniqueEncoding Tree ρ] [∀ e, UniqueEncoding Tree (β e)]
    {n : ρ → ℕ} {f : (e : ρ) → Fin (n e) → β e}
    (hn : Implementation n) (hf : Implementation (fun p : Σ e, Fin (n e) => ⌜f p.1 p.2⌝ₜ)) :
    Implementation (fun e => ⌜f e⌝ₜ) :=
  Realizes.implementation (b := tabulateBounds n f hn.bounds hf.bounds) <| by
    let hn := hn.realizes
    let hf := hf.realizes
    have he (e : ρ) := (encode_fin_function_codes (f e)).symm
    have hmap := (enumerate_realizes hn).mapDependentWith (f := fun e i => ⌜f e i⌝ₜ) hf
    simp only [← List.ofFn_eq_map] at hmap
    apply (Realizes.of_encode (g := fun e => List.ofFn (fun i => ⌜f e i⌝ₜ))
      (fun e => (Tree.encode_self _).trans (he e)) hmap).mono
    intro e
    have he' := he e
    rw [List.ofFn_eq_map] at he'
    simp only [tabulateBounds, mapDependentWithBounds, compBounds, mapDependentBounds,
      List.length_finRange, Sigma.encode_mk, encode_prod, encode_finRange, ← he']
    constructor
    · omega
    · exact le_rfl

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
@[simps] def finApplyBounds {ρ : Type*} {β : ρ → Type*}
    [UniqueEncoding Tree ρ] [∀ e, UniqueEncoding Tree (β e)]
    {n : ρ → ℕ} (f : (e : ρ) → Fin (n e) → β e) (i : (e : ρ) → Fin (n e))
    (bf bi : Bounds ρ) : Bounds ρ :=
  let size x := 1 + ⌜(i x).val⌝ₜ.size + ⌜f x⌝ₜ.size
  ⟨fun x => bi.time x + bf.time x + 4000 * size x ^ 2 + 5,
    fun x => max ⌜x⌝ₜ.size (max (max (bi.peak x) (bf.peak x)) (100 * size x + 100))⟩

@[source_bounds↓] noncomputable def Implementation.finApplyEncoded {ρ : Type*} {β : ρ → Type*}
    [UniqueEncoding Tree ρ] [∀ e, UniqueEncoding Tree (β e)]
    {n : ρ → ℕ} {f : (e : ρ) → Fin (n e) → β e} {i : (e : ρ) → Fin (n e)}
    (hf : Implementation (fun e => ⌜f e⌝ₜ)) (hi : Implementation (fun e => (i e).val)) :
    Implementation (fun e => ⌜f e (i e)⌝ₜ) :=
  Realizes.implementation (b := finApplyBounds f i hf.bounds hi.bounds) <| by
    let bf := hf.bounds
    let hf := hf.realizes
    let hi := hi.realizes
    have he (e : ρ) := encode_fin_function_codes (f e)
    have ht : Realizes (fun e => List.ofFn (fun i => ⌜f e i⌝ₜ)) bf :=
      .of_encode (fun e => (he e).trans (Tree.encode_self _).symm) hf
    apply (Realizes.of_some (g := fun e =>
      (List.ofFn (fun i => ⌜f e i⌝ₜ))[(i e).val]?) (by intro e; simp)
        ((hi.pair ht).comp getElem?_realizes)).mono
    intro e
    simp only [finApplyBounds, compBounds, pairBounds, lookupBounds, size_encode_prod, he, bf]
    constructor <;> omega

@[source_bounds↓] noncomputable def Implementation.finValApply {ρ : Type*} [UniqueEncoding Tree ρ]
    {n k : ρ → ℕ} {f : (e : ρ) → Fin (n e) → Fin (k e)} {i : (e : ρ) → Fin (n e)}
    (hf : Implementation (fun e => ⌜f e⌝ₜ)) (hi : Implementation (fun e => (i e).val)) :
    Implementation (fun e => (f e (i e)).val) :=
  .ofEncode (fun _ => (encode_fin _).symm.trans (Tree.encode_self _).symm)
    (Implementation.finApplyEncoded hf hi)

/-- Extend a represented table by appending one element, without re-enumerating its indices. -/
@[source_bounds↓] noncomputable def Implementation.finSnoc {ρ : Type*} {α : ρ → Type*}
    [UniqueEncoding Tree ρ] [∀ e, UniqueEncoding Tree (α e)]
    {n : ρ → ℕ} {f : (e : ρ) → Fin (n e) → α e} {a : (e : ρ) → α e}
    (hf : Implementation (fun e => ⌜f e⌝ₜ)) (ha : Implementation (fun e => ⌜a e⌝ₜ)) :
    Implementation (fun e => ⌜Fin.snoc (α := fun _ => α e) (f e) (a e)⌝ₜ) :=
  Realizes.implementation (b :=
    ⟨fun e => hf.bounds.time e + ha.bounds.time e + 26 * n e + 18,
     fun e => max (hf.bounds.peak e)
       (max (ha.bounds.peak e) (⌜f e⌝ₜ.size + ⌜a e⌝ₜ.size + 2))⟩) <| by
    let b := hf.bounds
    let hf := hf.realizes
    let ha := ha.realizes
    have hview : Realizes (fun e => List.ofFn (fun i => ⌜f e i⌝ₜ)) b :=
      .of_encode (fun e => (encode_fin_function_codes _).trans (Tree.encode_self _).symm) hf
    have hs : Realizes (fun t : Tree => [t])
        ⟨fun _ => 2, fun t => t.size + 2⟩ := by source_cases
    have hsingle := ha.comp hs
    apply (Realizes.of_encode (g := fun e => List.ofFn (fun i => ⌜f e i⌝ₜ) ++ [⌜a e⌝ₜ])
      ?_ (hview.append hsingle)).mono
    · intro e
      simp only [appendBounds, compBounds, encode_fin_function_codes, List.length_ofFn, b]
      simp
      omega
    · intro e
      rw [Tree.encode_self, encode_fin_snoc]
      simpa only [List.map_append, List.map_cons, List.map_nil, List.map_ofFn,
        Function.comp_def] using
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
  refine (Implementation.ofEncode
    (g := fun e => List.ofFn (fun i => ⌜f e i⌝ₜ) ++ List.ofFn (fun i => ⌜g e i⌝ₜ))
    ?_ (hf'.append hg')).rebudget
      ⟨fun e => hf.bounds.time e + hg.bounds.time e + 26 * n e + 16,
       fun e => max (hf.bounds.peak e) (max (hg.bounds.peak e) (⌜f e⌝ₜ.size + ⌜g e⌝ₜ.size))⟩ ?_
  · intro e
    rw [Tree.encode_self, encode_fin_function, List.ofFn_fin_append]
    simpa only [List.map_append, List.map_ofFn, Function.comp_def] using
      (encode_list_map_of_encode (encode Tree) (fun _ => Tree.encode_self _)
        (List.ofFn (f e) ++ List.ofFn (g e))).symm
  · intro e
    simp (config := { implicitDefEqProofs := false }) only
      [hf', hg', Implementation.bounds_ofEncode, Implementation.bounds_append,
       appendBounds, encode_fin_function_codes, List.length_ofFn]
    exact ⟨by omega, le_rfl⟩

-- Known operations reuse their certificates before unfolding. General lookup remains a
-- fallback after stored-field extraction; new tables still require explicit guidance.
attribute [scoped fun_prop] Implementation.finSnoc Implementation.finAppend
attribute [scoped source_fallback] Implementation.finApplyEncoded Implementation.finValApply

open Lean Meta Mathlib.Meta.FunProp in
run_elab do
  addTheorem ``Implementation.finApplyEncoded .scoped 100
  addTheorem ``Implementation.finValApply .scoped 100

/-- A stored table composition is cubic in time and quadratic in intermediate-tree size. -/
private theorem finComp_realizes :
    Realizes (fun x : Σ n, Σ k, Σ m, (Fin n → Fin k) × (Fin k → Fin m) =>
      ⌜x.2.2.2.2 ∘ x.2.2.2.1⌝ₜ)
      ⟨fun x => 500000 * (⌜x⌝ₜ.size + 1) ^ 3,
       fun x => 500000 * (⌜x⌝ₜ.size + 1) ^ 2⟩ := by
  refine Realizes.mono (by source_fun_prop using tabulate) ?_
  intro input
  constructor
  all_goals
    rcases input with ⟨n, k, m, f, g⟩
    let N := ⌜(n, k, m, f, g)⌝ₜ.size
    dsimp only
    change _ ≤ 500000 * (N + 1) ^ _
    have hf : ⌜f⌝ₜ.size ≤ N := by simp [N]; omega
    have hg : ⌜g⌝ₜ.size ≤ N := by simp [N]; omega
    have hn : n ≤ N := (card_le_size_encode_fin_function f).trans hf
    have hp := pow_le_pow_left' (Nat.add_le_add_right hn 1) 2
    have hN := Nat.le_self_pow (by decide : 2 ≠ 0) (N + 1)
    have hi (i : Fin n) : ⌜i.val⌝ₜ.size ≤ 4 * N + 1 := by
      have := size_encode_nat_le i.val
      have := i.isLt
      omega
    have hfi (i : Fin n) : ⌜(f i).val⌝ₜ.size ≤ N :=
      (size_encode_fin_apply_le f i).trans hf
  · have sumBound (a : Fin n → ℕ) (ha : ∀ i, a i ≤ 4 * N + 1) (b : ℕ) (hb : b ≤ N) :
        ((List.finRange n).map (fun i => 4000 * (1 + a i + b) ^ 2)).sum ≤
          144000 * (N + 1) ^ 3 := by
      have hsum := List.sum_le_sum (l := List.finRange n) (g := fun _ => 144000 * (N + 1) ^ 2)
        (fun i _ => show 4000 * (1 + a i + b) ^ 2 ≤ 144000 * (N + 1) ^ 2 from by
          have hs : 1 + a i + b ≤ 6 * (N + 1) := by have := ha i; omega
          nlinarith [pow_le_pow_left' hs 2])
      simp only [List.map_const', List.sum_replicate, List.length_finRange, smul_eq_mul] at hsum
      nlinarith [Nat.mul_le_mul_right ((N + 1) ^ 2) hn]
    have h₁ := sumBound (fun i => ⌜i.val⌝ₜ.size) hi ⌜f⌝ₜ.size hf
    have h₂ := sumBound (fun i => ⌜(f i).val⌝ₜ.size)
      (fun i => by have := hfi i; omega) ⌜g⌝ₜ.size hg
    have hpow : (N + 1) ^ 2 ≤ (N + 1) ^ 3 :=
      Nat.pow_le_pow_right (by omega) (by decide)
    simp only [encode_nat_tree, encode_fin_function] at h₁ h₂
    simp only [pairBounds, compBounds, tabulateBounds, finApplyBounds, identityBounds]
    simp
    omega
  · have hout := size_encode_fin_function_le (g ∘ f) N
      (fun i => (size_encode_fin_apply_le g (f i)).trans hg)
    have hr := size_encode_range_le n
    have hncode : ⌜n⌝ₜ.size ≤ N := by simp [N]; omega
    have hmcode : ⌜m⌝ₜ.size ≤ N := by simp [N]; omega
    have hout' : ⌜g ∘ f⌝ₜ.size ≤ (N + 1) ^ 2 := by
      nlinarith [Nat.mul_le_mul_right (N + 1) hn]
    have hx :
        ⌜(⟨n, k, m, f, g⟩ : Σ n, Σ k, Σ m, (Fin n → Fin k) × (Fin k → Fin m))⌝ₜ.size = N := by
      simp [N]
    simp only [encode_nat_tree, encode_fin_function] at hf hg hncode hmcode hout' hi hfi
    simp only [pairBounds, compBounds, tabulateBounds, finApplyBounds, identityBounds,
      Sigma.encode_mk, size_encode_prod, Tree.encode_self, encode_fin, encode_nat_tree,
      encode_fin_function, id_eq]
    simp only [Sigma.encode_mk, size_encode_prod, encode_nat_tree, encode_fin_function] at hx
    simp only [← hx] at *
    simp only [← max_assoc, max_le_iff, foldr_max_le]
    (repeat' apply And.intro) <;> try omega
    intro i _
    have := hi i
    have := hfi i
    omega

/-- Reuse the existing table-composition backend while retaining the caller's program. -/
@[source_bounds↓] noncomputable def Implementation.finComp {ρ : Type*} [UniqueEncoding Tree ρ]
    {n k m : ρ → ℕ} {f : (e : ρ) → Fin (n e) → Fin (k e)}
    {g : (e : ρ) → Fin (k e) → Fin (m e)}
    (h : Implementation (fun e => (⟨n e, k e, m e, f e, g e⟩ :
      Σ n, Σ k, Σ m, (Fin n → Fin k) × (Fin k → Fin m)))) :
    Implementation (fun e => ⌜g e ∘ f e⌝ₜ) :=
  h.comp (Realizes.implementation
    (f := fun x : Σ n, Σ k, Σ m, (Fin n → Fin k) × (Fin k → Fin m) =>
      ⌜x.2.2.2.2 ∘ x.2.2.2.1⌝ₜ)
    (b := ⟨fun x => 500000 * (⌜x⌝ₜ.size + 1) ^ 3,
      fun x => 500000 * (⌜x⌝ₜ.size + 1) ^ 2⟩)
    (by exact finComp_realizes))

end Complexity.TreeProgram.Source
