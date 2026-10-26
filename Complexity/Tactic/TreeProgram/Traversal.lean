/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Tactic.TreeProgram.Implementation
public import Complexity.Models.TreeMachine.Language.List

/-! # Certified list folds

`foldlTime` and `foldlPeak` follow the source fold: callback costs are charged at the actual
intermediate accumulators, and every stored state contributes to the peak.
-/

@[expose] public section

open Complexity TreeProgram TreeProgram.Code
namespace Complexity.TreeProgram.Source

section Cost

variable {α β : Type*} (f : β → α → β)

/-- Callback time along a source fold, at the actual intermediate accumulators. -/
def foldlTime (t : β × α → ℕ) : β → List α → ℕ
  | _, [] => 0
  | a, x :: xs => t (a, x) + foldlTime t (f a x) xs

variable {f} in
@[simp] theorem foldlTime_nil (t : β × α → ℕ) (a : β) : foldlTime f t a [] = 0 := rfl

variable {f} in
@[simp] theorem foldlTime_cons (t : β × α → ℕ) (a : β) (x : α) (xs : List α) :
    foldlTime f t a (x :: xs) = t (a, x) + foldlTime f t (f a x) xs := rfl

variable {f} in
/-- Accumulator-independent callback times add once per element. -/
@[simp] theorem foldlTime_eq_sum (t : α → ℕ) (a : β) (xs : List α) :
    foldlTime f (fun z => t z.2) a xs = (xs.map t).sum := by
  induction xs generalizing a <;> simp [*]

variable {f} in
/-- A constant callback time is charged once per element. -/
@[simp, dominated_simp] theorem foldlTime_const (c : ℕ) (a : β) (xs : List α) :
    foldlTime f (fun _ => c) a xs = xs.length * c := by
  induction xs generalizing a <;> simp [*, Nat.succ_mul, Nat.add_comm]

variable {f} in
/-- Callback times bounded by their current elements add at most once per element. -/
theorem foldlTime_le_sum {t : β × α → ℕ} (u : α → ℕ) (h : ∀ z, t z ≤ u z.2) (a : β)
    (xs : List α) : foldlTime f t a xs ≤ (xs.map u).sum := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih => simpa using Nat.add_le_add (h (a, x)) (ih (f a x))

variable {f} in
/-- One coefficient for the callback family bounds the whole fold. -/
theorem _root_.Complexity.Dominated.foldlTime {t u : β × α → ℕ} (h : Dominated t u) :
    Dominated (fun x : β × List α => foldlTime f t x.1 x.2)
      (fun x => foldlTime f u x.1 x.2) := by
  obtain ⟨C, hC⟩ := dominated_iff.mp h
  refine Dominated.of_le_mul C fun ⟨a, xs⟩ => ?_
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    have := hC (a, x)
    have := ih (f a x)
    simp only [smul_eq_mul, foldlTime_cons, Nat.mul_add] at *
    omega

variable {f} in
/-- A unit charge per callback adds the list length. -/
theorem foldlTime_add_one (t : β × α → ℕ) (a : β) (xs : List α) :
    foldlTime f (fun z => t z + 1) a xs = foldlTime f t a xs + xs.length := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => simp only [foldlTime_cons, ih, List.length_cons]; omega

/-- A fold whose state also carries a fixed environment charges the same callbacks. -/
theorem foldlTime_lift {ρ : Type*} (g : ρ → β → α → β) (t : (ρ × β) × α → ℕ) (e : ρ) (a : β)
    (xs : List α) :
    foldlTime (fun (ea : ρ × β) x => (ea.1, g ea.1 ea.2 x)) t (e, a) xs =
      foldlTime (g e) (fun z => t ((e, z.1), z.2)) a xs := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => simp only [foldlTime_cons, ih]

variable [UniqueEncoding Tree α] [UniqueEncoding Tree β]

/-- The largest stored state or callback peak along a source fold. -/
def foldlPeak (p : β × α → ℕ) : β → List α → ℕ
  | a, [] => ⌜a⌝ₜ.size
  | a, x :: xs => max ⌜(a, x)⌝ₜ.size (max (p (a, x)) (foldlPeak p (f a x) xs))

variable {f}

@[simp] theorem foldlPeak_nil (p : β × α → ℕ) (a : β) : foldlPeak f p a [] = ⌜a⌝ₜ.size := rfl

@[simp] theorem foldlPeak_cons (p : β × α → ℕ) (a : β) (x : α) (xs : List α) :
    foldlPeak f p a (x :: xs) =
      max ⌜(a, x)⌝ₜ.size (max (p (a, x)) (foldlPeak f p (f a x) xs)) := rfl

theorem size_le_foldlPeak (p : β × α → ℕ) (a : β) (xs : List α) :
    ⌜a⌝ₜ.size ≤ foldlPeak f p a xs := by
  cases xs <;> simp
  omega

theorem size_foldl_le_foldlPeak (p : β × α → ℕ) (a : β) (xs : List α) :
    ⌜xs.foldl f a⌝ₜ.size ≤ foldlPeak f p a xs := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih => exact (ih (f a x)).trans ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))

/-- A fold whose state carries a fixed environment stores it once more in every state. -/
theorem foldlPeak_lift_le {ρ : Type*} [UniqueEncoding Tree ρ] (g : ρ → β → α → β)
    (p : (ρ × β) × α → ℕ) (e : ρ) (a : β) (xs : List α) :
    foldlPeak (fun (ea : ρ × β) x => (ea.1, g ea.1 ea.2 x)) p (e, a) xs ≤
      ⌜e⌝ₜ.size + 1 + foldlPeak (g e) (fun z => p ((e, z.1), z.2)) a xs := by
  induction xs generalizing a with
  | nil => simp only [foldlPeak_nil, size_encode_prod]; omega
  | cons x xs ih =>
    have := ih (g e a x)
    simp only [foldlPeak_cons, size_encode_prod, max_le_iff] at this ⊢
    omega

/-- One source invariant bounds the remaining callback time and every stored state. -/
theorem foldl_le_of_invariant {t p : β × α → ℕ} (I : List α → β → Prop)
    (remaining : List α → β → ℕ) (space : ℕ) (xs : List α) (a : β) (initial : I xs a)
    (step : ∀ x rest a, I (x :: rest) a → I rest (f a x) ∧
      t (a, x) + remaining rest (f a x) ≤ remaining (x :: rest) a ∧
      ⌜(a, x)⌝ₜ.size ≤ space ∧ p (a, x) ≤ space)
    (stop : ∀ a, I [] a → ⌜a⌝ₜ.size ≤ space) :
    I [] (xs.foldl f a) ∧ foldlTime f t a xs ≤ remaining xs a ∧ foldlPeak f p a xs ≤ space := by
  induction xs generalizing a with
  | nil => simpa using And.intro initial (stop a initial)
  | cons x xs ih =>
    obtain ⟨hi, ht, hs, hp⟩ := step x xs a initial
    obtain ⟨hi', ht', hs'⟩ := ih (f a x) hi
    simp only [List.foldl_cons, foldlTime_cons, foldlPeak_cons, max_le_iff]
    exact ⟨hi', by omega, hs, hp, hs'⟩

/-- A fold that adds at most its current element needs only the initial accumulator and list. -/
theorem foldlPeak_le_of_size {p : β × α → ℕ} (a : β) (xs : List α)
    (result : ∀ a x, ⌜f a x⌝ₜ.size ≤ ⌜(a, x)⌝ₜ.size) (peak : ∀ a x, p (a, x) ≤ ⌜(a, x)⌝ₜ.size) :
    foldlPeak f p a xs ≤ ⌜a⌝ₜ.size + ⌜xs⌝ₜ.size := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    have hr := result a x
    have hp := peak a x
    have := ih (f a x)
    simp only [foldlPeak_cons, encode_list_cons, size_encode_prod, max_le_iff] at hr hp this ⊢
    omega

/-- The callback's result is stored as the next state, so a callback holding only its input and
its result adds nothing to the stored states. -/
@[simp, dominated_simp] theorem foldlPeak_max_size_uncurry (a : β) (xs : List α) :
    foldlPeak f (fun z => max ⌜z⌝ₜ.size ⌜Function.uncurry f z⌝ₜ.size) a xs =
      foldlPeak f (fun z => ⌜z⌝ₜ.size) a xs := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    have := size_le_foldlPeak (f := f) (fun z => ⌜z⌝ₜ.size) (f a x) xs
    simp only [foldlPeak_cons, ih, Function.uncurry_apply_pair]
    omega

/-- Prepending retains exactly the final list as its peak, including the empty fold: both lists,
sharing one terminator. -/
@[simp, dominated_simp] theorem foldlPeak_prepend {α : Type*} [UniqueEncoding Tree α]
    (acc xs : List α) :
    foldlPeak (fun acc x => x :: acc) (fun z => ⌜z⌝ₜ.size) acc xs =
      ⌜xs⌝ₜ.size + ⌜acc⌝ₜ.size - 1 := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    have h := ih (x :: acc)
    have := Tree.size_pos ⌜xs⌝ₜ
    simp only [foldlPeak_cons, encode_list_cons, size_encode_prod] at h ⊢
    omega

theorem _root_.Complexity.Dominated.foldlPeak {p q : β × α → ℕ} (h : Dominated p q) :
    Dominated (fun x : β × List α => foldlPeak f p x.1 x.2)
      (fun x => foldlPeak f q x.1 x.2) := by
  obtain ⟨C, hC⟩ := dominated_iff.mp h
  refine Dominated.of_le_mul (C + 1) fun ⟨a, xs⟩ => ?_
  induction xs generalizing a with
  | nil => exact Nat.le_mul_of_pos_left _ (Nat.succ_pos C)
  | cons x xs ih =>
    have hx := hC (a, x)
    have hr := ih (f a x)
    simp only [smul_eq_mul] at hx
    simp only [foldlPeak_cons, mul_max, max_le_iff]
    refine ⟨(Nat.le_mul_of_pos_left _ (Nat.succ_pos C)).trans (Nat.le_max_left _ _), ?_, ?_⟩
    · exact (hx.trans (Nat.mul_le_mul_right _ (Nat.le_succ C))).trans
        ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _))
    · exact hr.trans ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))

end Cost

namespace Traversal

private theorem foldlStep_bounded {α β : Type*} {time space : ℕ}
    [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    (f : β → α → β) (p : Value → Value → Code Value) (x : α) (a : β)
    (hpFresh : ∀ a v n, a.expression.bound ≤ n → v.expression.bound ≤ n →
      n ≤ ((p a v).build n).2.1)
    (rest acc : Var) (n : ℕ) (s : ℕ → Tree) (xs : List α)
    (hp : ∀ b v m t, n ≤ m → (∀ j < n, t j = s j) →
      b.expression.bound ≤ m → v.expression.bound ≤ m →
      b.eval t = ⌜a⌝ₜ → v.eval t = ⌜x⌝ₜ →
      (p b v).Bounded m t time space (fun w u =>
        w.eval u = ⌜f a x⌝ₜ ∧ ∀ j < m, u j = t j))
    (ha : acc.index < n) (hne : rest.index ≠ acc.index)
    (hsr : rest.get s = ⌜x :: xs⌝ₜ) (hsa : acc.get s = ⌜a⌝ₜ)
    (hs : ⌜x :: xs⌝ₜ.size ≤ space) (haSize : ⌜a⌝ₜ.size ≤ space)
    (ht : ⌜f a x⌝ₜ.size ≤ space) :
    (do
      let r ← read rest
      let x ← r.left
      let a ← read acc
      write acc (← p a x)
      write rest (← r.right)).Bounded n s (time + 10) space (fun _ t =>
        rest.get t = ⌜xs⌝ₜ ∧ acc.get t = ⌜f a x⌝ₜ ∧
        ∀ j < n, j ≠ rest.index → j ≠ acc.index → t j = s j) := by
  simp only [Var.get] at hsr hsa
  simp only [bounded_read_bind_iff, Var.get, bounded_left_bind_iff,
    Value.eval_var, Function.update_self]
  simp +contextual (disch := omega) only [encode_list_cons, encode_prod, Tree.size_pair,
    Nat.le_add_left, hsr, Nat.reduceSubDiff, Nat.add_one_sub_one, Tree.left_pair,
    Function.update_of_ne, hsa, Value.right, Value.expression.eq_2, ne_eq, true_and,
    and_self_left] at hs ht ⊢
  refine ⟨by omega, by omega, ?_⟩
  have hn := hpFresh (.var (n + 2)) (.var (n + 1)) (n + 3)
    (by change n + 2 + 1 ≤ n + 3; omega) (by change n + 1 + 1 ≤ n + 3; omega)
  apply Code.Bounded.bind (hp (.var (n + 2)) (.var (n + 1)) (n + 3) _
    (by omega)
    (by intros; simp (disch := omega))
    (by change n + 2 + 1 ≤ n + 3; omega)
    (by change n + 1 + 1 ≤ n + 3; omega) (by simp) (by simp))
  intro w t ⟨hw, hf⟩
  have hsteps := w.assignSteps_le
  have hr' : t n = .pair ⌜x⌝ₜ ⌜xs⌝ₜ := by
    simpa (disch := omega) using hf n (by omega)
  simp +contextual (disch := omega) [hw, hr', hf]
  omega

theorem foldl_budget_bounded {α β : Type*} {space : ℕ}
    [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    (f : β → α → β) (p : Value → Value → Code Value)
    (hpFresh : ∀ a v n, a.expression.bound ≤ n → v.expression.bound ≤ n →
      n ≤ ((p a v).build n).2.1)
    (cost : β → α → ℕ) (budget : List α → β → ℕ)
    (I : List α → β → Prop) (xs : List α) (a : β) (init v : Value) (n : ℕ) (s : ℕ → Tree)
    (hI : I xs a)
    (hstep : ∀ x as b, I (x :: as) b → I as (f b x))
    (hbudget : ∀ x as b, I (x :: as) b →
      cost b x + 12 + budget as (f b x) ≤ budget (x :: as) b)
    (hsize : ∀ as b, I as b → ⌜as⌝ₜ.size ≤ space ∧ ⌜b⌝ₜ.size ≤ space)
    (hp : ∀ x as b, I (x :: as) b → ∀ w v m t, n ≤ m → (∀ j < n, t j = s j) →
      w.expression.bound ≤ m → v.expression.bound ≤ m → w.eval t = ⌜b⌝ₜ → v.eval t = ⌜x⌝ₜ →
      (p w v).Bounded m t (cost b x) space (fun z u =>
        z.eval u = ⌜f b x⌝ₜ ∧ ∀ j < m, u j = t j))
    (hv : v.expression.bound ≤ n) (hx : v.eval s = ⌜xs⌝ₜ) (ha : init.eval s = ⌜a⌝ₜ) :
    (List.Code.foldl p init v).Bounded n s
      (budget xs a + init.expression.assignSteps + 6) space
      (fun w t => w.eval t = ⌜xs.foldl f a⌝ₜ ∧ ∀ j < n, t j = s j) := by
  have hv' := (v.eval_update_of_bound_le hv s ⌜a⌝ₜ).trans hx
  have hvTime := v.assignSteps_le
  obtain ⟨hs, hb⟩ := hsize xs a hI
  simp only [List.Code.foldl, List.Code.forEach, bind_assoc, bounded_newVar_bind_iff, ha, hv']
  refine ⟨by omega, hb, by omega, hs, ?_⟩
  let u := Function.update (Function.update s n ⌜a⌝ₜ) (n + 1) ⌜xs⌝ₜ
  let J (t : ℕ → Tree) (k : ℕ) := ∃ as b,
    t (n + 1) = ⌜as⌝ₜ ∧ t n = ⌜b⌝ₜ ∧ I as b ∧
      as.foldl f b = xs.foldl f a ∧ (∀ j < n, t j = s j) ∧ k = budget as b + 2
  have hl := Bounded.whileNode_budget (n := n + 2) (s := u) (space := space) ⟨n + 1⟩
    (do
      let r ← read ⟨n + 1⟩
      let x ← r.left
      let a ← read ⟨n⟩
      write ⟨n⟩ (← p a x)
      write ⟨n + 1⟩ (← r.right)) J (budget xs a + 2)
    ⟨xs, a, by simp [u], by simp [u], hI, rfl,
      (by intros; simp (disch := omega) [u]), rfl⟩
    (by rintro t k ⟨as, b, hr, _, hi, _⟩; simpa [Var.get, hr] using (hsize as b hi).1)
    (by rintro t k ⟨as, b, _, _, _, _, _, rfl⟩ _; omega)
    (by
      rintro t k ⟨as, b, hr, hb, hi, heq, hf, rfl⟩ hroot
      cases as with
      | nil => simp [Var.get, hr, encode_unit] at hroot
      | cons x as =>
        have hi' := hstep x as b hi
        refine ⟨cost b x + 10, ?_⟩
        apply (foldlStep_bounded f p x b hpFresh
          ⟨n + 1⟩ ⟨n⟩ (n + 2) t as
          (fun w v m u hm hframe => hp x as b hi w v m u (by omega)
            (fun j hj => (hframe j (by omega)).trans (hf j hj)))
          (by simp) (by simp) hr hb
          (hsize _ _ hi).1 (hsize _ _ hi).2 (hsize _ _ hi').2).mono le_rfl le_rfl
        rintro _ v ⟨hvr, hva, hvf⟩
        refine ⟨budget as (f b x) + 2, ⟨as, f b x, hvr, hva, hi', heq, ?_, rfl⟩, ?_⟩
        · intro j hj
          exact (hvf j (by omega) (by change j ≠ n + 1; omega)
            (by change j ≠ n; omega)).trans (hf j hj)
        · have := hbudget x as b hi; omega)
  apply Bounded.mono (time := (budget xs a + 2) + 2) ?_
    (by omega) le_rfl (fun _ _ h => h)
  apply Bounded.bind (by simpa [u] using hl)
  rintro _ t ⟨⟨k, as, b, hr, hb, hi, heq, hf, _⟩, hstop⟩
  cases as with
  | cons x as => simp [hr, encode_prod] at hstop
  | nil =>
    have hpos := (hsize [] b hi).2
    have hn := hpFresh (.var (n + 4)) (.var (n + 3)) (n + 5)
      (by change n + 4 + 1 ≤ n + 5; omega) (by change n + 3 + 1 ≤ n + 5; omega)
    simp only [List.foldl_nil] at heq
    simp only [bounded_read_iff, Var.get_mk, hb, heq, Value.eval_var,
      Function.update_self, Nat.add_assoc, Nat.reduceAdd, le_refl, true_and]
    refine ⟨by simpa [heq] using hpos, ?_⟩
    intro j hj
    change Function.update t (((p (.var (n + 4)) (.var (n + 3))).build (n + 5)).2.1 + 1)
      ⌜xs.foldl f a⌝ₜ j = s j
    rw [Function.update_of_ne (by omega)]
    exact hf j hj


/-- Map one callback over a list while retaining its shared environment. -/
def mapDependentProgram (p : Value → Code Value) (v : Value) : Code Value := do
  let e ← v.left
  let xs ← v.right
  List.Code.map (fun x => do p (← e.pair x)) xs

/-- Unpack the initial accumulator and list before running a fold callback. -/
def foldProgram (p : Value → Code Value) (v : Value) : Code Value := do
  let a ← v.left
  let xs ← v.right
  List.Code.foldl (fun a x => do p (← a.pair x)) a xs

end Traversal

theorem Implements.foldl {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {p : Value → Code Value} {f : β → α → β} {b : Bounds (β × α)}
    (hf : Implements p (Function.uncurry f) b) :
    Implements (Traversal.foldProgram p) (fun x : β × List α => x.2.foldl f x.1)
      ⟨fun x => foldlTime f b.time x.1 x.2 + 13 * x.2.length + 10,
        fun x => max ⌜x⌝ₜ.size (foldlPeak f b.peak x.1 x.2)⟩ := by
  obtain ⟨hpFresh, hp⟩ := hf
  let q (a x : Value) := do p (← a.pair x)
  have hqFresh : ∀ a v n, a.expression.bound ≤ n → v.expression.bound ≤ n →
      n ≤ ((q a v).build n).2.1 := by
    intro a v n _ _
    have := (hpFresh (.var n) (n + 1) (by change n + 1 ≤ n + 1; omega)).1
    change n ≤ ((p (.var n)).build (n + 1)).2.1
    omega
  constructor
  · intro v n hv
    have := (hpFresh (.var (n + 7)) (n + 8) (by change n + 7 + 1 ≤ n + 8; omega)).1
    change n ≤ ((p (.var (n + 7))).build (n + 8)).2.1 + 2 ∧
      ((p (.var (n + 7))).build (n + 8)).2.1 + 1 + 1 ≤
        ((p (.var (n + 7))).build (n + 8)).2.1 + 2
    omega
  · intro v n s ⟨a, xs⟩ hv hx
    let budget as c := foldlTime f b.time c as + 13 * as.length
    let space := max ⌜(a, xs)⌝ₜ.size (foldlPeak f b.peak a xs)
    let I (as : List α) (c : β) := ⌜as⌝ₜ.size ≤ space ∧ foldlPeak f b.peak c as ≤ space
    have hx' := (v.eval_update_of_bound_le hv s ⌜a⌝ₜ).trans hx
    have hs : ⌜(a, xs)⌝ₜ.size ≤ space := Nat.le_max_left _ _
    change (Traversal.foldProgram p v).Bounded n s (budget xs a + 10) space _
    simp only [Traversal.foldProgram]
    simp only [bounded_left_bind_iff, hx, encode_prod, Tree.left_pair,
      bounded_right_bind_iff, hx', Tree.right_pair]
    refine ⟨by omega, hs, by omega, hs, ?_⟩
    apply (Traversal.foldl_budget_bounded f q hqFresh (fun c x => b.time (c, x) + 1)
      budget I xs a (.var n) (.var (n + 1))
      (n + 2) _ ?_ ?_ ?_ ?_ ?_ (by change n + 1 + 1 ≤ n + 2; omega)
      (by simp) (by simp)).mono (by simp) le_rfl
    · intro w t ⟨hw, hf⟩
      refine ⟨hw, ?_⟩
      intro j hj
      simpa (disch := omega) using hf j (by omega)
    · refine ⟨?_, Nat.le_max_right _ _⟩
      simp only [size_encode_prod] at hs; omega
    · rintro x as c ⟨hs, hp⟩
      simp only [foldlPeak_cons, Nat.max_le] at hp
      refine ⟨?_, hp.2.2⟩
      simp only [encode_list_cons, size_encode_prod] at hs; omega
    · intro x as c _
      simp only [budget, foldlTime_cons, List.length_cons, Nat.mul_add, Nat.mul_one]
      omega
    · rintro as c ⟨hs, hc⟩
      exact ⟨hs, (size_le_foldlPeak b.peak c as).trans hc⟩
    · rintro x as c ⟨_, hs⟩ a v n s _ _ ha hv hc hx
      simp only [foldlPeak_cons, Nat.max_le] at hs
      simp only [q, bounded_pair_bind_iff]
      refine ⟨by omega, ?_, ?_⟩
      · simpa only [hc, hx, ← encode_prod] using hs.1
      · apply (hp (.var n) (n + 1) _ (c, x) (by change n + 1 ≤ n + 1; omega)
          (by simp [hc, hx, encode_prod])).mono (by simp) hs.2.1
        intro w t ⟨hw, hf⟩
        refine ⟨hw, ?_⟩
        intro j hj
        simpa (disch := omega) using hf j (by omega)

/-- Fold a callback; its growth is charged at every actual intermediate accumulator. -/
theorem HasProgram.foldl {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {f : β → α → β} {pf : Value → Code Value} {t p : β × α → ℕ}
    (hf : HasProgram (Function.uncurry f) pf t p) :
    HasProgram (fun x : β × List α => x.2.foldl f x.1) (Traversal.foldProgram pf)
      (fun x => foldlTime f t x.1 x.2 + x.2.length + 1)
      (fun x => max ⌜x⌝ₜ.size (foldlPeak f p x.1 x.2)) := by
  obtain ⟨b, h, hbt, hbp⟩ := hf.sound
  exact ⟨_, h.foldl, ((hbt.foldlTime (f := f)).add
    ((Dominated.refl _).const_mul_left 13)).add (Dominated.const 10),
    (Dominated.refl _).max (hbp.foldlPeak (f := f))⟩

end Complexity.TreeProgram.Source
