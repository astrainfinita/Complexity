/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Asymptotics.Basic
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Order.Filter.AtTopBot.Basic

/-! # Natural resources and polynomial substitutions -/

@[expose] public section

namespace Complexity

open Filter

namespace Dominated

variable {α : Type*} {f g f' g' : α → ℕ}

theorem mul (hf : Dominated f g) (hh : Dominated f' g') :
    Dominated (fun x => f x * f' x) (fun x => g x * g' x) := by
  obtain ⟨C, hc⟩ := hf
  obtain ⟨D, hd⟩ := hh
  refine ⟨C * D, ?_⟩
  intro x
  have hx := hc x
  have hy := hd x
  simpa only [Nat.nsmul_eq_mul, Nat.mul_mul_mul_comm] using Nat.mul_le_mul hx hy

theorem pow (hf : Dominated f g) (d : ℕ) :
    Dominated (fun x => f x ^ d) (fun x => g x ^ d) := by
  obtain ⟨C, hc⟩ := hf
  refine ⟨C ^ d, fun x => ?_⟩
  have hx := hc x
  simpa only [Nat.nsmul_eq_mul, Nat.mul_pow] using Nat.pow_le_pow_left hx d

theorem const_mul_left (hf : Dominated f g) (C : ℕ) :
    Dominated (fun x => C * f x) g := hf.const_nsmul_left C

@[simp] theorem const_mul_left_iff {C : ℕ} (hC : 0 < C) :
    Dominated (fun x => C * f x) g ↔ Dominated f g :=
  ⟨fun h => h.mono_left fun x => Nat.le_mul_of_pos_left (f x) hC,
    fun h => h.const_mul_left C⟩

theorem const (C : ℕ) : Dominated (fun _ : α => C) (fun _ => 1) :=
  ⟨C, fun _ => by simp only [Nat.nsmul_eq_mul, Nat.mul_one]; exact le_rfl⟩

theorem one (hg : ∀ x, 0 < g x) : Dominated (fun _ => 1) g :=
  of_le hg

@[simp] theorem const_of_pos (C : ℕ) (hg : ∀ x, 0 < g x) :
    Dominated (fun _ => C) g := (const C).trans (one hg)

theorem pow_of_le (h : Dominated f g) {d e : ℕ} (hde : d ≤ e)
    (hg : ∀ x, 0 < g x) :
    Dominated (fun x => f x ^ d) (fun x => g x ^ e) :=
  (h.pow d).mono fun x => Nat.pow_le_pow_right (hg x) hde

theorem max (hf : Dominated f g) (hh : Dominated f' g') :
    Dominated (fun x => Max.max (f x) (f' x)) (fun x => Max.max (g x) (g' x)) :=
  ((hf.mono fun _ => Nat.le_max_left _ _).add_same
    (hh.mono fun _ => Nat.le_max_right _ _)).mono_left fun _ =>
      max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)

theorem max_same (hf : Dominated f g) (hh : Dominated f' g) :
    Dominated (fun x => Max.max (f x) (f' x)) g :=
  (hf.add_same hh).mono_left fun _ => max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)

@[simp] theorem max_iff : Dominated (fun x => Max.max (f x) (f' x)) g ↔
    Dominated f g ∧ Dominated f' g :=
  ⟨fun h => ⟨h.mono_left fun _ => Nat.le_max_left ..,
      h.mono_left fun _ => Nat.le_max_right ..⟩, fun h => h.1.max_same h.2⟩

end Dominated

namespace Dominated

variable {α : Type*} {f g : α → ℕ}

theorem of_le_mul (C : ℕ) (h : ∀ x, f x ≤ C * g x) : Dominated f g :=
  dominated_iff.mpr ⟨C, h⟩

/-- A constant cost has a uniform allowance, without choosing its value in the caller. -/
theorem of_forall_eq (h : ∀ x y, f x = f y) : Dominated f (fun _ => 1) := by
  classical
  cases isEmpty_or_nonempty α with
  | inl _ => exact of_le fun x => isEmptyElim x
  | inr ha =>
    let a := Classical.choice ha
    exact (Dominated.const (f a)).mono_left fun x => (h x a).le

theorem le_pow {e : ℕ} (h : Dominated f g) (he : 0 < e) :
    Dominated f (fun x => g x ^ e) :=
  h.mono fun x => Nat.le_self_pow (by omega) (g x)

theorem mono_pow {d e : ℕ} (h : Dominated f (fun x => g x ^ d))
    (hde : d ≤ e) (hg : ∀ x, 0 < g x) : Dominated f (fun x => g x ^ e) :=
  h.mono fun x => Nat.pow_le_pow_right (hg x) hde

/-- The coefficient covers the whole dependent callback family before the sum is taken. -/
theorem sum_finRange {n : α → ℕ} {a : (x : α) → Fin (n x) → ℕ} {b : α → ℕ}
    (h : Dominated (fun z : Σ x, Fin (n x) => a z.1 z.2) (fun z => b z.1)) :
    Dominated (fun x => ((List.finRange (n x)).map (a x)).sum)
      (fun x => n x * b x) := by
  obtain ⟨C, hc⟩ := dominated_iff.mp h
  refine of_le_mul C fun x => ?_
  have hs := List.sum_le_sum (l := List.finRange (n x))
    (g := fun _ => C * b x) (fun i _ => hc ⟨x, i⟩)
  simpa only [List.map_const', List.sum_replicate, List.length_finRange,
    Nat.nsmul_eq_mul, Nat.mul_left_comm] using hs

/-- A table sum is bounded by a power of a scale that bounds both its length and its entries. -/
theorem sum_finRange_pow {n : α → ℕ} {a : (x : α) → Fin (n x) → ℕ} {S : α → ℕ} {e : ℕ}
    (he : 2 ≤ e) (hS : ∀ x, 0 < S x) (hn : Dominated n S)
    (h : Dominated (fun z : Σ x, Fin (n x) => a z.1 z.2) (fun z => S z.1)) :
    Dominated (fun x => ((List.finRange (n x)).map (a x)).sum) (fun x => S x ^ e) :=
  (sum_finRange h).trans ((hn.mul (Dominated.refl S)).trans
    (Dominated.of_le fun x => by rw [← pow_two]; exact Nat.pow_le_pow_right (hS x) he))

/-- Dependent traversal uses one coefficient for all environments and callback arguments. -/
theorem sum_map {ι : α → Type*} (xs : (x : α) → List (ι x))
    {a b : (x : α) → ι x → ℕ}
    (h : Dominated (fun z : Σ x, ι x => a z.1 z.2) (fun z => b z.1 z.2)) :
    Dominated (fun x => ((xs x).map (a x)).sum)
      (fun x => ((xs x).map (b x)).sum) := by
  obtain ⟨C, hc⟩ := dominated_iff.mp h
  refine of_le_mul C fun x => ?_
  induction xs x with
  | nil => simp
  | cons i xs ih =>
    simp only [List.map_cons, List.sum_cons, Nat.mul_add]
    exact Nat.add_le_add (hc ⟨x, i⟩) ih

/-- The same callback-family coefficient bounds a traversal's peak. -/
theorem foldr_max {ι : α → Type*} (xs : (x : α) → List (ι x))
    {a b : (x : α) → ι x → ℕ}
    (h : Dominated (fun z : Σ x, ι x => a z.1 z.2) (fun z => b z.1 z.2)) :
    Dominated (fun x => (xs x).foldr (fun i s => Max.max (a x i) s) 0)
      (fun x => (xs x).foldr (fun i s => Max.max (b x i) s) 0) := by
  obtain ⟨C, hc⟩ := dominated_iff.mp h
  refine of_le_mul C fun x => ?_
  induction xs x with
  | nil => simp
  | cons i xs ih =>
    simp only [List.foldr_cons]
    exact max_le ((hc ⟨x, i⟩).trans (Nat.mul_le_mul_left C (Nat.le_max_left ..)))
      (ih.trans (Nat.mul_le_mul_left C (Nat.le_max_right ..)))

/-- A uniform bound on all traversal elements bounds the peak, including empty lists. -/
theorem foldr_max_le {ι : α → Type*} (xs : (x : α) → List (ι x))
    {a : (x : α) → ι x → ℕ} {b : α → ℕ}
    (h : Dominated (fun z : Σ x, ι x => a z.1 z.2) (fun z => b z.1)) :
    Dominated (fun x => (xs x).foldr (fun i s => Max.max (a x i) s) 0) b := by
  apply (foldr_max xs (b := fun x _ => b x) h).mono
  intro x
  induction xs x with
  | nil => exact Nat.zero_le _
  | cons i xs ih => exact max_le le_rfl ih

/-- A shared coefficient over the elements that actually occur bounds a list's peak. -/
theorem list_foldr_max_le {ι : Type*} (xs : α → List ι)
    {a : α → ι → ℕ} {b : α → ℕ}
    (h : Dominated (fun z : {p : α × ι // p.2 ∈ xs p.1} => a z.1.1 z.1.2)
      (fun z => b z.1.1)) :
    Dominated (fun x => (xs x).foldr (fun i s => Max.max (a x i) s) 0) b := by
  obtain ⟨C, hc⟩ := dominated_iff.mp h
  refine of_le_mul C fun x => ?_
  have aux (ys : List ι) (hy : ∀ i ∈ ys, a x i ≤ C * b x) :
      ys.foldr (fun i s => Max.max (a x i) s) 0 ≤ C * b x := by
    induction ys with
    | nil => exact Nat.zero_le _
    | cons y ys ih =>
      exact max_le (hy y (by simp)) (ih (fun i hi => hy i (by simp [hi])))
  exact aux (xs x) (fun i hi => hc ⟨(x, i), hi⟩)

theorem ite_zero (h : Dominated f g) (p : α → Prop) [DecidablePred p] :
    Dominated (fun x => if p x then f x else 0) g :=
  h.mono_left fun x => by split <;> omega

/-- Two parametrizations cover the input type, with shared coefficients across both branches. -/
theorem of_cover {β γ : Type*} (u : β → α) (v : γ → α)
    (cover : ∀ x, (∃ y, u y = x) ∨ ∃ z, v z = x)
    (hu : Dominated (f ∘ u) (g ∘ u))
    (hv : Dominated (f ∘ v) (g ∘ v)) : Dominated f g := by
  obtain ⟨C, hc⟩ := dominated_iff.mp hu
  obtain ⟨D, hd⟩ := dominated_iff.mp hv
  refine of_le_mul (C + D) fun x => ?_
  rcases cover x with ⟨y, rfl⟩ | ⟨z, rfl⟩
  · exact (hc y).trans (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
  · exact (hd z).trans (Nat.mul_le_mul_right _ (Nat.le_add_left _ _))

/-- Branch coefficients are unified once for both subfamilies. -/
theorem of_cases (p : α → Prop)
    (yes : Dominated (f ∘ Subtype.val : {x // p x} → ℕ) (g ∘ Subtype.val))
    (no : Dominated (f ∘ Subtype.val : {x // ¬p x} → ℕ) (g ∘ Subtype.val)) :
    Dominated f g := by
  obtain ⟨C, hc⟩ := dominated_iff.mp yes
  obtain ⟨D, hd⟩ := dominated_iff.mp no
  refine of_le_mul (C + D) fun x => ?_
  classical
  by_cases h : p x
  · exact (hc ⟨x, h⟩).trans (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
  · exact (hd ⟨x, h⟩).trans (Nat.mul_le_mul_right _ (Nat.le_add_left _ _))

/-- Branch costs retain their shape, with one coefficient covering both input subfamilies. -/
theorem ite {f' g' : α → ℕ} (hf : Dominated f g) (hh : Dominated f' g')
    (p : α → Prop) [DecidablePred p] :
    Dominated (fun x => if p x then f x else f' x) (fun x => if p x then g x else g' x) := by
  apply of_cases p
  · convert hf.comp (Subtype.val : {x // p x} → α) using 1 <;>
      funext x <;> simp only [Function.comp_apply, ite_eq_left x.property]
  · convert hh.comp (Subtype.val : {x // ¬p x} → α) using 1 <;>
      funext x <;> simp only [Function.comp_apply, ite_eq_right x.property]

end Dominated

/-- Polynomial-size substitution uses the same coefficients at every internal input. -/
theorem Dominated.comp_pow {α : Type*} {f : ℕ → ℕ} {d k : ℕ} {u size : α → ℕ}
    (hf : Dominated f (fun n => n ^ d)) (hu : Dominated u (fun x => size x ^ k)) :
    Dominated (f ∘ u) (fun x => size x ^ (k * d)) := by
  exact (hf.comp u).trans (by simpa only [Function.comp_def, ← pow_mul] using hu.pow d)

/-- Comparison of size bounds at infinity, used only at complexity-class boundaries.
This relation does not relax correctness or termination at any input. -/
def DominatedAtTop (f g : ℕ → ℕ) : Prop :=
  ∃ C : ℕ, ∀ᶠ n in atTop, f n ≤ C * g n

/-- Natural size bounds admit one coefficient and one size threshold. -/
theorem dominatedAtTop_iff {f g : ℕ → ℕ} : DominatedAtTop f g ↔
    ∃ C N : ℕ, ∀ n ≥ N, f n ≤ C * g n := by
  simp only [DominatedAtTop, Filter.eventually_atTop]

/-- An all-input specification can be exported to the size boundary. -/
theorem Dominated.atTop {f g : ℕ → ℕ} (h : Dominated f g) : DominatedAtTop f g := by
  obtain ⟨C, hc⟩ := h
  exact ⟨C, Eventually.of_forall hc⟩

namespace DominatedAtTop

variable {f g h f' g' : ℕ → ℕ}

theorem of_eventually_le (h : ∀ᶠ n in atTop, f n ≤ g n) : DominatedAtTop f g :=
  ⟨1, by simpa only [Nat.one_mul] using h⟩

theorem of_le (h : ∀ n, f n ≤ g n) : DominatedAtTop f g :=
  of_eventually_le (Eventually.of_forall h)

theorem refl (f : ℕ → ℕ) : DominatedAtTop f f := of_le fun _ => le_rfl

theorem trans (hf : DominatedAtTop f g) (hg : DominatedAtTop g h) :
    DominatedAtTop f h := by
  obtain ⟨C, hc⟩ := hf
  obtain ⟨D, hd⟩ := hg
  refine ⟨C * D, ?_⟩
  filter_upwards [hc, hd] with n hn hm
  exact (hn.trans (Nat.mul_le_mul_left C hm)).trans_eq (Nat.mul_assoc _ _ _).symm

theorem mono (h : DominatedAtTop f g) (h' : ∀ n, g n ≤ g' n) : DominatedAtTop f g' :=
  h.trans (of_le h')

theorem mono_left (h : DominatedAtTop f g) (h' : ∀ n, f' n ≤ f n) : DominatedAtTop f' g :=
  (of_le h').trans h

theorem mono_eventually (h : DominatedAtTop f g) (h' : ∀ᶠ n in atTop, g n ≤ g' n) :
    DominatedAtTop f g' := h.trans (of_eventually_le h')

theorem add (hf : DominatedAtTop f g) (hh : DominatedAtTop f' g') :
    DominatedAtTop (fun n => f n + f' n) (fun n => g n + g' n) := by
  obtain ⟨C, hc⟩ := hf
  obtain ⟨D, hd⟩ := hh
  refine ⟨C + D, ?_⟩
  filter_upwards [hc, hd] with n hn hm
  rw [Nat.mul_add]
  exact Nat.add_le_add
    (hn.trans (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)))
    (hm.trans (Nat.mul_le_mul_right _ (Nat.le_add_left _ _)))

theorem add_same (hf : DominatedAtTop f g) (hh : DominatedAtTop f' g) :
    DominatedAtTop (fun n => f n + f' n) g := by
  obtain ⟨C, hc⟩ := hf
  obtain ⟨D, hd⟩ := hh
  refine ⟨C + D, ?_⟩
  filter_upwards [hc, hd] with n hn hm
  simpa only [Nat.add_mul] using Nat.add_le_add hn hm

@[simp] theorem add_iff : DominatedAtTop (fun n => f n + f' n) g ↔
    DominatedAtTop f g ∧ DominatedAtTop f' g :=
  ⟨fun h => ⟨h.mono_left fun _ => Nat.le_add_right ..,
    h.mono_left fun _ => Nat.le_add_left ..⟩, fun h => h.1.add_same h.2⟩

@[simp] theorem zero : DominatedAtTop (fun _ => 0) g := of_le fun _ => Nat.zero_le _

theorem mul (hf : DominatedAtTop f g) (hh : DominatedAtTop f' g') :
    DominatedAtTop (fun n => f n * f' n) (fun n => g n * g' n) := by
  obtain ⟨C, hc⟩ := hf
  obtain ⟨D, hd⟩ := hh
  refine ⟨C * D, ?_⟩
  filter_upwards [hc, hd] with n hn hm
  simpa only [Nat.mul_mul_mul_comm] using Nat.mul_le_mul hn hm

theorem pow (hf : DominatedAtTop f g) (d : ℕ) :
    DominatedAtTop (fun n => f n ^ d) (fun n => g n ^ d) := by
  obtain ⟨C, hc⟩ := hf
  exact ⟨C ^ d, hc.mono fun n hn => by
    simpa only [Nat.mul_pow] using Nat.pow_le_pow_left hn d⟩

theorem const_mul_left (hf : DominatedAtTop f g) (C : ℕ) :
    DominatedAtTop (fun n => C * f n) g :=
  (show DominatedAtTop (fun n => C * f n) f from
    ⟨C, Eventually.of_forall fun _ => le_rfl⟩).trans hf

theorem const (C : ℕ) : DominatedAtTop (fun _ => C) (fun _ => 1) :=
  (Dominated.const C).atTop

theorem one (hg : ∀ᶠ n in atTop, 0 < g n) : DominatedAtTop (fun _ => 1) g :=
  of_eventually_le hg

theorem const_of_pos (C : ℕ) (hg : ∀ᶠ n in atTop, 0 < g n) :
    DominatedAtTop (fun _ => C) g := (const C).trans (one hg)

theorem max (hf : DominatedAtTop f g) (hh : DominatedAtTop f' g') :
    DominatedAtTop (fun n => Max.max (f n) (f' n)) (fun n => Max.max (g n) (g' n)) :=
  ((hf.mono fun _ => Nat.le_max_left ..).add_same
    (hh.mono fun _ => Nat.le_max_right ..)).mono_left fun _ =>
      max_le (Nat.le_add_right ..) (Nat.le_add_left ..)

theorem max_same (hf : DominatedAtTop f g) (hh : DominatedAtTop f' g) :
    DominatedAtTop (fun n => Max.max (f n) (f' n)) g :=
  (hf.add_same hh).mono_left fun _ => max_le (Nat.le_add_right ..) (Nat.le_add_left ..)

end DominatedAtTop

end Complexity
