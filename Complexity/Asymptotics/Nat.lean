/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Asymptotics.Basic
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Data.Fintype.Order

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

/-- A difference is dominated whenever its minuend is. -/
theorem sub_left (hf : Dominated f g) (f' : α → ℕ) : Dominated (fun x => f x - f' x) g :=
  hf.mono_left fun _ => Nat.sub_le _ _

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

/-- On a finite type every function is bounded, hence within a multiple of any positive one. -/
theorem of_finite [Finite α] (hg : ∀ x, 0 < g x) : Dominated f g :=
  have ⟨C, hC⟩ := Finite.exists_le f
  ((Dominated.const C).mono_left hC).trans (one hg)

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
    (fun i _ => hc ⟨x, i⟩)
  simpa only [List.map_const', List.sum_replicate, List.length_finRange,
    Nat.nsmul_eq_mul, Nat.mul_left_comm] using hs

/-- A table sum is bounded by its target when every entry, multiplied by the table length, is
bounded by the same target. -/
theorem sum_finRange_of_mul {n : α → ℕ} {a : (x : α) → Fin (n x) → ℕ} {g : α → ℕ}
    (h : Dominated (fun z : Σ x, Fin (n x) => n z.1 * a z.1 z.2) (fun z => g z.1)) :
    Dominated (fun x => ((List.finRange (n x)).map (a x)).sum) g := by
  obtain ⟨C, hc⟩ := dominated_iff.mp h
  refine of_le_mul C fun x => ?_
  rcases Nat.eq_zero_or_pos (n x) with h0 | hpos
  · have hnil : List.finRange (n x) = [] := List.eq_nil_of_length_eq_zero (by simp [h0])
    simp [hnil]
  · have hs := List.sum_le_sum (l := List.finRange (n x))
      (fun i _ => by simpa only [Nat.nsmul_eq_mul] using hc ⟨x, i⟩)
    have hmul (l : List (Fin (n x))) :
        (l.map fun i => n x * a x i).sum = n x * (l.map (a x)).sum := by
      induction l <;> simp [*, Nat.mul_add]
    simp only [hmul, List.map_const', List.sum_replicate, List.length_finRange,
      Nat.nsmul_eq_mul] at hs
    exact Nat.le_of_mul_le_mul_left hs hpos

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

/-- `t` is polynomial in `s` on every input: `t` is `O((s + 1) ^ d)` for some `d`. The shift
by one makes constants and sums polynomial also where `s` vanishes. -/
structure IsPoly {α : Type*} (s t : α → ℕ) : Prop where
  /-- A degree bounding `t` by a power of `s + 1`. -/
  exists_dominated : ∃ d, Dominated t fun a => (s a + 1) ^ d

namespace IsPoly

variable {α : Type*} {s f g : α → ℕ}

theorem const (c : ℕ) : IsPoly s fun _ => c :=
  ⟨0, Dominated.const_of_pos c fun _ => Nat.pow_pos (Nat.succ_pos _)⟩

theorem refl : IsPoly s s :=
  ⟨1, Dominated.of_le fun a => by simp⟩

/-- On a finite type every function is polynomial in any measure. -/
theorem of_finite [Finite α] : IsPoly s f :=
  ⟨0, Dominated.of_finite fun _ => by simp⟩

theorem of_dominated (hg : IsPoly s g) (h : Dominated f g) : IsPoly s f :=
  let ⟨d, hd⟩ := hg
  ⟨d, h.trans hd⟩

theorem add (hf : IsPoly s f) (hg : IsPoly s g) : IsPoly s fun a => f a + g a := by
  obtain ⟨d, hf⟩ := hf
  obtain ⟨e, hg⟩ := hg
  have hpos (a : α) : 0 < s a + 1 := Nat.succ_pos _
  exact ⟨max d e, (hf.mono_pow (le_max_left d e) hpos).add_same
    (hg.mono_pow (le_max_right d e) hpos)⟩

theorem max (hf : IsPoly s f) (hg : IsPoly s g) : IsPoly s fun a => max (f a) (g a) := by
  obtain ⟨d, hf⟩ := hf
  obtain ⟨e, hg⟩ := hg
  have hpos (a : α) : 0 < s a + 1 := Nat.succ_pos _
  exact ⟨Max.max d e, (hf.mono_pow (le_max_left d e) hpos).max_same
    (hg.mono_pow (le_max_right d e) hpos)⟩

theorem mul (hf : IsPoly s f) (hg : IsPoly s g) : IsPoly s fun a => f a * g a := by
  obtain ⟨d, hf⟩ := hf
  obtain ⟨e, hg⟩ := hg
  exact ⟨d + e, (hf.mul hg).mono fun a => (pow_add (s a + 1) d e).ge⟩

theorem pow (hf : IsPoly s f) (n : ℕ) : IsPoly s fun a => f a ^ n := by
  obtain ⟨d, hf⟩ := hf
  exact ⟨d * n, (hf.pow n).mono fun a => (pow_mul (s a + 1) d n).ge⟩

theorem sub (hf : IsPoly s f) (g : α → ℕ) : IsPoly s fun a => f a - g a :=
  hf.of_dominated (Dominated.of_le fun _ => Nat.sub_le _ _)

/-- A maximum over a list, possibly of dependent elements, is polynomial when its elements are,
uniformly in the measure of their input. -/
theorem foldr_max {ι : α → Type*} (xs : (x : α) → List (ι x)) {a : (x : α) → ι x → ℕ}
    (h : IsPoly (fun z : Σ x, ι x => s z.1) fun z => a z.1 z.2) :
    IsPoly s fun x => (xs x).foldr (fun i m => Max.max (a x i) m) 0 :=
  let ⟨d, h⟩ := h
  ⟨d, Dominated.foldr_max_le xs h⟩

/-- A maximum over a list is polynomial when the elements that occur are, uniformly in the measure
of their input. -/
theorem list_foldr_max {ι : Type*} (xs : α → List ι) {a : α → ι → ℕ}
    (h : IsPoly (fun z : {p : α × ι // p.2 ∈ xs p.1} => s z.1.1) fun z => a z.1.1 z.1.2) :
    IsPoly s fun x => (xs x).foldr (fun i m => Max.max (a x i) m) 0 :=
  let ⟨d, h⟩ := h
  ⟨d, Dominated.list_foldr_max_le xs h⟩

/-- A table sum is polynomial when its length and its entries are, the entries uniformly in the
measure of their input. -/
theorem sum_finRange {n : α → ℕ} {a : (x : α) → Fin (n x) → ℕ} (hn : IsPoly s n)
    (h : IsPoly (fun z : Σ x, Fin (n x) => s z.1) fun z => a z.1 z.2) :
    IsPoly s fun x => ((List.finRange (n x)).map (a x)).sum := by
  obtain ⟨e, hn⟩ := hn
  obtain ⟨d, h⟩ := (IsPoly.mul ⟨e, hn.comp Sigma.fst⟩ h :
    IsPoly (fun z : Σ x, Fin (n x) => s z.1) fun z => n z.1 * a z.1 z.2)
  exact ⟨d, Dominated.sum_finRange_of_mul h⟩

/-- A function polynomial on the inputs where `p` holds and on those where it fails is
polynomial. -/
theorem of_cases (p : α → Prop)
    (yes : IsPoly (s ∘ Subtype.val : {x // p x} → ℕ) (f ∘ Subtype.val))
    (no : IsPoly (s ∘ Subtype.val : {x // ¬p x} → ℕ) (f ∘ Subtype.val)) : IsPoly s f := by
  obtain ⟨d, yes⟩ := yes
  obtain ⟨e, no⟩ := no
  have hpos (a : α) : 0 < s a + 1 := Nat.succ_pos _
  exact ⟨Max.max d e, Dominated.of_cases p (yes.mono_pow (le_max_left d e) fun _ => hpos _)
    (no.mono_pow (le_max_right d e) fun _ => hpos _)⟩

/-- A polynomial in `r`, applied where `r` is polynomial in `s`, is polynomial in `s`. -/
theorem comp {β : Type*} {r T : β → ℕ} {h : α → β} (hT : IsPoly r T)
    (hh : IsPoly s fun a => r (h a)) : IsPoly s fun a => T (h a) := by
  obtain ⟨d, hT⟩ := hT
  obtain ⟨e, hh⟩ := hh
  have h1 : Dominated (fun a => r (h a) + 1) fun a => (s a + 1) ^ e :=
    hh.add_same (Dominated.const_of_pos 1 fun _ => Nat.pow_pos (Nat.succ_pos _))
  exact ⟨e * d, (hT.comp h).trans ((h1.pow d).mono fun a => (pow_mul (s a + 1) e d).ge)⟩

end IsPoly

end Complexity
