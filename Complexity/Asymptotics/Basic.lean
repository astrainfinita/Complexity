/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Domination by a uniform natural additive coefficient

A program specification covers every input with one coefficient. Internal calls may repeatedly
visit small inputs, so an eventual estimate would not support arbitrary substitution. In
particular, a cofinite estimate on a finite input type could impose no bound at all.
The relation needs addition, order, and natural scalar multiplication, but no multiplication
on resources. It neither adds a positive allowance nor excludes zero bounds.
-/

@[expose] public section

namespace Complexity

variable {α β M : Type*} [AddCommMonoid M] [PartialOrder M] [CanonicallyOrderedAdd M]

/-- One natural additive coefficient bounds every input, including all callback arguments. -/
def Dominated (f g : α → M) : Prop := ∃ C : ℕ, ∀ x, f x ≤ C • g x

/-- `IsO(T)` is the property of a function of being `O(T)`, on every input:
`fun t => Dominated t T`. It states budgets in specifications, as in
`ComputableIn f IsO(T) IsO(S)`. -/
scoped notation "IsO(" T ")" => fun t => Dominated t T

omit [CanonicallyOrderedAdd M] in
theorem dominated_iff {f g : α → M} : Dominated f g ↔ ∃ C : ℕ, ∀ x, f x ≤ C • g x :=
  Iff.rfl

namespace Dominated

variable {f g h f' g' : α → M}

omit [CanonicallyOrderedAdd M] in
theorem of_le (h : ∀ x, f x ≤ g x) : Dominated f g :=
  ⟨1, fun x => by simpa only [one_nsmul] using h x⟩

omit [CanonicallyOrderedAdd M] in
theorem refl (f : α → M) : Dominated f f := of_le fun _ => le_rfl

theorem trans (hf : Dominated f g) (hg : Dominated g h) : Dominated f h := by
  obtain ⟨C, hc⟩ := hf
  obtain ⟨D, hd⟩ := hg
  refine ⟨C * D, ?_⟩
  intro x
  have hx := hc x
  have hy := hd x
  exact (hx.trans (nsmul_le_nsmul_right hy C)).trans_eq
    (by simpa only [Nat.mul_comm] using (mul_nsmul (h x) D C).symm)

theorem mono (h : Dominated f g) (h' : ∀ x, g x ≤ g' x) : Dominated f g' :=
  h.trans (of_le h')

theorem mono_left (h : Dominated f g) (h' : ∀ x, f' x ≤ f x) : Dominated f' g :=
  (of_le h').trans h

theorem add (hf : Dominated f g) (hf' : Dominated f' g') :
    Dominated (fun x => f x + f' x) (fun x => g x + g' x) := by
  obtain ⟨C, hc⟩ := hf
  obtain ⟨D, hd⟩ := hf'
  refine ⟨C + D, ?_⟩
  intro x
  have hx := hc x
  have hy := hd x
  rw [nsmul_add]
  exact add_le_add
    (hx.trans (nsmul_le_nsmul_left zero_le (Nat.le_add_right C D)))
    (hy.trans (nsmul_le_nsmul_left zero_le (Nat.le_add_left D C)))

theorem add_same (hf : Dominated f g) (hf' : Dominated f' g) :
    Dominated (fun x => f x + f' x) g := by
  obtain ⟨C, hc⟩ := hf
  obtain ⟨D, hd⟩ := hf'
  refine ⟨C + D, ?_⟩
  intro x
  have hx := hc x
  have hy := hd x
  simpa only [add_nsmul] using add_le_add hx hy

@[simp] theorem add_iff : Dominated (fun x => f x + f' x) g ↔
    Dominated f g ∧ Dominated f' g :=
  ⟨fun h => ⟨h.mono_left fun _ => le_self_add, h.mono_left fun _ => le_add_self⟩,
    fun h => h.1.add_same h.2⟩

@[simp] theorem zero : Dominated (fun _ => (0 : M)) g := of_le fun _ => zero_le

theorem const_nsmul_left (h : Dominated f g) (C : ℕ) :
    Dominated (fun x => C • f x) g := by
  exact (show Dominated (fun x => C • f x) f from
    ⟨C, fun _ => le_rfl⟩).trans h

/-- A fixed finite family may have separate coefficients. -/
theorem finset_sum {ι : Type*} (s : Finset ι) (a b : ι → α → M)
    (h : ∀ i ∈ s, Dominated (a i) (b i)) :
    Dominated (fun x => ∑ i ∈ s, a i x) (fun x => ∑ i ∈ s, b i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact of_le fun _ => le_rfl
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using
      (h i (Finset.mem_insert_self i s)).add
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

end Dominated

namespace Dominated

omit [CanonicallyOrderedAdd M] in
theorem comp {f g : α → M} (h : Dominated f g) (u : β → α) :
    Dominated (f ∘ u) (g ∘ u) := by
  obtain ⟨C, hc⟩ := dominated_iff.mp h
  exact dominated_iff.mpr ⟨C, fun x => hc (u x)⟩

omit [CanonicallyOrderedAdd M] in
/-- Check a uniform bound on a surjective parametrization of the legal inputs. -/
theorem of_comp_surjective {f g : α → M} (u : β → α) (hu : Function.Surjective u)
    (h : Dominated (f ∘ u) (g ∘ u)) : Dominated f g := by
  obtain ⟨C, hc⟩ := dominated_iff.mp h
  exact dominated_iff.mpr ⟨C, fun x => by obtain ⟨y, rfl⟩ := hu x; exact hc y⟩

/-- A single specification on the callback family supplies the shared coefficient automatically. -/
theorem sum {ι : Type*} (s : α → Finset ι) (a b : α → ι → M)
    (h : Dominated (fun z : {p : α × ι // p.2 ∈ s p.1} => a z.1.1 z.1.2)
      (fun z => b z.1.1 z.1.2)) :
    Dominated (fun x => ∑ i ∈ s x, a x i) (fun x => ∑ i ∈ s x, b x i) := by
  obtain ⟨C, hc⟩ := dominated_iff.mp h
  refine ⟨C, fun x => ?_⟩
  rw [← Finset.sum_nsmul]
  exact Finset.sum_le_sum (fun i hi => hc ⟨(x, i), hi⟩)

/-- List traversal counts repeated elements; the witness still covers the entire callback family. -/
theorem list_sum {ι : Type*} (xs : α → List ι) (a b : α → ι → M)
    (h : Dominated (fun z : {p : α × ι // p.2 ∈ xs p.1} => a z.1.1 z.1.2)
      (fun z => b z.1.1 z.1.2)) :
    Dominated (fun x => ((xs x).map (a x)).sum) (fun x => ((xs x).map (b x)).sum) := by
  obtain ⟨C, hc⟩ := dominated_iff.mp h
  refine dominated_iff.mpr ⟨C, fun x => ?_⟩
  have bound (ys : List ι) (hy : ∀ i ∈ ys, a x i ≤ C • b x i) :
      (ys.map (a x)).sum ≤ C • (ys.map (b x)).sum := by
    induction ys with
    | nil => simp
    | cons i ys ih =>
      simp only [List.map_cons, List.sum_cons, nsmul_add]
      exact add_le_add (hy i (List.mem_cons_self ..))
        (ih (fun j hj => hy j (List.mem_cons_of_mem i hj)))
  exact bound (xs x) (fun i hi => hc ⟨(x, i), hi⟩)

end Dominated

/-- Peak-like joins need a compatible supremum, but no multiplication on the resource. -/
theorem Dominated.sup {N : Type*} [AddCommMonoid N] [SemilatticeSup N]
    [CanonicallyOrderedAdd N] {f g f' g' : α → N}
    (hf : Dominated f g) (hh : Dominated f' g') :
    Dominated (fun x => f x ⊔ f' x) (fun x => g x ⊔ g' x) :=
  ((hf.mono fun _ => le_sup_left).add_same
    (hh.mono fun _ => le_sup_right)).mono_left fun _ => sup_le le_self_add le_add_self

end Complexity
