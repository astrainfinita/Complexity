/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Encoding.Fin
public import Complexity.Encoding.Nat
public import Complexity.Asymptotics.Nat
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Data.Finset.Lattice.Fold

/-! # Properness of actual tree encoding size -/

@[expose] public section

namespace Complexity

theorem Tree.finite_size_lt (N : ℕ) : {t : Tree | t.size < N}.Finite := by
  induction N with
  | zero => simp
  | succ N ih =>
    apply ((Set.finite_singleton Tree.nil).union
      ((ih.prod ih).image (fun p : Tree × Tree => Tree.pair p.1 p.2))).subset
    intro t ht
    cases t with
    | nil => exact Or.inl (by rfl)
    | node u a b =>
      cases u
      right
      refine ⟨(a, b), ⟨?_, ?_⟩, rfl⟩ <;>
        have ha := Tree.size_pos a <;> have hb := Tree.size_pos b <;>
        simp only [Set.mem_ofPred_eq, Tree.size_pair] at ht ⊢ <;> omega

theorem finite_size_encode_lt {α : Type*} [UniqueEncoding Tree α] (N : ℕ) :
    {x : α | (encode Tree x).size < N}.Finite :=
  (Tree.finite_size_lt N).preimage UniqueEncoding.encode_injective.injOn

/-- Maximum resource on the finite fiber of one exact input size. Empty fibers cost zero. -/
noncomputable def sizeEnvelope {α : Type*} [UniqueEncoding Tree α]
    (f : α → ℕ) (n : ℕ) : ℕ :=
  ((finite_size_encode_lt (n + 1)).subset
    (show {x | (encode Tree x).size = n} ⊆ {x | (encode Tree x).size < n + 1} from
      fun _ h => by simp only [Set.mem_ofPred_eq] at h ⊢; omega)).toFinset.sup f

theorem le_sizeEnvelope {α : Type*} [UniqueEncoding Tree α] (f : α → ℕ) (x : α) :
    f x ≤ sizeEnvelope f (encode Tree x).size := by
  apply Finset.le_sup
  simp

theorem sizeEnvelope_le {α : Type*} [UniqueEncoding Tree α] (f : α → ℕ) (n k : ℕ)
    (h : ∀ x, (encode Tree x).size = n → f x ≤ k) : sizeEnvelope f n ≤ k := by
  apply Finset.sup_le
  intro x hx
  exact h x (by simpa using hx)

/-- Encoding a natural resource preserves a positive growth bound. -/
theorem Dominated.size_encode_nat {α : Type*} {f g : α → ℕ}
    (h : Dominated f g) (hg : ∀ x, 0 < g x) :
    Dominated (fun x => ⌜f x⌝ₜ.size) g :=
  ((h.const_mul_left 4).add_same (Dominated.const_of_pos 1 hg)).mono_left
    fun x => size_encode_nat_le (f x)

/-- A vector of indices below `k` stores at most `4 * k + 2` nodes for each entry. -/
theorem size_encode_finVector_fin_le {n k : ℕ} (v : FinVector (Fin k) n) :
    ⌜v⌝ₜ.size ≤ 4 * (n * k) + 2 * n + 1 := by
  have hw := size_encode_finVector_le v (4 * k + 1) (fun i => by
    have hi := (v.get i).isLt
    simpa only [encode_fin] using (size_encode_nat_le (v.get i).val).trans
      (by omega : 4 * (v.get i).val + 1 ≤ 4 * k + 1))
  have : n * (4 * k + 1 + 1) = 4 * (n * k) + 2 * n := by ring
  omega

/-- Passing to exact-size fibers is needed only at a complexity-class boundary. -/
theorem dominated_sizeEnvelope {α : Type*} [UniqueEncoding Tree α]
    {b : α → ℕ} {T : ℕ → ℕ} (h : Dominated b (fun x => T (encode Tree x).size)) :
    Dominated (sizeEnvelope b) T := by
  obtain ⟨C, hc⟩ := h
  refine ⟨C, fun n => ?_⟩
  apply sizeEnvelope_le
  intro x hx
  simpa only [hx] using hc x

end Complexity
