/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Classes.Functions
public import Complexity.Resources.TuringMachine
public import Complexity.Encoding.Polynomial
public import Complexity.Models.TreeMachine.Simulation.BitList
public import Mathlib.Data.Fintype.EquivFin

/-!
# Polynomial tree computations on bit-string representations

The existing tree-to-Turing compiler removes the list-tree representation at
both boundaries. Its polynomial time bound transports polynomial-time computations from the tree
model with the composite bit-list encoding to the Turing model on the original bit strings.

For a direct tree encoding, polynomial conversions before and after the tree
computation give the same inclusion. No converse simulation is assumed.
-/

@[expose] public section

namespace Complexity

namespace TreeMachine

open TreeMachine.Simulation

private theorem timeBound_polynomial (k : ℕ) (p : Polynomial ℕ) :
    ∃ q : Polynomial ℕ, ∀ n,
      BitList.timeBound k n (p.eval (4 * n + 1)) = q.eval n := by
  let q := p.comp (4 * Polynomial.X + 1)
  let r : Polynomial ℕ := 4 * Polynomial.X + 1
  refine ⟨(6 * r + 7) +
    q * (2 + Polynomial.C k * (50 * (r + Polynomial.C k + q + 1))) +
    (3 * (r + Polynomial.C k + q) + 3) +
    200 * (Polynomial.X + Polynomial.C k + q + 1), ?_⟩
  intro n
  simp [BitList.timeBound, Compiler.timeBound, Program.stepTime, q, r]

/-- For bit-string encodings stored as list trees, the existing tree simulator
gives polynomial time on the original bit strings, with no compatibility hypothesis. -/
theorem fp_subset_tm_comp {α β : Type*} [e : Encoding (List Bool) α]
    [d : Encoding (List Bool) β] :
    @FP Tree α β (bitListEncoding.toEncoding.comp e) (bitListEncoding.toEncoding.comp d)
      timeSpaceModel ⊆ FP TM.timeSpaceModel := by
  classical
  let : Encoding Tree α := bitListEncoding.toEncoding.comp e
  let : Encoding Tree β := bitListEncoding.toEncoding.comp d
  intro f hf
  obtain ⟨p, s, h⟩ := FP.exists_polynomial_bound hf
  obtain ⟨k, hk, Q, hQ, M, h⟩ := computableInTimeAndSpace_iff.mp h
  let : Fintype Q := Fintype.ofFinite Q
  let : FinEnum Q := FinEnum.ofEquiv (Fin (Fintype.card Q)) (Fintype.equivFin Q)
  let t := fun n => BitList.timeBound k n (p.eval (4 * n + 1))
  let s := fun n => BitList.spaceBound k n (p.eval (4 * n + 1))
  have hc : TM.Computes (BitList.compiler M) f t s := by
    rw [TM.computes_iff]
    intro xs a ha
    obtain ⟨b, hb, hm⟩ := h (Tree.encodeBitList xs) a
      ((Encoding.mem_comp_encode bitListEncoding e).2 ha)
    obtain ⟨ys, hy, hd⟩ := (Encoding.mem_comp_iff bitListEncoding.toEncoding d).1 hb
    obtain rfl := (UniqueEncoding.encode_of_mem_decode hy).symm
    have ht := p.monotone_eval_nat (Tree.size_encodeBitList_le xs)
    exact ⟨ys, hd, BitList.computesInTimeAndSpace M (hm.mono ht le_rfl)⟩
  obtain ⟨q, hq⟩ := timeBound_polynomial k p
  obtain ⟨b, hb⟩ := IsBigO.exists_pow q
  exact FP.ftime_subset b ⟨t, ⟨s, hc.computableInTimeAndSpace⟩,
    (IsBigO.of_le fun n => (hq n).le).trans hb⟩

/-- Only the input conversion from bits and the output conversion to bits are
needed to transport a tree computation to an ordinary bit-string machine. -/
theorem fp_subset_tm_of_conversions {α β : Type*}
    [e : Encoding (List Bool) α] [d : Encoding (List Bool) β]
    [r : Encoding Tree α] [s : Encoding Tree β]
    (hi : _root_.id ∈ @FP Tree α α (bitListEncoding.toEncoding.comp e) r timeSpaceModel)
    (ho : _root_.id ∈ @FP Tree β β s (bitListEncoding.toEncoding.comp d) timeSpaceModel) :
    FP (α := α) (β := β) timeSpaceModel ⊆ FP TM.timeSpaceModel := by
  intro f hf
  have h := @fp_comp α α β (bitListEncoding.toEncoding.comp e) r s _root_.id f hf hi
  have h' := @fp_comp α β β (bitListEncoding.toEncoding.comp e) s
    (bitListEncoding.toEncoding.comp d) (f ∘ _root_.id) _root_.id ho h
  exact fp_subset_tm_comp h'

/-- Polynomial compatibility of the input and output encodings turns every
polynomial-time tree computation into a polynomial-time Turing computation. -/
theorem fp_subset_tm {α β : Type*}
    [Encoding (List Bool) α] [Encoding (List Bool) β]
    [Encoding Tree α] [Encoding Tree β]
    [Encoding.PolytimeCompatible α] [Encoding.PolytimeCompatible β] :
    FP (α := α) (β := β) timeSpaceModel ⊆ FP TM.timeSpaceModel :=
  fp_subset_tm_of_conversions Encoding.PolytimeCompatible.fromBits
    Encoding.PolytimeCompatible.toBits

end TreeMachine

end Complexity
