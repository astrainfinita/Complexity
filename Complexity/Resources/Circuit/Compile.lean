/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.Circuit.Compile
public import Complexity.Resources.Circuit.Basic

/-! # Depth bounds for gate replacement -/

@[expose] public section

namespace Complexity.Circuit

open FirstOrder FirstOrder.Language

variable {L L' : Language} {n m : ℕ}

/-- Gate implementations of depth at most `d` multiply propagated depth bounds by at most `d`. -/
theorem evalDepth_compile_le (c : Circuit L n m)
    (impl : ∀ {k}, L.Functions k → Circuit L' k 1) (d : ℕ)
    (hd : ∀ {k} (op : L.Functions k), (impl op).depth ≤ d)
    (x y : Fin n → ℕ) (hxy : ∀ i, x i ≤ d * y i) (j : Fin m) :
    (c.compile impl).evalDepth x j ≤ d * c.evalDepth y j := by
  induction c with
  | outputs select => exact hxy (select j)
  | @gate n m k op args next ih =>
      have hx : Finset.univ.sup (x ∘ args) ≤ d * Finset.univ.sup (y ∘ args) := by
        apply Finset.sup_le
        intro i _
        exact (hxy (args i)).trans
          (Nat.mul_le_mul_left d (Finset.le_sup (f := y ∘ args) (Finset.mem_univ i)))
      have hg : (impl op).evalDepth (x ∘ args) 0 ≤ d * (Finset.univ.sup (y ∘ args) + 1) := by
        have h := (impl op).evalDepth_le_evalDepth_add (x ∘ args) (fun _ => 0)
          (Finset.univ.sup (x ∘ args))
          (fun i => by simpa using Finset.le_sup (f := x ∘ args) (Finset.mem_univ i)) 0
        have hz := ((impl op).outputDepths_le_depth 0).trans (hd op)
        change (impl op).evalDepth (x ∘ args) 0 ≤ (impl op).outputDepths 0 + _ at h
        calc
          (impl op).evalDepth (x ∘ args) 0 ≤ d + d * Finset.univ.sup (y ∘ args) :=
            h.trans (Nat.add_le_add hz hx)
          _ = d * (Finset.univ.sup (y ∘ args) + 1) := by simp [Nat.mul_add, Nat.add_comm]
      simp only [compile, evalDepth, evalWith_comp, evalWith_keepInputs, evalWith_relabel,
        Fin.append_right_eq_snoc, evalWith_gate]
      apply ih
      intro i
      refine Fin.lastCases ?_ (fun t => ?_) i
      · simpa only [Fin.snoc_last, evalDepth] using hg
      · simpa only [Fin.snoc_castSucc] using hxy t

/-- If every implementation has depth at most `d`, compilation multiplies circuit depth
by at most `d`. Shared and unused wires are both covered by the bound. -/
theorem depth_compile_le (c : Circuit L n m)
    (impl : ∀ {k}, L.Functions k → Circuit L' k 1) (d : ℕ)
    (hd : ∀ {k} (op : L.Functions k), (impl op).depth ≤ d) :
    (c.compile impl).depth ≤ d * c.depth := by
  apply (depth_le_iff _ _).mpr
  intro j
  exact (c.evalDepth_compile_le impl d hd (fun _ => 0) (fun _ => 0) (by simp) j).trans
    (Nat.mul_le_mul_left d (c.outputDepths_le_depth j))

end Complexity.Circuit
