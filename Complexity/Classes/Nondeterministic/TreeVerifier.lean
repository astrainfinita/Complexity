/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Classes.Nondeterministic.Verifier
public import Complexity.Classes.StackMachine.TuringMachine
public import Complexity.Classes.TreeFunctions.Fuel
public import Complexity.Classes.TreeFunctions.Guard
public import Complexity.Classes.TreeFunctions.ToTree

/-!
# Nondeterministic polynomial time from a verifier

`NP.of_verifier`: a predicate `p` is in `NP .ntm` given a polynomial-time relation `R` on tree
machines that is sound for `p` without a witness-length restriction (`∀ a w, R (a, w) → p a`) and
complete with witnesses of code size within a polynomial bound `b`, provided the codes of the
witness type are recognized in polynomial time. The unrestricted soundness hypothesis is needed
because `TreeMachine.exists_fuel_mem_fp` only gives `b a ≤ (fuel a).length`, so guessed witnesses
may exceed `b a`. The relation is guarded into a relation on trees (`TreeMachine.p_guard`); a tree
is guessed as a bit string read by `BitList.toTree` (`nstack_of_tree_verifier`) by the stack
machine of `nstack_of_bits_verifier`; the stack machine is simulated by a Turing machine
(`StackMachine.np_eq_ntm`).
-/

@[expose] public section

namespace Complexity

open TreeProgram TreeProgram.Source

variable {α : Type*} [UniqueEncoding Tree α]

/-- A predicate is in `NP .nstack` given a polynomial-time relation on trees that is sound for all
trees (`hsound`) and complete with trees of size within a polynomial bound `b` (`hcomplete`). The
machine guesses the bit string of a tree's prefix code up to a polynomial-time fuel bounding `b`. -/
theorem nstack_of_tree_verifier {p : α → Prop} {R : α × Tree → Prop} (hR : R ∈ P .sizeCostTree)
    (b : α → ℕ) (hb : IsPoly (fun a => ⌜a⌝ₜ.size) b) (hsound : ∀ a t, R (a, t) → p a)
    (hcomplete : ∀ a, p a → ∃ t : Tree, t.size ≤ b a ∧ R (a, t)) :
    p ∈ NP .nstack := by
  obtain ⟨V, hV, hRV⟩ := hR
  obtain ⟨fuel, hfuel, hle⟩ := TreeMachine.exists_fuel_mem_fp b hb
  have hread : (fun x : α × List Bool => (x.1, BitList.toTree x.2)) ∈ FP .sizeCostTree := by
    model_fun_prop
  refine nstack_of_bits_verifier _ (TreeMachine.fp_comp hV hread) fuel hfuel fun a =>
    ⟨fun hp => ?_, fun ⟨_, _, hv⟩ => hsound a _ ((hRV _).1 hv)⟩
  obtain ⟨t, ht, hr⟩ := hcomplete a hp
  refine ⟨BitList.encodeTree t, ?_, ?_⟩
  · simpa using ht.trans (hle a)
  · simpa only [Function.comp_apply, BitList.toTree_encodeTree] using (hRV _).2 hr

/-- A predicate is in `NP .ntm` given a polynomial-time relation on tree machines that is sound for
all witnesses (`hsound`) and complete with witnesses of code size within a polynomial bound `b`
(`hcomplete`), when the codes of the witness type are recognized in polynomial time. -/
theorem NP.of_verifier {W : Type*} [UniqueEncoding Tree W] {p : α → Prop}
    (hW : (fun t : Tree => (decode W t).Dom) ∈ P .sizeCostTree)
    {R : α × W → Prop} (hR : R ∈ P .sizeCostTree)
    (b : α → ℕ) (hb : IsPoly (fun a => ⌜a⌝ₜ.size) b)
    (hsound : ∀ a w, R (a, w) → p a)
    (hcomplete : ∀ a, p a → ∃ w : W, ⌜w⌝ₜ.size ≤ b a ∧ R (a, w)) :
    p ∈ NP .ntm := by
  rw [← StackMachine.np_eq_ntm]
  refine nstack_of_tree_verifier (TreeMachine.p_guard hW hR) b hb
    (fun a _ ⟨w, _, hw⟩ => hsound a w hw) fun a hp => ?_
  obtain ⟨w, hw, hr⟩ := hcomplete a hp
  exact ⟨⌜w⌝ₜ, hw, w, rfl, hr⟩

end Complexity
