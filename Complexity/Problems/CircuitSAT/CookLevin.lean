/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.StackMachine.Circuit
public import Complexity.Models.StackMachine.Deterministic
public import Complexity.Problems.CircuitSAT.Basic
public import Complexity.Classes.Nondeterministic.Basic
public import Complexity.Classes.Reductions.Basic
public import Complexity.Resources.Nondeterministic.Basic
import Complexity.Classes.StackMachine.TuringMachine

/-!
# Bounded nondeterministic stack runs as satisfiability instances

For a binary-choice stack machine computing a multiset of outputs within `t` steps, membership of
an output is satisfiability of the `t`-step run circuit
(`StackMachine.ComputesWithinWith.mem_iff_circuitSAT`), and when `t` is polynomial in the input
length, so is the gate count (`StackMachine.isPoly_size_runCircuit`).

Through the nondeterministic Turing-to-stack simulation (`StackMachine.np_eq_ntm`) and
`NP.mem_iff_isPoly`, any function class `C` containing every stack machine's polynomial-step run
circuit map witnesses `ManyOneReducible C p CircuitSAT` for every `p ∈ NP .ntm`
(`NP.manyOneReducible_circuitSAT`). The generator placing these maps in `FP .sizeCostTree` is not
built yet, so this is not yet a polynomial-time reduction.
-/

public section

namespace Complexity

namespace StackMachine

/-- If a binary-choice stack machine computes `outs` within `t` steps, then `w` appears among its
branch outputs exactly when the `t`-step run circuit accepting `w` is satisfiable. `[Fintype κ]` is
kept separate from `[FinEnum κ]` so callers whose `ComputesWithinWith` hypothesis uses another
`Fintype` instance (such as `Fin.fintype`) do not need it to agree with the one derived from
`FinEnum`. -/
theorem ComputesWithinWith.mem_iff_circuitSAT {κ Q : Type} [Fintype κ] [FinEnum κ] [FinEnum Q]
    {M : StackMachine BinaryChoice κ Bool Q} {xs w : List Bool} {outs : Multiset (List Bool)}
    {t s : ℕ} (h : M.ComputesWithinWith Multiset xs outs t s) :
    w ∈ outs ↔ CircuitSAT ⟨t, M.runCircuit xs w t⟩ := by
  obtain ⟨hb, n, hn⟩ := h
  have hht : ∀ c ∈ returns (M.runWith Multiset xs t), M.Halted c :=
    M.forall_halted_of_forall_length_le xs fun p hp ↦ by
      simpa only [Controller.History.length_snd] using (hb p hp).1
  have hhn : ∀ c ∈ returns (M.runWith Multiset xs n), M.Halted c := fun c hc ↦
    let ⟨_, _, hH, _⟩ := hn.exists_mem_of_mem_left hc
    hH
  have hrun : M.runWith Multiset xs t = M.runWith Multiset xs n :=
    (M.runWith_eq_of_forall_halted Multiset xs hht (le_max_left t n)).symm.trans
      (M.runWith_eq_of_forall_halted Multiset xs hhn (le_max_right t n))
  rw [← hrun] at hn
  rw [CircuitSAT, M.exists_eval_runCircuit_iff xs w t]
  constructor
  · exact fun hw ↦ hn.exists_mem_of_mem_right (Multiset.mem_returns.2 hw)
  · rintro ⟨c, hc, _, ho⟩
    obtain ⟨y, hy, _, hoy⟩ := hn.exists_mem_of_mem_left hc
    obtain rfl : y = w := List.toArray_inj (hoy.symm.trans ho)
    exact Multiset.mem_returns.1 hy

/-- When the step budget is polynomial in the input length, the gate count of `runCircuit` is
polynomial in the input length. -/
theorem isPoly_size_runCircuit {κ Q : Type*} [FinEnum κ] [FinEnum Q]
    (M : StackMachine BinaryChoice κ Bool Q) (w : List Bool) {t : List Bool → ℕ}
    (ht : IsPoly List.length t) :
    IsPoly List.length fun xs ↦ (M.runCircuit xs w (t xs)).size :=
  ((ht.add (.const 1)).mul ((IsPoly.refl.add ht).add (.const 1))).of_dominated
    (M.dominated_size_runCircuit.comp fun xs ↦ (xs, w, t xs))

end StackMachine

/-- If a function class `C` contains every finite binary-choice stack machine's run-circuit map at
explicit polynomial step counts `c * (⌜a⌝₂.length + 1) ^ d`, then every predicate in `NP .ntm`
many-one reduces to `CircuitSAT` in `C`. -/
theorem NP.manyOneReducible_circuitSAT {α : Type*} [UniqueEncoding (RawWord Bool) α]
    {C : Set (α → Σ n, Circuit .booleanAlgebra n 1)}
    (hC : ∀ (κ Q : Type) [FinEnum κ] [FinEnum Q] (M : StackMachine BinaryChoice κ Bool Q)
      (c d : ℕ),
      (fun a ↦ ⟨_, M.runCircuit ⌜a⌝₂.toList ⌜true⌝₂.toList (c * (⌜a⌝₂.length + 1) ^ d)⟩) ∈ C)
    {p : α → Prop} (hp : p ∈ NP .ntm) :
    ManyOneReducible C p CircuitSAT := by
  rw [← StackMachine.np_eq_ntm, NP.mem_iff_isPoly] at hp
  obtain ⟨t, s, ⟨R, ⟨κ, _, Q, _, M, rfl⟩, hdec⟩, d, c, hc⟩ := hp
  have := Fintype.ofFinite Q
  let _ : FinEnum κ := FinEnum.ofEquiv _ (Fintype.equivFin κ)
  let _ : FinEnum Q := FinEnum.ofEquiv _ (Fintype.equivFin Q)
  refine ⟨_, hC κ Q M c d, fun a ↦ ?_⟩
  obtain ⟨bs, hcomp, hacc⟩ :=
    Encoding.NDecides.iff_of_uniqueOutput.1 hdec a ⌜a⌝₂ (UniqueEncoding.mem_decode_iff.2 rfl)
  have hmem : ⌜true⌝₂.toList ∈ (RawWord.toList <$> bs.map (encode (RawWord Bool))) ↔ true ∈ bs := by
    simp only [Multiset.fmap_def, Multiset.map_map, Function.comp_def, Multiset.mem_map,
      RawWord.toList_inj, UniqueEncoding.encode_inj, exists_eq_right]
  have hle : t ⌜a⌝₂.length ≤ c * (⌜a⌝₂.length + 1) ^ d := by
    simpa only [Nat.nsmul_eq_mul] using hc ⌜a⌝₂.length
  exact hacc.symm.trans (hmem.symm.trans ((hcomp.mono hle le_rfl).mem_iff_circuitSAT))

end Complexity
