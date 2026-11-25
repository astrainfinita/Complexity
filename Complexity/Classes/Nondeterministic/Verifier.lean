/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Classes.Functions.Basic
public import Complexity.Classes.Nondeterministic.Basic
public import Complexity.Models.TreeMachine.Simulation.Verifier
public import Complexity.Resources.StackMachine.Program
public import Complexity.Resources.TreeMachine.Basic

/-!
# Nondeterministic polynomial time from a verifier of bit strings

`nstack_of_bits_verifier`: a predicate is in `NP .nstack` when it holds exactly where some bit
string no longer than a polynomial-time list of units, the fuel, is accepted by a polynomial-time
verifier. The machine is `bitsVerifier`: it keeps the input, computes the fuel by a tree machine,
guesses the bit string, and runs the verifier on a second tree machine.
-/

@[expose] public section

namespace Complexity

open TreeMachine.Simulation.Program Std.WP

variable {α : Type*} [UniqueEncoding Tree α]

/-- A predicate holding exactly where a polynomial-time verifier accepts some bit string no longer
than a polynomial-time list of units is in nondeterministic polynomial time on stack machines. -/
theorem nstack_of_bits_verifier {p : α → Prop}
    (U : α × List Bool → Bool) (hU : U ∈ FP .sizeCostTree)
    (fuel : α → List Unit) (hfuel : fuel ∈ FP .sizeCostTree)
    (h : ∀ a, p a ↔ ∃ bs : List Bool, bs.length ≤ (fuel a).length ∧ U (a, bs) = true) :
    p ∈ NP .nstack := by
  obtain ⟨T₁, S₁, -, hT₁, -, ⟨k₁, hk₁, Q₁, hQ₁, M₁, rfl⟩, hM₁⟩ := FP.exists_monotone_isPoly hfuel
  obtain ⟨T₂, S₂, hmono₂, hT₂, -, ⟨k₂, hk₂, Q₂, hQ₂, M₂, rfl⟩, hM₂⟩ := FP.exists_monotone_isPoly hU
  let : FinEnum Q₁ := FinEnum.ofFinite Q₁
  let : FinEnum Q₂ := FinEnum.ofFinite Q₂
  -- The time of the machine on an input of size `N`, with `N + k₁ + T₁ N` bounding the fuel.
  let B (N : ℕ) :=
    verifierTime (k₁ + k₂) N (N + k₁ + T₁ N) (T₁ N) (T₂ (N + 4 * (N + k₁ + T₁ N) + 2))
  have hfb : IsPoly (fun N ↦ N) fun N ↦ N + k₁ + T₁ N := (IsPoly.refl.add (.const _)).add hT₁
  have harg : IsPoly (fun N ↦ N) fun N ↦ N + 4 * (N + k₁ + T₁ N) + 2 :=
    (IsPoly.refl.add ((IsPoly.const 4).mul hfb)).add (.const 2)
  have hB : IsPoly (fun N ↦ N) B :=
    (((((IsPoly.const 85).mul .refl).add (.const _)).add ((IsPoly.const 40).mul hT₁)).add
      (.const 164)).add (((IsPoly.const 400).mul ((hfb.add (.const 1)).pow 2)).add
        ((((IsPoly.const 38).mul harg).add ((IsPoly.const 40).mul (hT₂.comp harg))).add
          (.const 12)))
  -- On the code of `a`: `M₁` computes the fuel, of length at most `⌜a⌝ₜ.size + k₁ + T₁`, and
  -- `M₂` computes `U (a, bs)` for each guess within the time `T₂` at a bound on its size.
  have hrun (a : α) :
      M₁.ComputesWithin ⌜a⌝ₜ ⌜fuel a⌝ₜ (T₁ ⌜a⌝ₜ.size) (S₁ ⌜a⌝ₜ.size) ∧
      (fuel a).length ≤ ⌜a⌝ₜ.size + k₁ + T₁ ⌜a⌝ₜ.size ∧ ∀ bs : List Bool,
        bs.length ≤ (fuel a).length → ∃ s, M₂.ComputesWithin (.pair ⌜a⌝ₜ ⌜bs⌝ₜ) ⌜U (a, bs)⌝ₜ
          (T₂ (⌜a⌝ₜ.size + 4 * (⌜a⌝ₜ.size + k₁ + T₁ ⌜a⌝ₜ.size) + 2)) s := by
    have h₁ : M₁.ComputesWithin ⌜a⌝ₜ ⌜fuel a⌝ₜ (T₁ ⌜a⌝ₜ.size) (S₁ ⌜a⌝ₜ.size) :=
      Encoding.Computes.iff_of_uniqueEncoding.mp hM₁ a
    have hy := h₁.output_size_le
    rw [size_encode_list_unit] at hy
    refine ⟨h₁, by omega, fun bs hbs ↦ ⟨_, (Encoding.Computes.iff_of_uniqueEncoding.mp hM₂
      (a, bs)).mono (hmono₂ ?_) le_rfl⟩⟩
    have hl := size_encode_list_bool_le bs
    simp only [encode_prod, Tree.size_pair, TimeSpaceModel.sizeCostTree_inputSize]
    omega
  have hd : TimeSpaceModel.nstack.NDecidableWithinBySize p B
      (fun N ↦ Fintype.card (TreeMachine.Simulation.Work (k₁ + k₂ + 3)) * B N) := by
    refine StackMachine.Program.nDecidableWithinByCode_of_spec (bitsVerifier M₁ M₂)
      (fun _ r ↦ B r.length) (fun a r ha ↦ ?_) fun a r ha hp ↦ ?_
    · obtain rfl := UniqueEncoding.mem_decode_iff.mp ha
      obtain ⟨h₁, hn, h₂⟩ := hrun a
      refine ⟨(spec_bitsVerifier_all M₁ M₂ h₁ hn (fun bs ↦ U (a, bs)) h₂).entails_wp_of_pre_post
        (fun c b ⟨hc, hb⟩ ↦ ⟨hc, by rw [hb, length_encode_rawWord]⟩) ?_⟩
      rintro _ s b ⟨bs, hbs, ho⟩
      exact ⟨U (a, bs), ho, fun hv ↦ (h a).2 ⟨bs, hbs, hv⟩⟩
    · obtain rfl := UniqueEncoding.mem_decode_iff.mp ha
      obtain ⟨h₁, hn, h₂⟩ := hrun a
      obtain ⟨bs, hbs, hv⟩ := (h a).1 hp
      obtain ⟨s, h₂⟩ := h₂ bs hbs
      exact ⟨(spec_bitsVerifier_any M₁ M₂ h₁ hn bs hbs (hv ▸ h₂)).entails_wp_of_pre
        fun c b ⟨hc, hb⟩ ↦ ⟨hc, by rw [hb, length_encode_rawWord]⟩⟩
  exact NP.of_isPoly hd.mem_ntime hB

end Complexity
