/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Resources.Circuit.Composition
public import Complexity.Models.Circuit.Unroll

/-! # A certified generator for bounded circuit unfolding

The loop carries its layer index with the dependent circuit, and sums the cost of each layer.
The number of layers is a numeric parameter, not its binary representation length.
-/

@[expose] public section

open Complexity TreeProgram

namespace Complexity.TreeProgram.Source

open Internal (HasProgramInO)

/-- The loop state of `Circuit.unroll`: the width `n`, the number `t` of layers so far, the step
circuit, and the unfolding by `t` layers. -/
abbrev UnrollState :=
  Σ n, Σ t, Circuit .booleanAlgebra (n + 1) n × Circuit .booleanAlgebra (n + t) n

/-- Add one layer, counting it: `Circuit.unrollLayer` with its wire tables as `FinVector`s. -/
def unrollStep (x : UnrollState) : UnrollState :=
  ⟨x.1, x.2.1 + 1, x.2.2.1,
    (x.2.2.2.relabel ((FinVector.finRange (x.1 + x.2.1)).map Fin.castSucc).get).keepInputs.comp
      (x.2.2.1.relabel (((FinVector.finRange x.1).map (Fin.natAdd (x.1 + (x.2.1 + 1)))).push
        (Fin.castAdd x.1 (Fin.last (x.1 + x.2.1)))).get)⟩

theorem iterate_unrollStep (n : ℕ) (step : Circuit .booleanAlgebra (n + 1) n) (t : ℕ) :
    unrollStep^[t] ⟨n, 0, step, Circuit.id _ n⟩ = ⟨n, t, step, step.unroll t⟩ := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', ih]; rfl

/-- The numeric scale of the growth of one layer: the width, the layer count and the gate counts of
both circuits. -/
def unrollStepScale (x : UnrollState) :=
  2 * x.1 + x.2.1 + x.2.2.1.size + x.2.2.2.size + 2

/-- One layer, polynomial in `unrollStepScale`. -/
theorem hasProgramIn_unrollStep : HasProgramIn unrollStep hole(⊢ program)
    (IsPoly unrollStepScale) (IsPoly unrollStepScale) := by
  abstract_hole program using programUnrollStep
  fill_hole program in
    source_fun_prop (disch := dominated [unrollStepScale, relabelScale, keepScale, compScale,
      Circuit.size_relabel, Circuit.size_keepInputs, Circuit.size_comp])

/-- The arguments of `Circuit.unroll`: the width, the step circuit and the number of layers. -/
abbrev UnrollInput := Σ n, Circuit .booleanAlgebra (n + 1) n × ℕ

/-- Start the unfolding loop: the number of layers to add, and the state with no layer, holding the
identity circuit, which outputs the `FinVector` of all inputs. -/
def unrollInitial (x : UnrollInput) : ℕ × UnrollState :=
  (x.2.2, ⟨x.1, 0, x.2.1, .outputs (FinVector.finRange x.1).get⟩)

/-- The numeric scale of the growth of `Circuit.unroll`: the width, the number `t` of layers and
`t + 1` times the gate count of the step. -/
def unrollScale (x : UnrollInput) :=
  2 * x.1 + x.2.2 + (x.2.2 + 1) * x.2.1.size + 2

/-- Every source loop state, after at most `t` layers, is polynomial in `unrollScale`. -/
theorem isPoly_size_unrollState :
    IsPoly (fun z : {p : UnrollInput × ℕ // p.2 ≤ p.1.2.2} => unrollScale z.1.1)
      fun z => ⌜(⟨z.1.1.1, z.1.2, z.1.1.2.1, z.1.1.2.1.unroll z.1.2⟩ : UnrollState)⌝ₜ.size := by
  dominated [unrollScale, Circuit.size_unroll, Nat.add_one_mul]

theorem hasProgramIn_unrollInitial : HasProgramIn unrollInitial hole(⊢ program)
    (IsPoly unrollScale) (IsPoly unrollScale) := by
  abstract_hole program using programUnrollInitial
  fill_hole program in
    source_fun_prop (disch := dominated [unrollScale, Circuit.size_outputs, Nat.add_one_mul])

/-- The result projection is selected independently of its eventual budget. -/
theorem hasProgramIn_unrollResult : HasProgramIn (fun x : UnrollState => x.2.2.2) hole(⊢ program)
    IsO(fun _ => 1) IsO(fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programUnrollResult
  fill_hole program in source_fun_prop

/-- The loop sums one step allowance per layer and retains a maximum space allowance; every
reachable state is polynomial in `unrollScale`. -/
theorem hasProgramIn_unroll : HasProgramIn (fun x : UnrollInput => x.2.1.unroll x.2.2)
    hole(⊢ program) (IsPoly unrollScale) (IsPoly unrollScale) := by
  abstract_hole program using programUnroll
  let I (x : UnrollInput) (r : ℕ) (y : UnrollState) :=
    ∃ i, i + r = x.2.2 ∧ y = ⟨x.1, i, x.2.1, x.2.1.unroll i⟩
  -- A state at counter `r` is the unfolding by `t - r` layers.
  have hstate : IsPoly (fun z : {z : UnrollInput × ℕ × UnrollState // I z.1 z.2.1 z.2.2} =>
      unrollScale z.1.1) fun z => ⌜z.1.2⌝ₜ.size := by
    have h := isPoly_size_unrollState.comp (h := fun z : {z : UnrollInput × ℕ × UnrollState //
      I z.1 z.2.1 z.2.2} => ⟨(z.1.1, z.1.1.2.2 - z.1.2.1), Nat.sub_le _ _⟩) .refl
    have hr : IsPoly (fun z : {z : UnrollInput × ℕ × UnrollState // I z.1 z.2.1 z.2.2} =>
        unrollScale z.1.1) fun z => 4 * z.1.1.2.2 + 1 := by dominated [unrollScale]
    refine (((IsPoly.const 1).add hr).add h).of_dominated (Dominated.of_le fun z => ?_)
    rcases z with ⟨⟨⟨n, step, t⟩, r, y⟩, hz⟩
    dsimp only [I] at hz
    rcases hz with ⟨i, hi, rfl⟩
    obtain rfl : i = t - r := by omega
    have := size_encode_nat_le r
    simp only [Prod.size_encode_eq]
    omega
  have hscale : IsPoly (fun z : {z : UnrollInput × ℕ × UnrollState // I z.1 (z.2.1 + 1) z.2.2} =>
      unrollScale z.1.1) fun z => unrollStepScale z.1.2.2 :=
    IsPoly.refl.of_dominated (Dominated.of_le fun z => by
      rcases z with ⟨⟨⟨n, step, t⟩, r, y⟩, hz⟩
      dsimp only [I] at hz
      rcases hz with ⟨i, hi, rfl⟩
      have hm := Nat.mul_le_mul_right step.size (show i ≤ t by omega)
      simp only [unrollStepScale, unrollScale, Circuit.size_unroll, Nat.add_mul, Nat.one_mul]
      omega)
  have hiter := IsPoly.iterate_of_invariant (f := fun _ => unrollStep)
    (t := fun _ => hasProgramIn_unrollStep.time) (p := fun _ => hasProgramIn_unrollStep.peak) I
    (fun x => (unrollInitial x).1) (fun x => (unrollInitial x).2) unrollScale
    (fun _ => ⟨0, by simp only [unrollInitial, Nat.zero_add], rfl⟩)
    (by rintro x r y ⟨i, hi, rfl⟩; exact ⟨i + 1, by omega, rfl⟩)
    (by dominated [unrollScale, unrollInitial]) hstate
    (hasProgramIn_unrollStep.isPoly_time.comp hscale)
    (hasProgramIn_unrollStep.isPoly_peak.comp hscale)
  have hresult : IsPoly unrollScale fun x : UnrollInput =>
      ⌜unrollStep^[(unrollInitial x).1] (unrollInitial x).2⌝ₜ.size := by
    refine (isPoly_size_unrollState.comp (h := fun x => ⟨(x, x.2.2), le_rfl⟩) .refl).of_dominated
      (Dominated.of_le fun ⟨n, step, t⟩ => ?_)
    exact (congrArg (fun s : UnrollState => ⌜s⌝ₜ.size) (iterate_unrollStep n step t)).le
  have := hiter.1
  have := hiter.2
  fill_hole program in
    refine ((hasProgramIn_unrollInitial.hasProgramInO.comp_dependent
      (hasProgramIn_unrollStep.hasProgramInO.iterate.comp_dependent
        hasProgramIn_unrollResult.toHasProgramInO)).of_encode ?_).hasProgramIn ?_ ?_
  · rintro ⟨n, step, t⟩
    exact (congrArg (fun s : UnrollState => ⌜s.2.2.2⌝ₜ) (iterate_unrollStep n step t)).symm
  · dominated
  · dominated

/-- Unroll a circuit computed by a selected implementation. -/
theorem Internal.HasProgramInO.unroll {ρ : Type} [UniqueEncoding Tree ρ]
    {n t : ρ → ℕ} {step : (x : ρ) → Circuit .booleanAlgebra (n x + 1) (n x)}
    {r : Value → Code Value} {u q : ρ → ℕ}
    (h : HasProgramInO (fun x => (⟨n x, step x, t x⟩ : UnrollInput)) r u q) :
    HasProgramInO (fun x => (step x).unroll (t x)) (fun v => r v >>= programUnroll)
      (fun x => u x + hasProgramIn_unroll.time ⟨n x, step x, t x⟩)
      (fun x => max (q x) (hasProgramIn_unroll.peak ⟨n x, step x, t x⟩)) :=
  h.comp_dependent hasProgramIn_unroll.hasProgramInO

attribute [fun_prop] HasProgramInO.unroll

end Complexity.TreeProgram.Source
