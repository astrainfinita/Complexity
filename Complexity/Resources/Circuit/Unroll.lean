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

namespace Complexity.Circuit

/-- The unfolding has polynomial encoded size in the numeric layer count. -/
theorem size_encode_unroll_numeric_le {n : ℕ}
    (step : Circuit .booleanAlgebra (n + 1) n) (t : ℕ) :
    ⌜step.unroll t⌝ₜ.size ≤
      100 * (t * step.size + n + 1) * (n + t + t * step.size + 1) := by
  simpa only [size_unroll] using (step.unroll t).size_encode_numeric_le

end Complexity.Circuit

namespace Complexity.TreeProgram.Source

abbrev UnrollState :=
  Σ n, Σ t, Circuit .booleanAlgebra (n + 1) n × Circuit .booleanAlgebra (n + t) n

/-- Every source loop state has quadratic size in the numeric unfolding parameters. -/
theorem size_unrollState_le (n : ℕ) (step : Circuit .booleanAlgebra (n + 1) n)
    (t i : ℕ) (hi : i ≤ t) :
    ⌜(⟨n, i, step, step.unroll i⟩ : UnrollState)⌝ₜ.size ≤
      256 * (2 * n + t + (t + 1) * step.size + 2) ^ 2 := by
  let N := 2 * n + t + (t + 1) * step.size + 2
  have him := Nat.mul_le_mul_right step.size hi
  have hs := step.size_encode_numeric_le
  have hu := (step.unroll i).size_encode_numeric_le
  simp only [Circuit.size_unroll] at hu
  have hstep : ⌜step⌝ₜ.size ≤ 100 * N ^ 2 := hs.trans (by
    simpa only [pow_two, Nat.mul_assoc] using Nat.mul_le_mul
      (Nat.mul_le_mul_left 100 (by dsimp [N]; nlinarith : step.size + n + 1 ≤ N))
      (by dsimp [N]; nlinarith : n + 1 + step.size + 1 ≤ N))
  have hcurrent : ⌜step.unroll i⌝ₜ.size ≤ 100 * N ^ 2 := hu.trans (by
    simpa only [pow_two, Nat.mul_assoc] using Nat.mul_le_mul
      (Nat.mul_le_mul_left 100 (by dsimp [N]; nlinarith : i * step.size + n + 1 ≤ N))
      (by dsimp [N]; nlinarith : n + i + i * step.size + 1 ≤ N))
  have hn := size_encode_nat_le n
  have hi' := size_encode_nat_le i
  have hN := Nat.le_self_pow (by decide : 2 ≠ 0) N
  have hnN : 2 * n + i ≤ N := by dsimp [N]; omega
  change _ ≤ 256 * N ^ 2
  simp only [Sigma.encode_mk, size_encode_prod]
  omega

def unrollStep (x : UnrollState) : UnrollState :=
  ⟨x.1, x.2.1 + 1, x.2.2.1,
    ((x.2.2.2).relabel Fin.castSucc).keepInputs.comp
      (x.2.2.1.relabel (Fin.snoc (Fin.natAdd (x.1 + (x.2.1 + 1)))
        (Fin.castAdd x.1 (Fin.last (x.1 + x.2.1)))))⟩

theorem iterate_unrollStep (n : ℕ) (step : Circuit .booleanAlgebra (n + 1) n) (t : ℕ) :
    unrollStep^[t] ⟨n, 0, step, Circuit.id _ n⟩ = ⟨n, t, step, step.unroll t⟩ := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', ih]; rfl

def unrollStepScale (x : UnrollState) :=
  2 * x.1 + x.2.1 + x.2.2.1.size + x.2.2.2.size + 2

def unrollStepImpl : Implementation unrollStep
    (fun x => unrollStepScale x ^ 8) (fun x => unrollStepScale x ^ 4) := by
  -- Every circuit of a step has quadratic encoded size in the scale.
  have circuit {n m : UnrollState → ℕ}
      (c : (x : UnrollState) → Circuit .booleanAlgebra (n x) (m x))
      (hn : ∀ x, n x ≤ 4 * unrollStepScale x := by intro x; dsimp [unrollStepScale]; omega)
      (hm : ∀ x, m x ≤ 4 * unrollStepScale x := by intro x; dsimp [unrollStepScale]; omega)
      (hc : ∀ x, (c x).size ≤ 4 * unrollStepScale x := by
        intro x
        try simp only [Circuit.size_relabel, Circuit.size_keepInputs, Circuit.size_comp]
        dsimp [unrollStepScale]; omega) :
      Dominated (fun x => ⌜c x⌝ₜ.size) (fun x => unrollStepScale x ^ 2) :=
    Dominated.size_encode_circuit c (.of_le_mul 4 hn) (.of_le_mul 4 hm) (.of_le_mul 4 hc)
      fun x => by dsimp [unrollStepScale]; omega
  have := circuit fun x : UnrollState => x.2.2.1
  have := circuit fun x : UnrollState => x.2.2.2
  have := circuit fun x : UnrollState => x.2.2.2.relabel Fin.castSucc
  have := circuit fun x : UnrollState => (x.2.2.2.relabel Fin.castSucc).keepInputs
  have := circuit fun x : UnrollState => x.2.2.1.relabel
    (Fin.snoc (Fin.natAdd (x.1 + (x.2.1 + 1))) (Fin.castAdd x.1 (Fin.last (x.1 + x.2.1))))
  have := circuit fun x : UnrollState => (x.2.2.2.relabel Fin.castSucc).keepInputs.comp
    (x.2.2.1.relabel
      (Fin.snoc (Fin.natAdd (x.1 + (x.2.1 + 1))) (Fin.castAdd x.1 (Fin.last (x.1 + x.2.1)))))
  source_fun_prop using tabulate
  all_goals try simp only [Sigma.size_encode_eq, Prod.size_encode_eq]
  all_goals dominated [unrollStepScale, relabelScale, keepScale, compScale, Circuit.size_relabel,
    Circuit.size_keepInputs, Circuit.size_comp]

abbrev UnrollInput := Σ n, Circuit .booleanAlgebra (n + 1) n × ℕ

def unrollInitial (x : UnrollInput) : ℕ × UnrollState :=
  (x.2.2, ⟨x.1, 0, x.2.1, Circuit.id _ x.1⟩)

def unrollScale (x : UnrollInput) :=
  2 * x.1 + x.2.2 + (x.2.2 + 1) * x.2.1.size + 2

def unrollInitialImpl : Implementation unrollInitial
    (fun x => unrollScale x ^ 2) (fun x => unrollScale x ^ 2) := by
  have := Dominated.size_encode_circuit (fun x : UnrollInput => x.2.1)
    (R := unrollScale) (.of_le fun x => by dsimp [unrollScale]; omega)
    (.of_le fun x => by dsimp [unrollScale]; omega)
    (.of_le fun x => by dsimp [unrollScale]; nlinarith) fun x => by dsimp [unrollScale]; omega
  source_fun_prop using tabulate
  all_goals try simp only [Sigma.size_encode_eq, Prod.size_encode_eq]
  all_goals dominated [unrollScale, Circuit.id]

/-- The result projection is selected independently of its eventual budget. -/
def unrollResultImpl : Implementation (fun x : UnrollState => x.2.2.2)
    (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  all_goals dominated

/-- The loop sums one step allowance per layer and retains a maximum space allowance. -/
def unrollImplementation :
    Implementation (fun x : UnrollInput => x.2.1.unroll x.2.2)
      (fun x => unrollScale x ^ 9) (fun x => unrollScale x ^ 4) := by
  have hR x : 0 < unrollScale x := by dsimp [unrollScale]; omega
  let I (x : UnrollInput) (r : ℕ) (y : UnrollState) :=
    ∃ i, i + r = x.2.2 ∧ y = ⟨x.1, i, x.2.1, x.2.1.unroll i⟩
  let Z := {z : UnrollInput × ℕ × UnrollState // I z.1 z.2.1 z.2.2}
  have hscale : Dominated (fun z : Z => unrollStepScale z.1.2.2) (fun z => unrollScale z.1.1) :=
    Dominated.of_le fun z => by
      rcases z with ⟨⟨⟨n, step, t⟩, r, y⟩, hz⟩
      change unrollStepScale y ≤ unrollScale ⟨n, step, t⟩
      dsimp only [I] at hz
      rcases hz with ⟨i, hi, rfl⟩
      have hm := Nat.mul_le_mul_right step.size (show i ≤ t by omega)
      simp only [unrollStepScale, unrollScale, Circuit.size_unroll, Nat.add_mul, Nat.one_mul]
      omega
  have hstate : Dominated (fun z : Z => ⌜z.1.2.2⌝ₜ.size) (fun z => unrollScale z.1.1 ^ 2) :=
    Dominated.of_le_mul 256 fun z => by
      rcases z with ⟨⟨⟨n, step, t⟩, r, y⟩, hz⟩
      change ⌜y⌝ₜ.size ≤ 256 * unrollScale ⟨n, step, t⟩ ^ 2
      dsimp only [I] at hz
      rcases hz with ⟨i, hi, rfl⟩
      exact size_unrollState_le n step t i (by omega)
  have hcount : Dominated (fun z : Z => z.1.2.1) (fun z => unrollScale z.1.1) :=
    Dominated.of_le fun z => by
      rcases z with ⟨⟨⟨n, step, t⟩, r, y⟩, hz⟩
      change r ≤ unrollScale ⟨n, step, t⟩
      dsimp only [I] at hz
      obtain ⟨i, hi, _⟩ := hz
      dsimp [unrollScale]
      omega
  have hcounter := Dominated.size_encode_nat hcount (fun z => hR z.1.1)
  have hsize : Dominated (fun z : Z => ⌜z.1.2⌝ₜ.size) (fun z => unrollScale z.1.1 ^ 4) := by
    simp only [Prod.size_encode_eq]
    dominated [unrollScale]
  let active (z : {z : UnrollInput × ℕ × UnrollState // I z.1 (z.2.1 + 1) z.2.2}) : Z :=
    ⟨(z.1.1, z.1.2.1 + 1, z.1.2.2), z.2⟩
  have hiter := Dominated.iterate_of_invariant (f := unrollStep)
    (t := fun y => unrollStepScale y ^ 8) (p := fun y => unrollStepScale y ^ 4) I
    (fun x => (unrollInitial x).1) (fun x => (unrollInitial x).2)
    (fun x => unrollScale x ^ 8) (fun x => unrollScale x ^ 4)
    (fun _ => ⟨0, by simp only [unrollInitial, Nat.zero_add], rfl⟩)
    (by rintro x r y ⟨i, hi, rfl⟩; exact ⟨i + 1, by omega, rfl⟩)
    (hcounter.le_pow (by decide)) hsize ((hscale.comp active).pow 8)
    ((hscale.comp active).pow 4)
  have hresult : Dominated (fun x : UnrollInput =>
      ⌜unrollStep^[(unrollInitial x).1] (unrollInitial x).2⌝ₜ.size) (fun x => unrollScale x ^ 2) :=
    Dominated.of_le_mul 256 fun x => by
      rcases x with ⟨n, step, t⟩
      dsimp only [unrollInitial]
      rw [iterate_unrollStep]
      exact size_unrollState_le n step t t le_rfl
  obtain ⟨htime, hpeak⟩ := hiter
  refine ((unrollInitialImpl.compDep
    (unrollStepImpl.iterate.compDep unrollResultImpl)).ofEncode ?_).mono ?_ ?_
  · rintro ⟨n, step, t⟩
    exact (congrArg (fun s : UnrollState => ⌜s.2.2.2⌝ₜ) (iterate_unrollStep n step t)).symm
  all_goals dominated [unrollScale, unrollInitial]

/-- Unroll a circuit computed by a selected implementation. -/
def Implementation.unroll {ρ : Type} [UniqueEncoding Tree ρ]
    {n t : ρ → ℕ} {step : (x : ρ) → Circuit .booleanAlgebra (n x + 1) (n x)} {u q : ρ → ℕ}
    (h : Implementation (fun x => (⟨n x, step x, t x⟩ : UnrollInput)) u q) :
    Implementation (fun x => (step x).unroll (t x))
      (fun x => u x + unrollScale ⟨n x, step x, t x⟩ ^ 9)
      (fun x => max (q x) (unrollScale ⟨n x, step x, t x⟩ ^ 4)) :=
  h.compDep unrollImplementation

attribute [scoped fun_prop] Implementation.unroll

end Complexity.TreeProgram.Source
