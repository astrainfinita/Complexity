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
  simpa only [size_unroll, Nat.mul_assoc] using (step.unroll t).size_encode_le

end Complexity.Circuit

namespace Complexity.TreeProgram.Source

open Internal (HasProgramInO)

abbrev UnrollState :=
  Σ n, Σ t, Circuit .booleanAlgebra (n + 1) n × Circuit .booleanAlgebra (n + t) n

/-- Every source loop state has quadratic size in the numeric unfolding parameters. -/
theorem size_unrollState_le (n : ℕ) (step : Circuit .booleanAlgebra (n + 1) n)
    (t i : ℕ) (hi : i ≤ t) :
    ⌜(⟨n, i, step, step.unroll i⟩ : UnrollState)⌝ₜ.size ≤
      256 * (2 * n + t + (t + 1) * step.size + 2) ^ 2 := by
  let N := 2 * n + t + (t + 1) * step.size + 2
  have him := Nat.mul_le_mul_right step.size hi
  have hs := step.size_encode_le
  have hu := (step.unroll i).size_encode_le
  simp only [Circuit.size_unroll] at hu
  have hstep : ⌜step⌝ₜ.size ≤ 100 * N ^ 2 := hs.trans <| Nat.mul_le_mul_left 100 <| by
    rw [pow_two]; exact Nat.mul_le_mul (by dsimp [N]; nlinarith) (by dsimp [N]; nlinarith)
  have hcurrent : ⌜step.unroll i⌝ₜ.size ≤ 100 * N ^ 2 := hu.trans <| Nat.mul_le_mul_left 100 <| by
    rw [pow_two]; exact Nat.mul_le_mul (by dsimp [N]; nlinarith) (by dsimp [N]; nlinarith)
  have hn := size_encode_nat_le n
  have hi' := size_encode_nat_le i
  have hN := Nat.le_self_pow (by decide : 2 ≠ 0) N
  have hnN : 2 * n + i ≤ N := by dsimp [N]; omega
  change _ ≤ 256 * N ^ 2
  simp only [Sigma.encode_mk, size_encode_prod]
  omega

def unrollStep (x : UnrollState) : UnrollState :=
  ⟨x.1, x.2.1 + 1, x.2.2.1,
    (x.2.2.2.relabel Fin.castSucc).keepInputs.comp
      (x.2.2.1.relabel (Fin.snoc (Fin.natAdd (x.1 + (x.2.1 + 1)))
        (Fin.castAdd x.1 (Fin.last (x.1 + x.2.1)))))⟩

theorem iterate_unrollStep (n : ℕ) (step : Circuit .booleanAlgebra (n + 1) n) (t : ℕ) :
    unrollStep^[t] ⟨n, 0, step, Circuit.id _ n⟩ = ⟨n, t, step, step.unroll t⟩ := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', ih]; rfl

def unrollStepScale (x : UnrollState) :=
  2 * x.1 + x.2.1 + x.2.2.1.size + x.2.2.2.size + 2

theorem hasProgramIn_unrollStep : HasProgramIn unrollStep hole(⊢ program)
    IsO(fun x => unrollStepScale x ^ 8) IsO(fun x => unrollStepScale x ^ 4) := by
  abstract_hole program using programUnrollStep
  refine HasProgramInO.toHasProgramIn ?_
  -- `dominated` looks at three rounds of terms; the gate count of a layer takes a fourth.
  have hsize {n t : ℕ} (step : Circuit .booleanAlgebra (n + 1) n)
      (c : Circuit .booleanAlgebra (n + t) n) (f : Fin (n + 1) → Fin (n + t + 1 + n)) :
      ((c.relabel Fin.castSucc).keepInputs.comp (step.relabel f)).size = c.size + step.size := by
    simp
  fill_hole program in
    source_fun_prop (disch := dominated
      [unrollStepScale, relabelScale, keepScale, compScale, Circuit.size_relabel,
        Circuit.size_keepInputs, Circuit.size_comp, hsize]) using tabulate

abbrev UnrollInput := Σ n, Circuit .booleanAlgebra (n + 1) n × ℕ

def unrollInitial (x : UnrollInput) : ℕ × UnrollState :=
  (x.2.2, ⟨x.1, 0, x.2.1, Circuit.id _ x.1⟩)

def unrollScale (x : UnrollInput) :=
  2 * x.1 + x.2.2 + (x.2.2 + 1) * x.2.1.size + 2

theorem hasProgramIn_unrollInitial : HasProgramIn unrollInitial hole(⊢ program)
    IsO(fun x => unrollScale x ^ 2) IsO(fun x => unrollScale x ^ 2) := by
  abstract_hole program using programUnrollInitial
  refine HasProgramInO.toHasProgramIn ?_
  have : Dominated (fun x : UnrollInput => ⌜x.2.1⌝ₜ.size) (fun x => unrollScale x ^ 2) := by
    dominated [unrollScale, Nat.add_one_mul]
  fill_hole program in
    source_fun_prop (disch := dominated
      [unrollScale, Circuit.id]) using tabulate

/-- The result projection is selected independently of its eventual budget. -/
theorem hasProgramIn_unrollResult : HasProgramIn (fun x : UnrollState => x.2.2.2) hole(⊢ program)
    IsO(fun _ => 1) IsO(fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programUnrollResult
  fill_hole program in source_fun_prop

/-- The loop sums one step allowance per layer and retains a maximum space allowance. -/
theorem hasProgramIn_unroll :
    HasProgramIn (fun x : UnrollInput => x.2.1.unroll x.2.2) hole(⊢ program)
      IsO(fun x => unrollScale x ^ 9) IsO(fun x => unrollScale x ^ 4) := by
  abstract_hole program using programUnroll
  refine HasProgramInO.toHasProgramIn ?_
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
  fill_hole program in
    refine ((hasProgramIn_unrollInitial.toHasProgramInO.comp_dependent
      (hasProgramIn_unrollStep.toHasProgramInO.iterate.comp_dependent
        hasProgramIn_unrollResult.toHasProgramInO)).of_encode ?_).mono
      ?_ ?_
  · rintro ⟨n, step, t⟩
    exact (congrArg (fun s : UnrollState => ⌜s.2.2.2⌝ₜ) (iterate_unrollStep n step t)).symm
  all_goals dominated [unrollScale, unrollInitial]

/-- Unroll a circuit computed by a selected implementation. -/
theorem Internal.HasProgramInO.unroll {ρ : Type} [UniqueEncoding Tree ρ]
    {n t : ρ → ℕ} {step : (x : ρ) → Circuit .booleanAlgebra (n x + 1) (n x)}
    {r : Value → Code Value} {u q : ρ → ℕ}
    (h : HasProgramInO (fun x => (⟨n x, step x, t x⟩ : UnrollInput)) r u q) :
    HasProgramInO (fun x => (step x).unroll (t x)) (fun v => r v >>= programUnroll)
      (fun x => u x + unrollScale ⟨n x, step x, t x⟩ ^ 9)
      (fun x => max (q x) (unrollScale ⟨n x, step x, t x⟩ ^ 4)) :=
  h.comp_dependent hasProgramIn_unroll.toHasProgramInO

attribute [scoped fun_prop] HasProgramInO.unroll

end Complexity.TreeProgram.Source
