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

noncomputable def unrollStepImpl : Implementation unrollStep := by source_fun_prop using tabulate

@[simps] def unrollStepBounds : Bounds UnrollState :=
  let N (x : UnrollState) := 2 * x.1 + x.2.1 + x.2.2.1.size + x.2.2.2.size + 2
  ⟨fun x => 1000000000000000000000000000000 * N x ^ 9,
   fun x => 10000000000000000000000000 * N x ^ 4⟩
theorem unrollStep_realizes : Realizes unrollStep unrollStepBounds := by
  refine unrollStepImpl.realizes.mono ?_
  rintro ⟨n, t, step, current⟩
  simp only [unrollStepImpl, source_bounds]
  simp only [compBounds, pairBounds, relabelBounds, keepBounds,
    circuitCompBounds, unrollStepBounds, identityBounds, Sigma.encode_mk, size_encode_prod,
    Circuit.size_relabel, Circuit.size_keepInputs, Tree.encode_self]
  dsimp +instances only
  let N := 2 * n + t + step.size + current.size + 2
  change _ ≤ 1000000000000000000000000000000 * N ^ 9 ∧
    _ ≤ 10000000000000000000000000 * N ^ 4
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hN₂ := Nat.le_self_pow (by decide : 2 ≠ 0) N
  have h₁₂ : 1 ≤ N ^ 2 := Nat.one_le_pow 2 _ hN
  have h₂₄ : N ^ 2 ≤ N ^ 4 := Nat.pow_le_pow_right hN (by decide)
  have h₃₄ : N ^ 3 ≤ N ^ 4 := Nat.pow_le_pow_right hN (by decide)
  have h₂₇ : N ^ 2 ≤ N ^ 7 := Nat.pow_le_pow_right hN (by decide)
  have h₇₉ : N ^ 7 ≤ N ^ 9 := Nat.pow_le_pow_right hN (by decide)
  have h₈₉ : N ^ 8 ≤ N ^ 9 := Nat.pow_le_pow_right hN (by decide)
  have hnN : n ≤ N := by dsimp [N]; omega
  have htN : t ≤ N := by dsimp [N]; omega
  have hntN : n + t + 1 ≤ N := by dsimp [N]; omega
  have hn := size_encode_nat_le n
  have ht := size_encode_nat_le t
  have hn' := size_encode_nat_le (n + 1)
  have ht' := size_encode_nat_le (t + 1)
  have hnt := size_encode_nat_le (n + t)
  have hnt' := size_encode_nat_le (n + t + 1)
  have hnt'' := size_encode_nat_le (n + (t + 1))
  have hntn := size_encode_nat_le (n + t + 1 + n)
  have hbn := (length_le_codeSize n.bits).trans hn
  have hbt := (length_le_codeSize t.bits).trans ht
  have hbnt := (length_le_codeSize (n + t).bits).trans hnt
  have wireSize {q k : ℕ} (hq : q ≤ 2 * N) (hk : k ≤ 2 * N) (w : Fin q → Fin k) :
      ⌜w⌝ₜ.size ≤ 32 * N ^ 2 := by
    have hw := size_encode_fin_function_le w (4 * k + 1) (fun i => by
      have := size_encode_nat_le (w i).val
      have := (w i).isLt
      simpa only [encode_fin] using (by omega : ⌜(w i).val⌝ₜ.size ≤ 4 * k + 1))
    have hp := Nat.mul_le_mul hq (by omega : 4 * k + 1 + 1 ≤ 10 * N)
    nlinarith only [hw, hp, hN₂, h₁₂]
  have circuitSize {a b : ℕ} (c : Circuit .booleanAlgebra a b)
      (h₁ : c.size + b + 1 ≤ N) (h₂ : a + c.size + 1 ≤ N) :
      ⌜c⌝ₜ.size ≤ 100 * N ^ 2 := c.size_encode_numeric_le.trans (by
    simpa only [pow_two, Nat.mul_assoc] using Nat.mul_le_mul
      (Nat.mul_le_mul_left 100 h₁) h₂)
  have hs := circuitSize step (by dsimp [N]; omega) (by dsimp [N]; omega)
  have hc := circuitSize current (by dsimp [N]; omega) (by dsimp [N]; omega)
  let wires : Fin (n + 1) → Fin (n + t + 1 + n) :=
    Fin.snoc (Fin.natAdd (n + (t + 1))) (Fin.castAdd n (Fin.last (n + t)))
  let a := current.relabel Fin.castSucc
  let b := a.keepInputs
  let d := step.relabel wires
  have ha := circuitSize a
    (by simp only [a, Circuit.size_relabel]; dsimp [N]; omega)
    (by simp only [a, Circuit.size_relabel]; dsimp [N]; omega)
  have hb := circuitSize b
    (by simp only [a, b, Circuit.size_relabel, Circuit.size_keepInputs]; dsimp [N]; omega)
    (by simp only [a, b, Circuit.size_relabel, Circuit.size_keepInputs]; dsimp [N]; omega)
  have hd := circuitSize d
    (by simp only [d, Circuit.size_relabel]; dsimp [N]; omega)
    (by simp only [d, Circuit.size_relabel]; dsimp [N]; omega)
  have hout := circuitSize (b.comp d)
    (by simp only [a, b, d, Circuit.size_relabel, Circuit.size_keepInputs, Circuit.size_comp]
        dsimp [N]; omega)
    (by simp only [a, b, d, Circuit.size_relabel, Circuit.size_keepInputs, Circuit.size_comp]
        dsimp [N]; omega)
  have hw₁ := wireSize (by omega) (by omega) (Fin.castSucc : Fin (n + t) → Fin (n + t + 1))
  have hw₂ := wireSize (by omega) (by dsimp [N]; omega)
    (Fin.natAdd (n + (t + 1)) : Fin n → Fin (n + t + 1 + n))
  have hw₃ := wireSize (by omega) (by dsimp [N]; omega) wires
  have relabelBudget (g q : ℕ) (hg : g + 1 ≤ N) (hq : q ≤ 2 * N) :
      300000000000000 * (g + 1) * q ^ 6 + 20 ≤ 1000000000000000000 * N ^ 7 ∧
        1000000000000 * q ^ 4 + (g + 1) * (128 * q ^ 2 + 1) + 1 ≤
          1000000000000000 * N ^ 4 := by
    have hq₂ := pow_le_pow_left' hq 2
    have hq₄ := pow_le_pow_left' hq 4
    have hq₆ := pow_le_pow_left' hq 6
    norm_num only [mul_pow, Nat.reducePow] at hq₂ hq₄ hq₆
    have htime : (g + 1) * q ^ 6 ≤ 64 * N ^ 7 := calc
      _ ≤ N * (64 * N ^ 6) := Nat.mul_le_mul hg hq₆
      _ = _ := by rw [pow_succ N 6]; ac_rfl
    have hstack : (g + 1) * (128 * q ^ 2 + 1) ≤ 513 * N ^ 3 := calc
      _ ≤ N * (513 * N ^ 2) := Nat.mul_le_mul hg (by omega)
      _ = _ := by rw [pow_succ N 2]; ac_rfl
    rw [Nat.mul_assoc]
    omega
  have hra := relabelBudget current.size
    (n + t + n + (n + t + 1) + 2 * current.size + 1)
    (by dsimp [N]; omega) (by dsimp [N]; omega)
  have hrd := relabelBudget step.size
    (n + 1 + n + (n + t + 1 + n) + 2 * step.size + 1)
    (by dsimp [N]; omega) (by dsimp [N]; omega)
  have hk : n + t + 1 + n + 2 * current.size + 1 ≤ 2 * N := by dsimp [N]; omega
  have hcomp : n + t + 1 + (n + t + 1 + n) + n +
      2 * (current.size + step.size) + 1 ≤ 2 * N := by dsimp [N]; omega
  have hk₄ := pow_le_pow_left' hk 4
  have hk₉ := pow_le_pow_left' hk 9
  have hc₄ := pow_le_pow_left' hcomp 4
  have hc₈ := pow_le_pow_left' hcomp 8
  norm_num only [mul_pow, Nat.reducePow] at hk₄ hk₉ hc₄ hc₈
  have hpn := pow_le_pow_left' (by omega : n + 1 ≤ N) 2
  have hpnt := pow_le_pow_left' hntN 2
  have hrn := (size_encode_range_le n).trans (Nat.mul_le_mul_left 3 hpn)
  have hrnt := (size_encode_range_le (n + t)).trans (Nat.mul_le_mul_left 3 hpnt)
  have hsum : ((List.finRange n).map (fun i =>
      2 + (3 + (28 * t.bits.length + 25) + 1) +
        (2000 * (1 + ⌜n⌝ₜ.size + ⌜t + 1⌝ₜ.size) + 10020) + (1 + 1) +
        (2000 * (1 + ⌜n + (t + 1)⌝ₜ.size + ⌜i.val⌝ₜ.size) + 10020) + 0)).sum ≤
          500000 * N ^ 2 := by
    have h := List.sum_le_sum (l := List.finRange n) (g := fun _ => 500000 * N)
      (fun i _ => show 2 + (3 + (28 * t.bits.length + 25) + 1) +
        (2000 * (1 + ⌜n⌝ₜ.size + ⌜t + 1⌝ₜ.size) + 10020) + (1 + 1) +
        (2000 * (1 + ⌜n + (t + 1)⌝ₜ.size + ⌜i.val⌝ₜ.size) + 10020) + 0 ≤ 500000 * N from by
          have := size_encode_nat_le i.val
          have := i.isLt
          omega)
    simp only [List.map_const', List.sum_replicate, List.length_finRange, smul_eq_mul] at h
    apply h.trans
    calc
      _ = 500000 * (n * N) := by ring
      _ ≤ 500000 * (N * N) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right N hnN)
      _ = 500000 * N ^ 2 := by ring
  simp only [a, b, d, wires] at ha hb hd hout hw₃
  simp only [tabulateBounds, compBounds, pairBounds, identityBounds, Sigma.encode_mk,
    size_encode_prod, encode_fin, Fin.val_last, Fin.val_castAdd,
    Fin.val_castSucc, List.map_const', List.sum_replicate, List.length_finRange,
    smul_eq_mul, ← max_assoc, max_le_iff, foldr_max_le]
  dsimp +instances only [id] at *
  (repeat' apply And.intro) <;> first
  | omega
  | (change 1 + (1 + ⌜n⌝ₜ.size + (1 + ⌜t⌝ₜ.size +
       (1 + ⌜step⌝ₜ.size + ⌜current⌝ₜ.size))) + _ ≤ _
     omega)
  | (intro i hi
     have hcode := size_encode_nat_le i.val
     have hlt := i.isLt
     have hsumcode := size_encode_nat_le (n + (t + 1) + i.val)
     (repeat' apply And.intro) <;> omega)

abbrev UnrollInput := Σ n, Circuit .booleanAlgebra (n + 1) n × ℕ

def unrollInitial (x : UnrollInput) : ℕ × UnrollState :=
  (x.2.2, ⟨x.1, 0, x.2.1, Circuit.id _ x.1⟩)

@[simps] def unrollInitialBounds : Bounds UnrollInput :=
  let N (x : UnrollInput) := 2 * x.1 + x.2.2 + (x.2.2 + 1) * x.2.1.size + 2
  ⟨fun x => 1000000 * N x ^ 2, fun x => 1000000 * N x ^ 2⟩
theorem unrollInitial_realizes : Realizes unrollInitial unrollInitialBounds := by
  refine Realizes.mono (by source_fun_prop using tabulate) ?_
  rintro ⟨n, step, t⟩
  simp only [unrollInitialBounds, tabulateBounds,
    compBounds, pairBounds, identityBounds, Sigma.encode_mk, size_encode_prod,
    Tree.encode_self, Circuit.id, Circuit.encode_outputs, size_encode_unit]
  dsimp +instances only
  let N := 2 * n + t + (t + 1) * step.size + 2
  change _ ≤ 1000000 * N ^ 2 ∧ _ ≤ 1000000 * N ^ 2
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hN₂ := Nat.le_self_pow (by decide : 2 ≠ 0) N
  have h₁₂ : 1 ≤ N ^ 2 := Nat.one_le_pow 2 _ hN
  have hnN : n ≤ N := by dsimp [N]; omega
  have htN : t ≤ N := by dsimp [N]; omega
  have hg : step.size ≤ (t + 1) * step.size := by rw [Nat.add_mul, Nat.one_mul]; omega
  have hn := size_encode_nat_le n
  have ht := size_encode_nat_le t
  have hz := size_encode_nat_le 0
  have hs : ⌜step⌝ₜ.size ≤ 100 * N ^ 2 := step.size_encode_numeric_le.trans (by
    simpa only [pow_two, Nat.mul_assoc] using Nat.mul_le_mul
      (Nat.mul_le_mul_left 100 (by dsimp [N]; omega : step.size + n + 1 ≤ N))
      (by dsimp [N]; omega : n + 1 + step.size + 1 ≤ N))
  have hp := pow_le_pow_left' (by dsimp [N]; omega : n + 1 ≤ N) 2
  have hr := (size_encode_range_le n).trans (Nat.mul_le_mul_left 3 hp)
  have hid := size_encode_fin_function_le (id : Fin n → Fin n) (4 * n + 1) (fun i => by
    have := size_encode_nat_le i.val
    have := i.isLt
    simpa only [encode_fin, id_eq] using (by omega : ⌜i.val⌝ₜ.size ≤ 4 * n + 1))
  have hid' : ⌜(id : Fin n → Fin n)⌝ₜ.size ≤ 8 * N ^ 2 := by nlinarith only [hid, hp]
  dsimp +instances only [id] at *
  simp only [List.map_const', List.sum_replicate, List.length_finRange, smul_eq_mul,
    encode_fin, max_le_iff, foldr_max_le]
  (repeat' apply And.intro) <;> first
  | omega
  | (change 1 + (1 + ⌜n⌝ₜ.size + (1 + ⌜step⌝ₜ.size + ⌜t⌝ₜ.size)) +
       ⌜List.range n⌝ₜ.size ≤ _
     omega)
  | (intro i hi
     have hcode := size_encode_nat_le i.val
     have hlt := i.isLt
     (repeat' apply And.intro) <;> omega)

noncomputable def unrollInitialImpl : Implementation unrollInitial :=
  unrollInitial_realizes.implementation

private theorem unroll_cost_le (n : ℕ) (step : Circuit .booleanAlgebra (n + 1) n) (t : ℕ) :
    let N := 2 * n + t + (t + 1) * step.size + 2
    (iterateCost unrollStep unrollStepBounds t ⟨n, 0, step, Circuit.id _ n⟩).time ≤
        t * (10000000000000000000000000000000 * N ^ 9) ∧
      (iterateCost unrollStep unrollStepBounds t ⟨n, 0, step, Circuit.id _ n⟩).peak ≤
        100000000000000000000000000 * N ^ 4 := by
  let N := 2 * n + t + (t + 1) * step.size + 2
  have hN : 1 ≤ N := by dsimp [N]; omega
  have htN : t ≤ N := by dsimp [N]; omega
  have hN₂ := Nat.le_self_pow (by decide : 2 ≠ 0) N
  have h₁₂ : 1 ≤ N ^ 2 := Nat.one_le_pow 2 _ hN
  have h₂₄ : N ^ 2 ≤ N ^ 4 := Nat.pow_le_pow_right hN (by decide)
  have h₂₉ : N ^ 2 ≤ N ^ 9 := Nat.pow_le_pow_right hN (by decide)
  have hiN (i : ℕ) (hi : i ≤ t) :
      2 * n + i + step.size + (step.unroll i).size + 2 ≤ N := by
    have hm := Nat.mul_le_mul_right step.size hi
    simp only [N, Circuit.size_unroll, Nat.add_mul, Nat.one_mul]
    omega
  have h := iterateCost_le unrollStep unrollStepBounds
    (fun r y => ∃ i, i + r = t ∧ y = (⟨n, i, step, step.unroll i⟩ : UnrollState))
    (fun r _ => r * (10000000000000000000000000000000 * N ^ 9))
    (100000000000000000000000000 * N ^ 4) t ⟨n, 0, step, Circuit.id _ n⟩
    ⟨0, by omega, rfl⟩ ?_ ?_
  · exact h.2
  · rintro r y ⟨i, hi, rfl⟩
    have hi' : i ≤ t := by omega
    have hr : r + 1 ≤ t := by omega
    have hs := size_unrollState_le n step t i hi'
    change _ ≤ 256 * N ^ 2 at hs
    have hcount := size_encode_nat_le (r + 1)
    have htime : unrollStepBounds.time ⟨n, i, step, step.unroll i⟩ ≤
        1000000000000000000000000000000 * N ^ 9 :=
      Nat.mul_le_mul_left _ (pow_le_pow_left' (hiN i hi') 9)
    have hpeak : unrollStepBounds.peak ⟨n, i, step, step.unroll i⟩ ≤
        10000000000000000000000000 * N ^ 4 :=
      Nat.mul_le_mul_left _ (pow_le_pow_left' (hiN i hi') 4)
    refine ⟨⟨i + 1, by omega, rfl⟩, ?_, ?_, ?_⟩
    · rw [Nat.add_mul, Nat.one_mul]
      omega
    · simp only [size_encode_prod]
      omega
    · omega
  · rintro y ⟨i, hi, rfl⟩
    have hs := size_unrollState_le n step t i (by omega)
    change _ ≤ 256 * N ^ 2 at hs
    have hz := size_encode_nat_le 0
    simp only [size_encode_prod]
    omega

/-- Generator bounds in the numeric layer count, including all intermediate circuits. -/
@[simps] def unrollBounds : Bounds UnrollInput :=
  let N (x : UnrollInput) := 2 * x.1 + x.2.2 + (x.2.2 + 1) * x.2.1.size + 2
  ⟨fun x => 100000000000000000000000000000000 * N x ^ 10,
   fun x => 1000000000000000000000000000 * N x ^ 4⟩

theorem unroll_base :
    Realizes (fun x : UnrollInput => ⌜x.2.1.unroll x.2.2⌝ₜ) unrollBounds := by
  let result : UnrollState → Tree := fun x => ⌜x.2.2.2⌝ₜ
  have hr : Realizes result ⟨fun _ => 4, fun x => ⌜x⌝ₜ.size⟩ := by source_fun_prop
  have hc := unrollInitial_realizes.comp (unrollStep_realizes.iterate.comp hr)
  have he : (result ∘ (fun x : ℕ × UnrollState => unrollStep^[x.1] x.2)) ∘ unrollInitial =
      (fun x : UnrollInput => ⌜x.2.1.unroll x.2.2⌝ₜ) := by
    funext x
    dsimp only [Function.comp_def, unrollInitial]
    rw [iterate_unrollStep]
  rw [he] at hc
  refine hc.mono ?_
  rintro ⟨n, step, t⟩
  let N := 2 * n + t + (t + 1) * step.size + 2
  have hN : 1 ≤ N := by dsimp [N]; omega
  have htN : t ≤ N := by dsimp [N]; omega
  have h₁₀ : 1 ≤ N ^ 10 := Nat.one_le_pow 10 _ hN
  have h₂₁₀ : N ^ 2 ≤ N ^ 10 := Nat.pow_le_pow_right hN (by decide)
  have h₂₄ : N ^ 2 ≤ N ^ 4 := Nat.pow_le_pow_right hN (by decide)
  have htime : t * (10000000000000000000000000000000 * N ^ 9) ≤
      10000000000000000000000000000000 * N ^ 10 := calc
    _ ≤ N * (10000000000000000000000000000000 * N ^ 9) := Nat.mul_le_mul_right _ htN
    _ = _ := by rw [pow_succ N 9]; ac_rfl
  have hi := unroll_cost_le n step t
  have hs := size_unrollState_le n step t t le_rfl
  dsimp only at hi
  dsimp only [N] at htime h₁₀ h₂₁₀ h₂₄
  simp only [compBounds, unrollInitialBounds, unrollBounds, unrollInitial, iterateBounds,
    iterate_unrollStep, max_le_iff]
  omega

noncomputable def unrollImplementation :
    Implementation (fun x : UnrollInput => ⌜x.2.1.unroll x.2.2⌝ₜ) := unroll_base.implementation

@[scoped fun_prop] theorem unroll_realizes {ρ : Type} [UniqueEncoding Tree ρ]
    {n t : ρ → ℕ} {step : (x : ρ) → Circuit .booleanAlgebra (n x + 1) (n x)}
    {b : Bounds ρ}
    (h : Realizes (fun x => (⟨n x, step x, t x⟩ : UnrollInput)) b) :
    Realizes (fun x => ⌜(step x).unroll (t x)⌝ₜ)
      (compBounds (fun x => (⟨n x, step x, t x⟩ : UnrollInput)) b unrollBounds) :=
  h.comp unroll_base

end Complexity.TreeProgram.Source
