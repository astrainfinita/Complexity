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

def unrollStepScale (x : UnrollState) :=
  2 * x.1 + x.2.1 + x.2.2.1.size + x.2.2.2.size + 2

@[source_growth] theorem unrollStep_growth : unrollStepImpl.HasGrowth
    (fun x => unrollStepScale x ^ 8)
    (fun x => unrollStepScale x ^ 4) := by
  let R := unrollStepScale
  have hR x : 0 < R x := by dsimp [R, unrollStepScale]; omega
  have linear {u : UnrollState → ℕ} (h : ∀ x, u x ≤ 4 * R x) : Dominated u R :=
    Dominated.of_le_mul 4 h
  have circuit {n m : UnrollState → ℕ}
      (c : (x : UnrollState) → Circuit .booleanAlgebra (n x) (m x))
      (hn : ∀ x, n x ≤ 4 * R x) (hm : ∀ x, m x ≤ 4 * R x)
      (hc : ∀ x, (c x).size ≤ 4 * R x) :
      Dominated (fun x => ⌜c x⌝ₜ.size) (fun x => R x ^ 2) :=
    Dominated.size_encode_circuit c (linear hn) (linear hm) (linear hc) hR
  have wires {n m : UnrollState → ℕ} (w : (x : UnrollState) → Fin (n x) → Fin (m x))
      (hn : ∀ x, n x ≤ 4 * R x) (hm : ∀ x, m x ≤ 4 * R x) :
      Dominated (fun x => ⌜w x⌝ₜ.size) (fun x => R x ^ 2) :=
    Dominated.size_encode_fin_function w (linear hn) (linear hm) hR
  have hvalues {n k : ℕ} (f : Fin n → Fin k) :
      ⌜fun i => (f i).val⌝ₜ = ⌜f⌝ₜ := by
    simpa only [encode_fin_function, Function.comp_def] using encode_fin_values f
  have hn : Dominated (fun x : UnrollState => x.1) R := linear (by
    intro x; dsimp [R, unrollStepScale]; omega)
  have ht : Dominated (fun x : UnrollState => x.2.1) R := linear (by
    intro x; dsimp [R, unrollStepScale]; omega)
  have hnt := hn.add_same ht
  have hn1 := hn.add_same (Dominated.one hR)
  have ht1 := ht.add_same (Dominated.one hR)
  have hnt1 := hnt.add_same (Dominated.one hR)
  have hntn := hnt1.add_same hn
  have hcn1 := Dominated.size_encode_nat hn1 hR
  have hnpow := hn1.pow 2
  have hntpow := hnt1.pow 2
  have hcnt := Dominated.size_encode_nat hnt hR
  have hcn := Dominated.size_encode_nat hn hR
  have hct := Dominated.size_encode_nat ht hR
  have hcnt1 := Dominated.size_encode_nat hnt1 hR
  have hcntn := Dominated.size_encode_nat hntn hR
  have hct1 := Dominated.size_encode_nat ht1 hR
  have hcnt' := Dominated.size_encode_nat (hn.add_same ht1) hR
  have hstep := circuit (fun x : UnrollState => x.2.2.1)
    (by intro x; dsimp [R, unrollStepScale]; omega)
    (by intro x; dsimp [R, unrollStepScale]; omega)
    (by intro x; dsimp [R, unrollStepScale]; omega)
  have hcurrent := circuit (fun x : UnrollState => x.2.2.2)
    (by intro x; dsimp [R, unrollStepScale]; omega)
    (by intro x; dsimp [R, unrollStepScale]; omega)
    (by intro x; dsimp [R, unrollStepScale]; omega)
  have input : Dominated (fun x : UnrollState => ⌜x⌝ₜ.size) (fun x => R x ^ 2) := by
    rw [show (fun x : UnrollState => ⌜x⌝ₜ.size) =
      (fun x => 1 + ⌜x.1⌝ₜ.size + (1 + ⌜x.2.1⌝ₜ.size +
        (1 + ⌜x.2.2.1⌝ₜ.size + ⌜x.2.2.2⌝ₜ.size))) from by funext ⟨n, t, s, c⟩; rfl]
    simp only [Dominated.add_iff]
    repeat' apply And.intro
    all_goals with_reducible first
      | assumption
      | exact Dominated.const_of_pos _ (fun x => Nat.pow_pos (hR x))
      | exact Dominated.le_pow (g := R) (by assumption) (by decide)
  have hc0 : Dominated (fun x : UnrollState => ⌜x.2.2.2.relabel Fin.castSucc⌝ₜ.size)
      (fun x => R x ^ 2) := by
    apply circuit <;> intro x <;>
      simp -failIfUnchanged only [Circuit.size_relabel] <;>
      dsimp [R, unrollStepScale] <;> omega
  have hc1 : Dominated (fun x : UnrollState => ⌜(x.2.2.2.relabel Fin.castSucc).keepInputs⌝ₜ.size)
      (fun x => R x ^ 2) := by
    apply circuit <;> intro x <;>
      simp -failIfUnchanged only [Circuit.size_relabel, Circuit.size_keepInputs] <;>
      dsimp [R, unrollStepScale] <;> omega
  have hc2 : Dominated (fun x : UnrollState =>
      ⌜x.2.2.1.relabel (Fin.snoc (Fin.natAdd (x.1 + (x.2.1 + 1)))
        (Fin.castAdd x.1 (Fin.last (x.1 + x.2.1))))⌝ₜ.size)
      (fun x => R x ^ 2) := by
    apply circuit <;> intro x <;>
      simp -failIfUnchanged only [Circuit.size_relabel] <;>
      dsimp [R, unrollStepScale] <;> omega
  have hc3 : Dominated (fun x : UnrollState =>
      ⌜(x.2.2.2.relabel Fin.castSucc).keepInputs.comp
        (x.2.2.1.relabel (Fin.snoc (Fin.natAdd (x.1 + (x.2.1 + 1)))
          (Fin.castAdd x.1 (Fin.last (x.1 + x.2.1)))))⌝ₜ.size)
      (fun x => R x ^ 2) := by
    apply circuit <;> intro x <;>
      simp -failIfUnchanged only [Circuit.size_relabel, Circuit.size_keepInputs,
        Circuit.size_comp] <;>
      dsimp [R, unrollStepScale] <;> omega
  have hrange1 : Dominated (fun x : UnrollState => ⌜List.range x.1⌝ₜ.size)
      (fun x => R x ^ 2) :=
    ((hn1.pow 2).const_mul_left 3).mono_left fun x => size_encode_range_le _
  have hrange2 : Dominated (fun x : UnrollState => ⌜List.range (x.1 + x.2.1)⌝ₜ.size)
      (fun x => R x ^ 2) :=
    ((hnt1.pow 2).const_mul_left 3).mono_left fun x => size_encode_range_le _
  source_fun_prop
  all_goals
    change Dominated _ (fun x => R x ^ _)
    simp only [Function.comp_apply, id_eq, Sigma.encode_mk, size_encode_prod,
      Tree.encode_self, encode_fin, Fin.val_castAdd, Fin.val_last,
      List.map_const', List.sum_replicate, List.length_finRange, List.length_ofFn,
      encode_finRange, ← List.ofFn_eq_map, encode_fin_function_codes, hvalues,
      encode_list_cons, encode_list_nil, size_encode_unit, relabelFn, keepFn, compFn,
      Nat.nsmul_eq_mul, Nat.mul_one,
      Dominated.add_iff, Dominated.max_iff, Dominated.const_mul_left_iff, Nat.ofNat_pos,
      Dominated.zero, true_and]
    repeat' apply And.intro
  all_goals with_reducible first
    | assumption
    | trivial
    | exact Dominated.const_of_pos _ (fun x => Nat.pow_pos (hR x))
    | exact Dominated.le_pow (g := R) (by assumption) (by decide)
    | exact Dominated.mono_pow (g := R) (d := 2) (by assumption) (by decide) hR
    | apply Dominated.pow_of_le (g := R) _ (by decide) hR
      apply linear
      intro x
      simp -failIfUnchanged only [relabelScale, keepScale, compScale, Circuit.size_relabel,
        Circuit.size_keepInputs]
      dsimp [R, unrollStepScale]
      omega
    | apply Dominated.mono_pow (g := R) (d := 2) _ (by decide) hR
      first
        | apply wires <;> intro x <;> dsimp [R, unrollStepScale] <;> omega
    | skip
  · simp only [List.ofFn_eq_map]
    refine (Dominated.sum_finRange (b := R) ?_).trans ?_
    · have hc₁ := Dominated.comp hct (Sigma.fst : (Σ x : UnrollState, Fin x.1) → _)
      have hc₂ := Dominated.comp hcn (Sigma.fst : (Σ x : UnrollState, Fin x.1) → _)
      have hc₃ := Dominated.comp hct1 (Sigma.fst : (Σ x : UnrollState, Fin x.1) → _)
      have hc₄ := Dominated.comp hcnt' (Sigma.fst : (Σ x : UnrollState, Fin x.1) → _)
      have hi : Dominated (fun z : Σ x : UnrollState, Fin x.1 => z.2.val)
          (fun z => R z.1) := (Dominated.comp hn Sigma.fst).mono_left fun z => z.2.isLt.le
      have hci := Dominated.size_encode_nat hi (fun z => hR z.1)
      simp only [Function.comp_def] at hc₁ hc₂ hc₃ hc₄
      simp only [Dominated.add_iff, Dominated.zero, and_true]
      repeat' apply And.intro
      all_goals with_reducible first
        | assumption
        | exact Dominated.const_of_pos _ (fun z => hR z.1)
    · apply Dominated.mono_pow (g := R) (d := 2) _ (by decide) hR
      simpa only [pow_two] using hn.mul (Dominated.refl R)
  all_goals
    let Z₁ := Σ x : UnrollState, Fin (x.1 + x.2.1)
    let Z₂ := Σ x : UnrollState, Fin x.1
    have hi₁ : Dominated (fun z : Z₁ => z.2.val) (fun z => R z.1) :=
      (Dominated.comp hnt Sigma.fst).mono_left fun z => z.2.isLt.le
    have hi₂ : Dominated (fun z : Z₂ => z.2.val) (fun z => R z.1) :=
      (Dominated.comp hn Sigma.fst).mono_left fun z => z.2.isLt.le
    have hci₁ := Dominated.size_encode_nat hi₁ (fun z => hR z.1)
    have hci₂ := Dominated.size_encode_nat hi₂ (fun z => hR z.1)
    have hs₁ := Dominated.comp input (Sigma.fst : Z₁ → _)
    have hs₂ := Dominated.comp input (Sigma.fst : Z₂ → _)
    have hc₁ := Dominated.comp hcn (Sigma.fst : Z₂ → _)
    have hc₂ := Dominated.comp hct (Sigma.fst : Z₂ → _)
    have hc₃ := Dominated.comp hct1 (Sigma.fst : Z₂ → _)
    have hc₄ := Dominated.comp hcnt' (Sigma.fst : Z₂ → _)
    simp only [Function.comp_def] at hs₁ hs₂ hc₁ hc₂ hc₃ hc₄
  all_goals
    apply Dominated.foldr_max_le
    simp only [Fin.val_castSucc, Dominated.max_iff, Dominated.add_iff,
      Dominated.zero, and_true]
    repeat' apply And.intro
  all_goals with_reducible first
    | apply Dominated.const_of_pos
      intro z
      exact Nat.pow_pos (hR z.1)
    | exact Dominated.mono_pow hs₁ (by decide) (fun z => hR z.1)
    | exact Dominated.mono_pow hs₂ (by decide) (fun z => hR z.1)
    | exact Dominated.le_pow hci₁ (by decide)
    | exact Dominated.le_pow hci₂ (by decide)
    | exact Dominated.le_pow hc₁ (by decide)
    | exact Dominated.le_pow hc₂ (by decide)
    | exact Dominated.le_pow hc₃ (by decide)
    | exact Dominated.le_pow hc₄ (by decide)

abbrev UnrollInput := Σ n, Circuit .booleanAlgebra (n + 1) n × ℕ

def unrollInitial (x : UnrollInput) : ℕ × UnrollState :=
  (x.2.2, ⟨x.1, 0, x.2.1, Circuit.id _ x.1⟩)

def unrollScale (x : UnrollInput) :=
  2 * x.1 + x.2.2 + (x.2.2 + 1) * x.2.1.size + 2

noncomputable def unrollInitialImpl : Implementation unrollInitial := by
  source_fun_prop using tabulate

@[source_growth] theorem unrollInitial_growth : unrollInitialImpl.HasGrowth
    (fun x => unrollScale x ^ 2)
    (fun x => unrollScale x ^ 2) := by
  let R := unrollScale
  have hR x : 0 < R x := by dsimp [R, unrollScale]; omega
  have hn : Dominated (fun x : UnrollInput => x.1) R := Dominated.of_le fun x => by
    dsimp [R, unrollScale]; omega
  have ht : Dominated (fun x : UnrollInput => x.2.2) R := Dominated.of_le fun x => by
    dsimp [R, unrollScale]; omega
  have hg : Dominated (fun x : UnrollInput => x.2.1.size) R := Dominated.of_le fun x => by
    have := Nat.le_mul_of_pos_left x.2.1.size (Nat.succ_pos x.2.2)
    simp only [Nat.succ_eq_add_one] at this
    dsimp [R, unrollScale]
    omega
  have hn1 := hn.add_same (Dominated.one hR)
  have hstep := Dominated.size_encode_circuit (fun x : UnrollInput => x.2.1) hn1 hn hg hR
  have hcn := Dominated.size_encode_nat hn hR
  have hct := Dominated.size_encode_nat ht hR
  have hpow := hn1.pow 2
  have hid := Dominated.size_encode_fin_function
    (fun x : UnrollInput => (id : Fin x.1 → Fin x.1))
    hn hn hR
  have hrange : Dominated (fun x : UnrollInput => ⌜List.range x.1⌝ₜ.size)
      (fun x => R x ^ 2) := (hpow.const_mul_left 3).mono_left fun x => size_encode_range_le _
  have input : Dominated (fun x : UnrollInput => ⌜x⌝ₜ.size) (fun x => R x ^ 2) := by
    rw [show (fun x : UnrollInput => ⌜x⌝ₜ.size) =
      (fun x => 1 + ⌜x.1⌝ₜ.size + (1 + ⌜x.2.1⌝ₜ.size + ⌜x.2.2⌝ₜ.size)) from by
      funext ⟨n, c, t⟩; rfl]
    simp only [Dominated.add_iff]
    repeat' apply And.intro
    all_goals with_reducible first
      | assumption
      | exact Dominated.const_of_pos _ (fun x => Nat.pow_pos (hR x))
      | exact Dominated.le_pow (g := R) (by assumption) (by decide)
  source_fun_prop
  all_goals
    change Dominated _ (fun x => R x ^ 2)
    simp only [id_eq, Sigma.encode_mk, size_encode_prod, size_encode_unit,
      Tree.encode_self, Circuit.id, Circuit.encode_outputs,
      List.map_const', List.sum_replicate, List.length_finRange, Nat.nsmul_eq_mul,
      Nat.mul_one, Dominated.add_iff, Dominated.max_iff, Dominated.zero, true_and]
    repeat' apply And.intro
  all_goals with_reducible first
    | assumption
    | exact Dominated.const_of_pos _ (fun x => Nat.pow_pos (hR x))
    | exact Dominated.le_pow (g := R) (by assumption) (by decide)
    | skip
  · have hi : Dominated (fun z : Σ x : UnrollInput, Fin x.1 => z.2.val)
        (fun z => R z.1) := (Dominated.comp hn Sigma.fst).mono_left fun z => z.2.isLt.le
    have hci := Dominated.size_encode_nat hi (fun z => hR z.1)
    have hs := Dominated.comp input (Sigma.fst : (Σ x : UnrollInput, Fin x.1) → _)
    simp only [Function.comp_def] at hs
    apply Dominated.foldr_max_le
    simp only [encode_fin, Dominated.max_iff, Dominated.add_iff]
    repeat' apply And.intro
    all_goals with_reducible first
      | assumption
      | apply Dominated.const_of_pos
        intro z
        exact Nat.pow_pos (hR z.1)
      | exact Dominated.le_pow hci (by decide)

/-- The result projection is selected independently of its eventual budget. -/
noncomputable def unrollResultImpl : Implementation (fun x : UnrollState => ⌜x.2.2.2⌝ₜ) := by
  source_fun_prop

@[source_growth] theorem unrollResult_growth : unrollResultImpl.HasGrowth
    (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  · exact Dominated.const _
  · apply (Dominated.refl _).max_same
    apply Dominated.of_le
    rintro ⟨n, t, step, current⟩
    simp only [Sigma.encode_mk, size_encode_prod, Tree.encode_self]
    omega

noncomputable def unrollImplementation :
    Implementation (fun x : UnrollInput => ⌜x.2.1.unroll x.2.2⌝ₜ) :=
  (unrollInitialImpl.comp (unrollStepImpl.iterate.comp unrollResultImpl)).congr (by
    funext x
    dsimp only [Function.comp_def, unrollInitial]
    rw [iterate_unrollStep])

/-- The loop sums one step allowance per layer and retains a maximum space allowance. -/
@[source_growth] theorem unroll_growth : unrollImplementation.HasGrowth
    (fun x => unrollScale x ^ 9) (fun x => unrollScale x ^ 4) := by
  let R := unrollScale
  have hR x : 0 < R x := by dsimp [R, unrollScale]; omega
  let I (x : UnrollInput) (r : ℕ) (y : UnrollState) :=
    ∃ i, i + r = x.2.2 ∧ y = ⟨x.1, i, x.2.1, x.2.1.unroll i⟩
  let Z := {z : UnrollInput × ℕ × UnrollState // I z.1 z.2.1 z.2.2}
  have hscale : Dominated (fun z : Z => unrollStepScale z.1.2.2) (fun z => R z.1.1) :=
    Dominated.of_le fun z => by
      rcases z with ⟨⟨⟨n, step, t⟩, r, y⟩, hz⟩
      change unrollStepScale y ≤ R ⟨n, step, t⟩
      dsimp only [I] at hz
      rcases hz with ⟨i, hi, rfl⟩
      have hm := Nat.mul_le_mul_right step.size (show i ≤ t by omega)
      simp only [unrollStepScale, R, unrollScale, Circuit.size_unroll, Nat.add_mul, Nat.one_mul]
      omega
  have hstate : Dominated (fun z : Z => ⌜z.1.2.2⌝ₜ.size) (fun z => R z.1.1 ^ 2) :=
    Dominated.of_le_mul 256 fun z => by
      rcases z with ⟨⟨⟨n, step, t⟩, r, y⟩, hz⟩
      change ⌜y⌝ₜ.size ≤ 256 * R ⟨n, step, t⟩ ^ 2
      dsimp only [I] at hz
      rcases hz with ⟨i, hi, rfl⟩
      exact size_unrollState_le n step t i (by omega)
  have hcount : Dominated (fun z : Z => z.1.2.1) (fun z => R z.1.1) :=
    Dominated.of_le fun z => by
      rcases z with ⟨⟨⟨n, step, t⟩, r, y⟩, hz⟩
      change r ≤ R ⟨n, step, t⟩
      dsimp only [I] at hz
      obtain ⟨i, hi, _⟩ := hz
      dsimp [R, unrollScale]
      omega
  have hcounter := Dominated.size_encode_nat hcount (fun z => hR z.1.1)
  have hsize : Dominated (fun z : Z => ⌜z.1.2⌝ₜ.size) (fun z => R z.1.1 ^ 4) := by
    rw [show (fun z : Z => ⌜z.1.2⌝ₜ.size) =
      (fun z => 1 + ⌜z.1.2.1⌝ₜ.size + ⌜z.1.2.2⌝ₜ.size) from by
      funext ⟨⟨x, r, y⟩, hz⟩; rfl]
    simp only [Dominated.add_iff]
    exact ⟨⟨Dominated.const_of_pos 1 (fun z => Nat.pow_pos (hR z.1.1)),
      hcounter.le_pow (by decide)⟩, hstate.mono_pow (by decide) (fun z => hR z.1.1)⟩
  let active (z : {z : UnrollInput × ℕ × UnrollState // I z.1 (z.2.1 + 1) z.2.2}) : Z :=
    ⟨(z.1.1, z.1.2.1 + 1, z.1.2.2), z.2⟩
  have htotal := unrollInitial_growth.iterate_comp
    unrollStep_growth unrollResult_growth I
    (fun x => R x ^ 8) (fun x => R x ^ 4) (fun _ => 1) (fun x => R x ^ 4)
    (fun _ => ⟨0, by simp only [unrollInitial, Nat.zero_add], rfl⟩)
    (by rintro x r y ⟨i, hi, rfl⟩; exact ⟨i + 1, by omega, rfl⟩)
    (hcounter.le_pow (by decide)) hsize ((hscale.comp active).pow 8)
    ((hscale.comp active).pow 4)
    (Dominated.refl _)
    ((hsize.comp (fun z : {z : UnrollInput × UnrollState // I z.1 0 z.2} =>
      ⟨(z.1.1, 0, z.1.2), z.2⟩)).mono_left
      (fun z => size_encode_snd_le (0, z.1.2)))
  unfold unrollImplementation
  apply Implementation.HasGrowth.congr
  apply htotal.mono
  · have ht : Dominated (fun x : UnrollInput => x.2.2) R := Dominated.of_le fun x => by
      dsimp [R, unrollScale]; omega
    have rounds : Dominated (fun x : UnrollInput => x.2.2 * R x ^ 8)
        (fun x => R x ^ 9) := by
      simpa only [pow_succ', Nat.mul_comm] using ht.mul ((Dominated.refl R).pow 8)
    exact ((Dominated.refl R).pow 2 |>.mono_pow (by decide) hR).add_same
      ((rounds.add_same (Dominated.const_of_pos 1 fun x => Nat.pow_pos (hR x))).add_same
        (Dominated.const_of_pos 1 fun x => Nat.pow_pos (hR x)))
  · exact ((Dominated.refl R).pow 2 |>.mono_pow (by decide) hR).max_same
      ((Dominated.refl _).max_same (Dominated.refl _))

noncomputable def Implementation.unroll {ρ : Type} [UniqueEncoding Tree ρ]
    {n t : ρ → ℕ} {step : (x : ρ) → Circuit .booleanAlgebra (n x + 1) (n x)}
    (h : Implementation (fun x => (⟨n x, step x, t x⟩ : UnrollInput))) :
    Implementation (fun x => ⌜(step x).unroll (t x)⌝ₜ) :=
  h.comp unrollImplementation

@[simp, source_bounds↓] theorem Implementation.bounds_unroll {ρ : Type} [UniqueEncoding Tree ρ]
    {n t : ρ → ℕ} {step : (x : ρ) → Circuit .booleanAlgebra (n x + 1) (n x)}
    (h : Implementation (fun x => (⟨n x, step x, t x⟩ : UnrollInput))) :
    (Implementation.unroll h).bounds =
      compBounds (fun x => (⟨n x, step x, t x⟩ : UnrollInput))
        h.bounds unrollImplementation.bounds :=
  Implementation.bounds_comp _ _

attribute [scoped fun_prop] Implementation.unroll

end Complexity.TreeProgram.Source
