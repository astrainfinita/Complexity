/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Tactic.TreeProgram.Arithmetic

/-! # Counted source iteration with per-call resource bounds -/

@[expose] public section

open Complexity TreeProgram
namespace Complexity.TreeProgram.Source

namespace Costed

/-- Joint evaluation of a counted loop; the model keeps only a binary counter. -/
noncomputable def iterate {α : Type*} [UniqueEncoding Tree α] (run : α → Costed α) : ℕ → α →
  Costed α
  | 0, a => ofValue a ⟨0, 2 * ⌜((0 : ℕ), a)⌝ₜ.size + 10⟩
  | n + 1, a =>
    let step := run a
    let rest := iterate run n step.value
    ofValue rest.value ⟨step.cost.time + Implementation.pred.bounds.time (n + 1) + 20 +
      rest.cost.time,
      max (2 * max ⌜(n + 1, a)⌝ₜ.size (Implementation.pred.bounds.peak (n + 1)) + 10) (max (2 *
        step.cost.peak) rest.cost.peak)⟩

@[simp] theorem value_iterate {α : Type*} [UniqueEncoding Tree α] (run : α → Costed α)
    (n : ℕ) (a : α) : (iterate run n a).value = (fun a => (run a).value)^[n] a := by
  induction n generalizing a <;> simp [iterate, Function.iterate_succ_apply, *]

@[simp] theorem cost_iterate_zero {α : Type*} [UniqueEncoding Tree α] (run : α → Costed α)
    (a : α) : (iterate run 0 a).cost = ⟨0, 2 * ⌜((0 : ℕ), a)⌝ₜ.size + 10⟩ := rfl

@[simp] theorem time_iterate_succ {α : Type*} [UniqueEncoding Tree α] (run : α → Costed α)
    (n : ℕ) (a : α) : (iterate run (n + 1) a).cost.time =
      (run a).cost.time + Implementation.pred.bounds.time (n + 1) + 20 + (iterate run n (run
        a).value).cost.time := rfl

@[simp] theorem peak_iterate_succ {α : Type*} [UniqueEncoding Tree α] (run : α → Costed α)
    (n : ℕ) (a : α) : (iterate run (n + 1) a).cost.peak =
      max (2 * max ⌜(n + 1, a)⌝ₜ.size (Implementation.pred.bounds.peak (n + 1)) + 10)
        (max (2 * (run a).cost.peak) (iterate run n (run a).value).cost.peak) := rfl

theorem size_le_iterate {α : Type*} [UniqueEncoding Tree α] (run : α → Costed α)
    (n : ℕ) (a : α) : 2 * ⌜(n, a)⌝ₜ.size + 10 ≤ (iterate run n a).cost.peak := by
  cases n <;> simp

end Costed

def Iteration.continues {α : Type*} (x : ℕ × α) := !x.1.bits.isEmpty

def Iteration.continuesImplementation {α : Type*} [UniqueEncoding Tree α] :
    Implementation (Iteration.continues (α := α)) := by
  let h : Implementation (Iteration.continues (α := α)) := by source_fun_prop
  refine h.rebudget ⟨fun _ => 10, fun x => 2 * ⌜x⌝ₜ.size + 10⟩ ?_
  simp only [h, source_bounds]
  rintro ⟨n, a⟩
  cases h : n.bits <;> simp [h] <;> omega

@[simp, source_bounds↓] theorem Iteration.bounds_continues {α : Type*} [UniqueEncoding Tree α] :
    (Iteration.continuesImplementation (α := α)).bounds =
      ⟨fun _ => 10, fun x => 2 * ⌜x⌝ₜ.size + 10⟩ := rfl

noncomputable def Iteration.stepImplementation {α : Type*} [UniqueEncoding Tree α]
    {f : α → α} (hf : Implementation f) :
    Implementation (fun x : ℕ × α => (x.1.pred, f x.2)) := by
  let h : Implementation (fun x : ℕ × α => (x.1.pred, f x.2)) := by source_fun_prop
  refine h.rebudget
    ⟨fun x => hf.bounds.time x.2 + Implementation.pred.bounds.time x.1 + 4,
     fun x => max (2 * max ⌜x⌝ₜ.size (Implementation.pred.bounds.peak x.1) + 10) (2 *
       hf.bounds.peak x.2)⟩ ?_
  -- Keep the projection equalities explicit: reducing the predecessor implementation
  -- during kernel conversion is much more expensive than checking these equalities.
  simp (config := { implicitDefEqProofs := false }) only [h, Implementation.bounds_pair,
    Implementation.bounds_comp, Implementation.bounds_fst, Implementation.bounds_snd,
    Implementation.bounds_congr, compBounds, pairBounds, projectionBounds]
  rintro ⟨n, a⟩
  have hp := Implementation.pred.implements.size_le n
  have hf := hf.implements.size_le a
  simp only [size_encode_prod]
  simp only [max_le_iff]
  (repeat' apply And.intro) <;> omega

@[simp, source_bounds↓] theorem Iteration.bounds_step {α : Type*} [UniqueEncoding Tree α]
    {f : α → α} (hf : Implementation f) :
    (Iteration.stepImplementation hf).bounds =
      ⟨fun x => hf.bounds.time x.2 + Implementation.pred.bounds.time x.1 + 4,
       fun x => max (2 * max ⌜x⌝ₜ.size (Implementation.pred.bounds.peak x.1) + 10) (2 *
         hf.bounds.peak x.2)⟩ := rfl

/-- Compile one callback for every count, retaining the summed evaluation costs. -/
@[simps program evaluate] noncomputable def Implementation.iterate {α : Type*}
    [UniqueEncoding Tree α]
    {f : α → α} (hf : Implementation f) :
    Implementation (fun x : ℕ × α => f^[x.1] x.2) := by
  let hc := Iteration.continuesImplementation (α := α)
  let hs := Iteration.stepImplementation hf
  let eval (x : ℕ × α) := Costed.iterate hf.evaluate x.1 x.2
  refine ⟨loopCode hc.program hs.program (Implementation.snd (α := ℕ) (β := α)).program,
    (fun x => Costed.ofValue (eval x).value ⟨(eval x).cost.time + 17, (eval x).cost.peak⟩),
    (fun x => by simp [eval, hf.value_eq]), ?_⟩
  have hc' := hc.implements
  have hs' := hs.implements
  simp only [hc, hs, Iteration.bounds_continues, Iteration.bounds_step] at hc' hs'
  let I (x y : ℕ × α) := (eval y).cost.peak ≤ (eval x).cost.peak ∧
    f^[y.1] y.2 = f^[x.1] x.2
  have hsize (x y) (hi : I x y) : 2 * ⌜y⌝ₜ.size + 10 ≤ (eval x).cost.peak :=
    (Costed.size_le_iterate hf.evaluate y.1 y.2).trans hi.1
  suffices h : Implements (loopCode hc.program hs.program
      (Implementation.snd (α := ℕ) (β := α)).program)
      (fun x : ℕ × α => f^[x.1] x.2)
      ⟨fun x => 10 + ((eval x).cost.time + 2) + 1 + 4, fun x => (eval x).cost.peak⟩ by
    apply (h.mono (c := ⟨fun x => (eval x).cost.time + 17, fun x => (eval x).cost.peak⟩)
      (fun x => ⟨by dsimp only; omega, le_rfl⟩)).of_encode
    intro x
    simp only [Costed.value_ofValue, eval, Costed.value_iterate, hf.value_eq]
  apply hc'.loop_budget hs' (Implementation.snd (α := ℕ) (β := α)).implements I
    (fun _ y => (eval y).cost.time + 2) (fun _ => 1) (fun x => (eval x).cost.peak)
    (fun _ => ⟨le_rfl, rfl⟩) ?_ ?_ (fun _ _ _ _ => by omega) ?_ ?_
  · intro x y hi; have := hsize x y hi; omega
  · intro x y hi; exact hsize x y hi
  · rintro x ⟨n, a⟩ hi ht
    cases n with
    | zero => simp [Iteration.continues] at ht
    | succ n =>
      have hp := hi.1
      have hv := hi.2
      simp only [eval, Costed.peak_iterate_succ, Costed.time_iterate_succ,
        hf.value_eq, Nat.pred_succ, max_le_iff] at hp ⊢
      refine ⟨⟨hp.1, hp.2.1⟩, ⟨hp.2.2, ?_⟩, ?_⟩
      · simpa only [Function.iterate_succ_apply] using hv
      · dsimp only [Implementation.bounds, Costed.bounds]
        omega
  · rintro x ⟨n, a⟩ hi ht
    have hb : n.bits = [] := by simpa [Iteration.continues, List.isEmpty_iff] using ht
    have hz : n = 0 := by simpa using congrArg BitList.toNat hb
    subst n
    have := hsize x (0, a) hi
    exact ⟨le_rfl, by simp only [Implementation.bounds_snd, projectionBounds]; omega,
      by simpa using hi.2⟩

/-- Project iteration costs without exposing the implementing program or joint evaluation. -/
noncomputable def iterateCost {α : Type*} [UniqueEncoding Tree α] (f : α → α) (b : Bounds α)
    (n : ℕ) (a : α) : Cost :=
  (Costed.iterate (fun a => Costed.ofValue (f a) ⟨b.time a, b.peak a⟩) n a).cost

@[simp] theorem iterateCost_zero {α : Type*} [UniqueEncoding Tree α] (f : α → α) (b : Bounds α)
    (a : α) : iterateCost f b 0 a = ⟨0, 2 * ⌜((0 : ℕ), a)⌝ₜ.size + 10⟩ := rfl

@[simp] theorem iterateCost_succ {α : Type*} [UniqueEncoding Tree α] (f : α → α) (b : Bounds α)
    (n : ℕ) (a : α) : iterateCost f b (n + 1) a =
      ⟨b.time a + Implementation.pred.bounds.time (n + 1) + 20 + (iterateCost f b n (f a)).time,
        max (2 * max ⌜(n + 1, a)⌝ₜ.size (Implementation.pred.bounds.peak (n + 1)) + 10)
          (max (2 * b.peak a) (iterateCost f b n (f a)).peak)⟩ := rfl

/-- Source invariants bound the accumulated callback times and every intermediate state. -/
theorem iterateCost_le {α : Type*} [UniqueEncoding Tree α] (f : α → α) (b : Bounds α)
    (I : ℕ → α → Prop) (remaining : ℕ → α → ℕ) (space n : ℕ) (a : α)
    (initial : I n a)
    (step : ∀ n a, I (n + 1) a → I n (f a) ∧
      b.time a + Implementation.pred.bounds.time (n + 1) + 20 + remaining n (f a) ≤ remaining (n
        + 1) a ∧
      2 * max ⌜(n + 1, a)⌝ₜ.size (Implementation.pred.bounds.peak (n + 1)) + 10 ≤ space ∧ 2 *
        b.peak a ≤ space)
    (stop : ∀ a, I 0 a → 2 * ⌜((0 : ℕ), a)⌝ₜ.size + 10 ≤ space) :
    I 0 (f^[n] a) ∧ (iterateCost f b n a).time ≤ remaining n a ∧
      (iterateCost f b n a).peak ≤ space := by
  induction n generalizing a with
  | zero => simpa using And.intro initial (stop a initial)
  | succ n ih =>
    obtain ⟨hi, ht, hs, hp⟩ := step n a initial
    obtain ⟨hi', ht', hs'⟩ := ih (f a) hi
    simp only [iterateCost_succ, Function.iterate_succ_apply, max_le_iff]
    exact ⟨hi', by omega, hs, hp, hs'⟩

@[simps] noncomputable def iterateBounds {α : Type*} [UniqueEncoding Tree α] (f : α → α)
    (b : Bounds α) : Bounds (ℕ × α) :=
  ⟨fun x => (iterateCost f b x.1 x.2).time + 17, fun x => (iterateCost f b x.1 x.2).peak⟩

@[simp, source_bounds↓] theorem Implementation.bounds_iterate {α : Type*}
    [UniqueEncoding Tree α] {f : α → α} (hf : Implementation f) :
    hf.iterate.bounds = iterateBounds f hf.bounds := by
  have callback : hf.evaluate =
      fun a => Costed.ofValue (f a) ⟨hf.bounds.time a, hf.bounds.peak a⟩ := by
    funext a
    rw [← hf.value_eq a]
    rfl
  change (⟨fun x => (Costed.iterate hf.evaluate x.1 x.2).cost.time + 17,
    fun x => (Costed.iterate hf.evaluate x.1 x.2).cost.peak⟩ : Bounds (ℕ × α)) = _
  rw [callback]
  rfl

/-- A potential may depend on the initial input, remaining count, and current state.
The round and callback peak comparisons cover the active invariant family with one coefficient;
terminal states only require their stored input size. The library handles controller constants
and the semantic recurrence. -/
theorem Implementation.HasGrowth.iterate_of_potential
    {α ρ : Type*} [UniqueEncoding Tree α] {f : α → α} {hf : Implementation f}
    {t p : α → ℕ} (h : hf.HasGrowth t p)
    (I : ρ → ℕ → α → Prop) (count : ρ → ℕ) (initial : ρ → α)
    (remaining : ρ → ℕ → α → ℕ) (peak : ρ → ℕ)
    (start : ∀ x, I x (count x) (initial x))
    (next : ∀ x n a, I x (n + 1) a → I x n (f a))
    (hround : Dominated
      (fun z : {z : ρ × ℕ × α // I z.1 (z.2.1 + 1) z.2.2} =>
        t z.1.2.2 + ⌜z.1.2.1 + 1⌝ₜ.size + 1)
      (fun z => remaining z.1.1 (z.1.2.1 + 1) z.1.2.2 -
        remaining z.1.1 z.1.2.1 (f z.1.2.2)))
    (hsize : Dominated (fun z : {z : ρ × ℕ × α // I z.1 z.2.1 z.2.2} => ⌜z.1.2⌝ₜ.size)
      (fun z => peak z.1.1))
    (hp : Dominated (fun z : {z : ρ × ℕ × α // I z.1 (z.2.1 + 1) z.2.2} => p z.1.2.2)
      (fun z => peak z.1.1)) :
    Dominated (fun x => hf.iterate.bounds.time (count x, initial x))
      (fun x => remaining x (count x) (initial x) + 1) ∧
    Dominated (fun x => hf.iterate.bounds.peak (count x, initial x)) peak := by
  let Z := {z : ρ × ℕ × α // I z.1 z.2.1 z.2.2}
  let A := {z : ρ × ℕ × α // I z.1 (z.2.1 + 1) z.2.2}
  have hc := h.1.comp (fun z : A => z.1.2.2)
  have htPred := Implementation.hasGrowth_pred.1.comp (fun z : A => z.1.2.1 + 1)
  have round := ((hc.add htPred).add (Dominated.const 20)).trans hround
  have hs := (h.2.comp (fun z : A => z.1.2.2)).trans hp
  have hpPred := (Implementation.hasGrowth_pred.2.comp (fun z : Z => z.1.2.1)).trans
    (hsize.mono_left fun z => size_encode_fst_le z.1.2)
  have fixed : Dominated (fun _ : Z => 10) (fun z => peak z.1.1) :=
    (Dominated.const_of_pos 10 fun z : Z => Tree.size_pos ⌜z.1.2⌝ₜ).trans hsize
  have controlSpace := ((hsize.max_same hpPred).const_mul_left 2).add_same fixed
  obtain ⟨C, hC⟩ := round
  obtain ⟨D, hD⟩ := controlSpace
  obtain ⟨P, hP⟩ := hs.const_mul_left 2
  have bound (x : ρ) := iterateCost_le f hf.bounds (I x) (fun n a => C * remaining x n a)
    ((D + P) * peak x) (count x) (initial x) (start x) (fun n a ha => by
      have ht := hC ⟨(x, n, a), ha⟩
      have hc := hD ⟨(x, n + 1, a), ha⟩
      have hp := hP ⟨(x, n, a), ha⟩
      simp only [Function.comp_apply, Nat.nsmul_eq_mul] at ht hc hp
      refine ⟨next x n a ha, ?_, ?_, ?_⟩
      · have hmono : remaining x n (f a) ≤ remaining x (n + 1) a := by
          by_contra hn
          have hz : remaining x (n + 1) a - remaining x n (f a) = 0 :=
            Nat.sub_eq_zero_of_le (by omega)
          rw [hz, Nat.mul_zero] at ht
          omega
        have heq := Nat.mul_add C (remaining x (n + 1) a - remaining x n (f a))
          (remaining x n (f a))
        rw [Nat.sub_add_cancel hmono] at heq
        omega
      · rw [Nat.add_mul]
        omega
      · rw [Nat.add_mul]
        omega) (fun a ha => by
      have hp := hD ⟨(x, 0, a), ha⟩
      simp only [Function.comp_apply, Nat.nsmul_eq_mul] at hp
      rw [Nat.add_mul]
      omega)
  have ht : Dominated (fun x => (iterateCost f hf.bounds (count x) (initial x)).time)
      (fun x => remaining x (count x) (initial x)) :=
    Dominated.of_le_mul C fun x => (bound x).2.1
  have hp : Dominated (fun x => (iterateCost f hf.bounds (count x) (initial x)).peak) peak :=
    Dominated.of_le_mul (D + P) fun x => (bound x).2.2
  simpa only [Implementation.bounds_iterate, iterateBounds] using
    And.intro (ht.add (Dominated.const 17)) hp

/-- A common round allowance is the special potential `remaining count * round allowance`.
The caller supplies only its invariant and uniform size relations. Callback allowances are
required only when the remaining count is positive. -/
theorem Implementation.HasGrowth.iterate_of_invariant
    {α ρ : Type*} [UniqueEncoding Tree α] {f : α → α} {hf : Implementation f}
    {t p : α → ℕ} (h : hf.HasGrowth t p)
    (I : ρ → ℕ → α → Prop) (count : ρ → ℕ) (initial : ρ → α) (time peak : ρ → ℕ)
    (start : ∀ x, I x (count x) (initial x))
    (next : ∀ x n a, I x (n + 1) a → I x n (f a))
    (hcount : Dominated (fun z : {z : ρ × ℕ × α // I z.1 z.2.1 z.2.2} => ⌜z.1.2.1⌝ₜ.size)
      (fun z => time z.1.1))
    (hsize : Dominated (fun z : {z : ρ × ℕ × α // I z.1 z.2.1 z.2.2} => ⌜z.1.2⌝ₜ.size)
      (fun z => peak z.1.1))
    (ht : Dominated (fun z : {z : ρ × ℕ × α // I z.1 (z.2.1 + 1) z.2.2} => t z.1.2.2)
      (fun z => time z.1.1))
    (hp : Dominated (fun z : {z : ρ × ℕ × α // I z.1 (z.2.1 + 1) z.2.2} => p z.1.2.2)
      (fun z => peak z.1.1)) :
    Dominated (fun x => hf.iterate.bounds.time (count x, initial x))
      (fun x => count x * time x + 1) ∧
    Dominated (fun x => hf.iterate.bounds.peak (count x, initial x)) peak := by
  apply h.iterate_of_potential I count initial (fun x n _ => n * time x) peak start next
    ?_ hsize hp
  let active (z : {z : ρ × ℕ × α // I z.1 (z.2.1 + 1) z.2.2}) :
      {z : ρ × ℕ × α // I z.1 z.2.1 z.2.2} := ⟨(z.1.1, z.1.2.1 + 1, z.1.2.2), z.2⟩
  have fixed : Dominated (fun _ : {z : ρ × ℕ × α // I z.1 z.2.1 z.2.2} => 1)
      (fun z => time z.1.1) := hcount.mono_left fun z => Tree.size_pos ⌜z.1.2.1⌝ₜ
  have hround := (ht.add_same (hcount.comp active)).add_same (fixed.comp active)
  simpa only [Function.comp_def, active, Nat.add_mul, Nat.one_mul,
    Nat.add_sub_cancel_left] using hround

/-- Preparation, a counted loop, and its result callback share one selected implementation.
The step callback is compared only on active states, and the result callback only on terminal
states of the source invariant. -/
theorem Implementation.HasGrowth.iterate_comp
    {ρ α β : Type*} [UniqueEncoding Tree ρ] [UniqueEncoding Tree α]
    [UniqueEncoding Tree β] {f : α → α} {g : α → β}
    {init : ρ → ℕ × α} {hi : Implementation init}
    {hf : Implementation f} {hg : Implementation g}
    {ti pi : ρ → ℕ} {t p u q : α → ℕ}
    (prep : hi.HasGrowth ti pi) (step : hf.HasGrowth t p) (result : hg.HasGrowth u q)
    (I : ρ → ℕ → α → Prop) (time peak outTime outPeak : ρ → ℕ)
    (start : ∀ x, I x ((init x).1) ((init x).2))
    (next : ∀ x n a, I x (n + 1) a → I x n (f a))
    (hcount : Dominated (fun z : {z : ρ × ℕ × α // I z.1 z.2.1 z.2.2} => ⌜z.1.2.1⌝ₜ.size)
      (fun z => time z.1.1))
    (hsize : Dominated (fun z : {z : ρ × ℕ × α // I z.1 z.2.1 z.2.2} => ⌜z.1.2⌝ₜ.size)
      (fun z => peak z.1.1))
    (ht : Dominated (fun z : {z : ρ × ℕ × α // I z.1 (z.2.1 + 1) z.2.2} => t z.1.2.2)
      (fun z => time z.1.1))
    (hp : Dominated (fun z : {z : ρ × ℕ × α // I z.1 (z.2.1 + 1) z.2.2} => p z.1.2.2)
      (fun z => peak z.1.1))
    (hu : Dominated (fun z : {z : ρ × α // I z.1 0 z.2} => u z.1.2)
      (fun z => outTime z.1.1))
    (hq : Dominated (fun z : {z : ρ × α // I z.1 0 z.2} => q z.1.2)
      (fun z => outPeak z.1.1)) :
    (hi.comp (hf.iterate.comp hg)).HasGrowth
      (fun x => ti x + ((init x).1 * time x + 1 + outTime x))
      (fun x => max (pi x) (max (peak x) (outPeak x))) := by
  have hloop := step.iterate_of_invariant I (fun x => (init x).1) (fun x => (init x).2)
    time peak start next
    hcount hsize ht hp
  have terminal (x : ρ) : I x 0 (f^[(init x).1] ((init x).2)) := by
    have reach (n : ℕ) (a : α) (ha : I x n a) : I x 0 (f^[n] a) := by
      induction n generalizing a with
      | zero => exact ha
      | succ n ih => simpa only [Function.iterate_succ_apply] using ih (f a) (next x n a ha)
    exact reach _ _ (start x)
  let last (x : ρ) : {z : ρ × α // I z.1 0 z.2} := ⟨(x, f^[(init x).1] ((init x).2)), terminal x⟩
  have houtTime :=
    ((result.1.comp (fun z : {z : ρ × α // I z.1 0 z.2} => z.1.2)).trans hu).comp last
  have houtPeak :=
    ((result.2.comp (fun z : {z : ρ × α // I z.1 0 z.2} => z.1.2)).trans hq).comp last
  apply HasGrowth.of_bounds _ (by rw [bounds_comp, bounds_comp])
  · exact prep.1.add (hloop.1.add houtTime)
  · exact prep.2.max (hloop.2.max houtPeak)

/-- Compose preparation, a loop retaining its captured environment, and the result projection. -/
@[simps!] noncomputable def iterateWithBounds {ρ α : Type*} [UniqueEncoding Tree ρ]
  [UniqueEncoding Tree α]
    (f : ρ → α → α) (count : ρ → ℕ) (initial : ρ → α)
    (bi : Bounds ρ) (bs : Bounds (ρ × α)) : Bounds ρ :=
  compBounds (fun e => (count e, (e, initial e))) bi
    (compBounds (fun x : ℕ × (ρ × α) =>
      (fun a : ρ × α => (a.1, f a.1 a.2))^[x.1] x.2)
      (iterateBounds (fun a : ρ × α => (a.1, f a.1 a.2))
        (pairBounds Prod.fst (fun a => f a.1 a.2) projectionBounds bs)) projectionBounds)

/-- Captured values stay in one loop state; one callback covers all runtime environments. -/
noncomputable def Implementation.iterateWith {ρ α : Type*}
    [UniqueEncoding Tree ρ] [UniqueEncoding Tree α]
    {f : ρ → α → α} {count : ρ → ℕ} {initial : ρ → α}
    (hi : Implementation (fun e => (count e, (e, initial e))))
    (hs : Implementation (fun x : ρ × α => f x.1 x.2)) :
    Implementation (fun e => (f e)^[count e] (initial e)) :=
  (hi.comp ((Implementation.fst.pair hs).iterate.comp Implementation.snd)).congr (by
    funext e
    have h (n : ℕ) (a : α) :
        (fun x : ρ × α => (x.1, f x.1 x.2))^[n] (e, a) = (e, (f e)^[n] a) :=
      (Function.Semiconj.iterate_right (f := fun a => (e, a)) (fun _ => rfl) n a).symm
    exact congrArg Prod.snd (h (count e) (initial e)))

@[simp, source_bounds↓] theorem Implementation.bounds_iterateWith {ρ α : Type*}
    [UniqueEncoding Tree ρ] [UniqueEncoding Tree α]
    {f : ρ → α → α} {count : ρ → ℕ} {initial : ρ → α}
    (hi : Implementation (fun e => (count e, (e, initial e))))
    (hs : Implementation (fun x : ρ × α => f x.1 x.2)) :
    (hi.iterateWith hs).bounds = iterateWithBounds f count initial hi.bounds hs.bounds := by
  simp only [iterateWith, bounds_congr, bounds_comp, bounds_iterate,
    bounds_pair, bounds_fst, bounds_snd, iterateWithBounds]

/-- Captured iteration reuses one callback specification for every environment. The invariant
is stated on the user state; retaining the environment and projecting the result are charged
by the library. Time accumulates per round, while space remains a peak. -/
theorem Implementation.HasGrowth.iterateWith
    {ρ α : Type*} [UniqueEncoding Tree ρ] [UniqueEncoding Tree α]
    {f : ρ → α → α} {count : ρ → ℕ} {initial : ρ → α}
    {hi : Implementation (fun e => (count e, (e, initial e)))}
    {hs : Implementation (fun x : ρ × α => f x.1 x.2)}
    {ti pi : ρ → ℕ} {t p : ρ × α → ℕ}
    (prep : hi.HasGrowth ti pi) (step : hs.HasGrowth t p)
    (I : ρ → ℕ → α → Prop) (time peak : ρ → ℕ)
    (start : ∀ x, I x (count x) (initial x))
    (next : ∀ x n a, I x (n + 1) a → I x n (f x a))
    (hcount : Dominated (fun z : {z : ρ × ℕ × α // I z.1 z.2.1 z.2.2} => ⌜z.1.2.1⌝ₜ.size)
      (fun z => time z.1.1))
    (hsize : Dominated (fun z : {z : ρ × ℕ × α // I z.1 z.2.1 z.2.2} =>
      ⌜(z.1.2.1, (z.1.1, z.1.2.2))⌝ₜ.size) (fun z => peak z.1.1))
    (ht : Dominated (fun z : {z : ρ × ℕ × α // I z.1 (z.2.1 + 1) z.2.2} => t (z.1.1, z.1.2.2))
      (fun z => time z.1.1))
    (hp : Dominated (fun z : {z : ρ × ℕ × α // I z.1 (z.2.1 + 1) z.2.2} => p (z.1.1, z.1.2.2))
      (fun z => peak z.1.1)) :
    (hi.iterateWith hs).HasGrowth (fun x => ti x + (count x * time x + 1))
      (fun x => max (pi x) (peak x)) := by
  have fst : (Implementation.fst (α := ρ) (β := α)).HasGrowth
      (fun _ => 1) (fun x => ⌜x⌝ₜ.size) :=
    HasGrowth.of_bounds _ bounds_fst (Dominated.const 1) (Dominated.refl _)
  have snd : (Implementation.snd (α := ρ) (β := α)).HasGrowth
      (fun _ => 1) (fun x => ⌜x⌝ₜ.size) :=
    HasGrowth.of_bounds _ bounds_snd (Dominated.const 1) (Dominated.refl _)
  have output : Dominated (fun x : ρ × α => ⌜(x.1, f x.1 x.2)⌝ₜ.size)
      (fun x => max ⌜x⌝ₜ.size (p x)) := by
    have env : Dominated (fun x : ρ × α => ⌜x.1⌝ₜ.size)
        (fun x => max ⌜x⌝ₜ.size (p x)) :=
      Dominated.of_le fun x => (size_encode_fst_le x).trans (Nat.le_max_left _ _)
    simpa only [size_encode_prod, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (env.add_same step.size_encode).add_same
      (Dominated.const_of_pos 1 fun x => (Tree.size_pos _).trans_le (Nat.le_max_left _ _))
  have carry := (fst.pair step).mono
    (((Dominated.refl t).add (Dominated.const 2)).mono_left (fun x => by omega))
    ((Dominated.of_le (fun x => Nat.le_max_left ⌜x⌝ₜ.size (p x))).max_same
      ((Dominated.of_le (fun x => Nat.le_max_right ⌜x⌝ₜ.size (p x))).max_same output))
  let J (e : ρ) (n : ℕ) (x : ρ × α) := x.1 = e ∧ I e n x.2
  let lift (z : {z : ρ × ℕ × α // I z.1 z.2.1 z.2.2}) :
      {z : ρ × ℕ × (ρ × α) // J z.1 z.2.1 z.2.2} :=
    ⟨(z.1.1, z.1.2.1, (z.1.1, z.1.2.2)), rfl, z.2⟩
  have surj : Function.Surjective lift := by
    rintro ⟨⟨e, n, c, a⟩, hc, ha⟩
    dsimp only [J] at hc ha
    subst c
    exact ⟨⟨(e, n, a), ha⟩, rfl⟩
  let activeLift (z : {z : ρ × ℕ × α // I z.1 (z.2.1 + 1) z.2.2}) :
      {z : ρ × ℕ × (ρ × α) // J z.1 (z.2.1 + 1) z.2.2} :=
    ⟨(z.1.1, z.1.2.1, (z.1.1, z.1.2.2)), rfl, z.2⟩
  have activeSurj : Function.Surjective activeLift := by
    rintro ⟨⟨e, n, c, a⟩, hc, ha⟩
    dsimp only [J] at hc ha
    subst c
    exact ⟨⟨(e, n, a), ha⟩, rfl⟩
  let active (z : {z : ρ × ℕ × (ρ × α) // J z.1 (z.2.1 + 1) z.2.2}) :
      {z : ρ × ℕ × (ρ × α) // J z.1 z.2.1 z.2.2} :=
    ⟨(z.1.1, z.1.2.1 + 1, z.1.2.2), z.2⟩
  have size : Dominated
      (fun z : {z : ρ × ℕ × (ρ × α) // J z.1 z.2.1 z.2.2} => ⌜z.1.2⌝ₜ.size)
      (fun z => peak z.1.1) := Dominated.of_comp_surjective lift surj hsize
  have hinput := size.mono_left (fun z => size_encode_snd_le z.1.2)
  have htime : Dominated
      (fun z : {z : ρ × ℕ × (ρ × α) // J z.1 (z.2.1 + 1) z.2.2} => t z.1.2.2)
      (fun z => time z.1.1) := Dominated.of_comp_surjective activeLift activeSurj ht
  have hpeak : Dominated
      (fun z : {z : ρ × ℕ × (ρ × α) // J z.1 (z.2.1 + 1) z.2.2} => p z.1.2.2)
      (fun z => peak z.1.1) := Dominated.of_comp_surjective activeLift activeSurj hp
  have hcount' : Dominated
      (fun z : {z : ρ × ℕ × (ρ × α) // J z.1 z.2.1 z.2.2} => ⌜z.1.2.1⌝ₜ.size)
      (fun z => time z.1.1) := Dominated.of_comp_surjective lift surj hcount
  have fixed := hcount'.mono_left (fun z => Tree.size_pos ⌜z.1.2.1⌝ₜ)
  have growth := prep.iterate_comp carry snd J time peak (fun _ => 1) peak
    (fun e => ⟨rfl, start e⟩) (fun e n a ha => by
      obtain ⟨he, ha⟩ := ha
      exact ⟨he, by simpa only [he] using next e n a.2 ha⟩)
    hcount' size (htime.add_same (fixed.comp active))
    ((hinput.comp active).max_same hpeak)
    (Dominated.refl _)
    (hinput.comp (fun z : {z : ρ × (ρ × α) // J z.1 0 z.2} => ⟨(z.1.1, 0, z.1.2), z.2⟩))
  have ht' : Dominated (fun x => ti x + (count x * time x + 1 + 1))
      (fun x => ti x + (count x * time x + 1)) := by
    simpa only [Nat.add_assoc] using (Dominated.refl ti).add
      ((Dominated.refl (fun x => count x * time x)).add (Dominated.const 2))
  simpa only [Implementation.iterateWith, HasGrowth, bounds_congr, max_self] using
    growth.mono ht' (Dominated.refl _)

-- Only Implementation is searched; budget proofs cannot change the selected program.
attribute [scoped fun_prop] Implementation.iterate Implementation.iterateWith

end Complexity.TreeProgram.Source
