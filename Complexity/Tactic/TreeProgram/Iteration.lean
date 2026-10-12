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
def iterate {α : Type*} [UniqueEncoding Tree α] (run : α → Costed α) : ℕ → α → Costed α
  | 0, a => ofValue a ⟨0, 2 * ⌜((0 : ℕ), a)⌝ₜ.size + 10⟩
  | n + 1, a =>
    let step := run a
    let rest := iterate run n step.value
    ofValue rest.value ⟨step.cost.time + 100 * ⌜n + 1⌝ₜ.size + 420 + rest.cost.time,
      max (20 * ⌜(n + 1, a)⌝ₜ.size + 100) (max (2 * step.cost.peak) rest.cost.peak)⟩

@[simp] theorem value_iterate {α : Type*} [UniqueEncoding Tree α] (run : α → Costed α)
    (n : ℕ) (a : α) : (iterate run n a).value = (fun a => (run a).value)^[n] a := by
  induction n generalizing a <;> simp [iterate, Function.iterate_succ_apply, *]

@[simp] theorem cost_iterate_zero {α : Type*} [UniqueEncoding Tree α] (run : α → Costed α)
    (a : α) : (iterate run 0 a).cost = ⟨0, 2 * ⌜((0 : ℕ), a)⌝ₜ.size + 10⟩ := rfl

@[simp] theorem time_iterate_succ {α : Type*} [UniqueEncoding Tree α] (run : α → Costed α)
    (n : ℕ) (a : α) : (iterate run (n + 1) a).cost.time =
      (run a).cost.time + 100 * ⌜n + 1⌝ₜ.size + 420 + (iterate run n (run a).value).cost.time := rfl

@[simp] theorem peak_iterate_succ {α : Type*} [UniqueEncoding Tree α] (run : α → Costed α)
    (n : ℕ) (a : α) : (iterate run (n + 1) a).cost.peak =
      max (20 * ⌜(n + 1, a)⌝ₜ.size + 100)
        (max (2 * (run a).cost.peak) (iterate run n (run a).value).cost.peak) := rfl

theorem size_le_iterate {α : Type*} [UniqueEncoding Tree α] (run : α → Costed α)
    (n : ℕ) (a : α) : 2 * ⌜(n, a)⌝ₜ.size + 10 ≤ (iterate run n a).cost.peak := by
  cases n <;> simp
  omega

end Costed

def Iteration.continues {α : Type*} (x : ℕ × α) := !x.1.bits.isEmpty

theorem Iteration.continues_realizes {α : Type*} [UniqueEncoding Tree α] :
    Realizes (Iteration.continues (α := α))
      ⟨fun _ => 10, fun x => 2 * ⌜x⌝ₜ.size + 10⟩ := by
  refine Realizes.mono (by source_fun_prop) ?_
  rintro ⟨n, a⟩
  cases h : n.bits <;> simp [h] <;> omega

theorem Iteration.step_realizes {α : Type*} [UniqueEncoding Tree α]
    {f : α → α} {b : Bounds α} (hf : Realizes f b) :
    Realizes (fun x : ℕ × α => (x.1.pred, f x.2))
      ⟨fun x => b.time x.2 + 100 * ⌜x.1⌝ₜ.size + 404,
       fun x => max (20 * ⌜x⌝ₜ.size + 100) (2 * b.peak x.2)⟩ := by
  refine Realizes.mono (by source_fun_prop) ?_
  rintro ⟨n, a⟩
  have hp := pred_realizes.size_le n
  have hf := hf.size_le a
  dsimp only at hp
  simp only [compBounds, pairBounds, projectionBounds, size_encode_prod, max_le_iff]
  (repeat' apply And.intro) <;> omega

/-- Compile one callback for every count, retaining the summed evaluation costs. -/
@[simps program evaluate] noncomputable def Implementation.iterate {α : Type*}
    [UniqueEncoding Tree α]
    {f : α → α} (hf : Implementation f) :
    Implementation (fun x : ℕ × α => f^[x.1] x.2) := by
  let hc := (Iteration.continues_realizes (α := α)).implementation
  let hs := (Iteration.step_realizes hf.realizes).implementation
  let eval (x : ℕ × α) := Costed.iterate hf.evaluate x.1 x.2
  refine ⟨loopCode hc.program hs.program (Implementation.snd (α := ℕ) (β := α)).program,
    (fun x => Costed.ofValue (eval x).value ⟨(eval x).cost.time + 17, (eval x).cost.peak⟩),
    (fun x => by simp [eval, hf.value_eq]), ?_⟩
  have hc' := hc.implements
  have hs' := hs.implements
  simp only [hc, hs, Realizes.bounds_implementation] at hc' hs'
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
def iterateCost {α : Type*} [UniqueEncoding Tree α] (f : α → α) (b : Bounds α)
    (n : ℕ) (a : α) : Cost :=
  (Costed.iterate (fun a => Costed.ofValue (f a) ⟨b.time a, b.peak a⟩) n a).cost

@[simp] theorem iterateCost_zero {α : Type*} [UniqueEncoding Tree α] (f : α → α) (b : Bounds α)
    (a : α) : iterateCost f b 0 a = ⟨0, 2 * ⌜((0 : ℕ), a)⌝ₜ.size + 10⟩ := rfl

@[simp] theorem iterateCost_succ {α : Type*} [UniqueEncoding Tree α] (f : α → α) (b : Bounds α)
    (n : ℕ) (a : α) : iterateCost f b (n + 1) a =
      ⟨b.time a + 100 * ⌜n + 1⌝ₜ.size + 420 + (iterateCost f b n (f a)).time,
        max (20 * ⌜(n + 1, a)⌝ₜ.size + 100)
          (max (2 * b.peak a) (iterateCost f b n (f a)).peak)⟩ := rfl

/-- Source invariants bound the accumulated callback times and every intermediate state. -/
theorem iterateCost_le {α : Type*} [UniqueEncoding Tree α] (f : α → α) (b : Bounds α)
    (I : ℕ → α → Prop) (remaining : ℕ → α → ℕ) (space n : ℕ) (a : α)
    (initial : I n a)
    (step : ∀ n a, I (n + 1) a → I n (f a) ∧
      b.time a + 100 * ⌜n + 1⌝ₜ.size + 420 + remaining n (f a) ≤ remaining (n + 1) a ∧
      20 * ⌜(n + 1, a)⌝ₜ.size + 100 ≤ space ∧ 2 * b.peak a ≤ space)
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

@[simps] def iterateBounds {α : Type*} [UniqueEncoding Tree α] (f : α → α)
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

theorem Realizes.iterate {α : Type*} [UniqueEncoding Tree α] {f : α → α}
    {b : Bounds α} (hf : Realizes f b) :
    Realizes (fun x : ℕ × α => f^[x.1] x.2) (iterateBounds f b) := by
  simpa only [Implementation.bounds_iterate, Realizes.bounds_implementation] using
    hf.implementation.iterate.realizes

/-- Compose preparation, a loop retaining its captured environment, and the result projection. -/
@[simps!] def iterateWithBounds {ρ α : Type*} [UniqueEncoding Tree ρ] [UniqueEncoding Tree α]
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

theorem Realizes.iterateWith {ρ α : Type*} [UniqueEncoding Tree ρ] [UniqueEncoding Tree α]
    {f : ρ → α → α} {count : ρ → ℕ} {initial : ρ → α}
    {bi : Bounds ρ} {bs : Bounds (ρ × α)}
    (hi : Realizes (fun e => (count e, (e, initial e))) bi)
    (hs : Realizes (fun x : ρ × α => f x.1 x.2) bs) :
    Realizes (fun e => (f e)^[count e] (initial e)) (iterateWithBounds f count initial bi bs) := by
  simpa only [Implementation.bounds_iterateWith, Realizes.bounds_implementation] using
    (hi.implementation.iterateWith hs.implementation).realizes

-- Realizes rules propagate a requested budget to the callback premises before selection.
-- They also serve native fun_prop, which does not use the source driver's adapters.
attribute [scoped fun_prop] Implementation.iterate Realizes.iterate
  Implementation.iterateWith Realizes.iterateWith

end Complexity.TreeProgram.Source
