/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Tactic.TreeProgram.Arithmetic

/-! # Counted source iteration

`iterateTime` and `iteratePeak` follow the source iteration: each round charges the callback at
the actual state and the binary counter step, and space is a peak over all stored states. The
implementation is a tail loop over the counter and the state.
-/

@[expose] public section

open Complexity TreeProgram
namespace Complexity.TreeProgram.Source

open Internal (HasProgramInO)

section Cost

variable {α : Type*} [UniqueEncoding Tree α] (f : α → α)

/-- Callback time along a counted iteration, including each binary counter step. -/
def iterateTime (t : α → ℕ) : ℕ → α → ℕ
  | 0, _ => 0
  | n + 1, a => t a + ⌜n + 1⌝ₜ.size + iterateTime t n (f a)

/-- The largest stored state or callback peak along a counted iteration. -/
def iteratePeak (p : α → ℕ) : ℕ → α → ℕ
  | 0, a => ⌜((0 : ℕ), a)⌝ₜ.size
  | n + 1, a => max ⌜(n + 1, a)⌝ₜ.size (max (p a) (iteratePeak p n (f a)))

variable {f}

omit [UniqueEncoding Tree α] in
@[simp] theorem iterateTime_zero (t : α → ℕ) (a : α) : iterateTime f t 0 a = 0 := rfl

omit [UniqueEncoding Tree α] in
@[simp] theorem iterateTime_succ (t : α → ℕ) (n : ℕ) (a : α) :
    iterateTime f t (n + 1) a = t a + ⌜n + 1⌝ₜ.size + iterateTime f t n (f a) := rfl

@[simp] theorem iteratePeak_zero (p : α → ℕ) (a : α) :
    iteratePeak f p 0 a = ⌜((0 : ℕ), a)⌝ₜ.size := rfl

@[simp] theorem iteratePeak_succ (p : α → ℕ) (n : ℕ) (a : α) :
    iteratePeak f p (n + 1) a = max ⌜(n + 1, a)⌝ₜ.size (max (p a) (iteratePeak f p n (f a))) :=
  rfl

omit [UniqueEncoding Tree α] in
/-- Every counter step is charged, so the count is bounded by the time. -/
theorem le_iterateTime (t : α → ℕ) (n : ℕ) (a : α) : n ≤ iterateTime f t n a := by
  induction n generalizing a with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have := ih (f a)
    have := Tree.size_pos ⌜n + 1⌝ₜ
    simp only [iterateTime_succ]
    omega

omit [UniqueEncoding Tree α] in
theorem iterateTime_add_one (t : α → ℕ) (n : ℕ) (a : α) :
    iterateTime f (fun a => t a + 1) n a = iterateTime f t n a + n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp only [iterateTime_succ, ih]; omega

/-- Every state reached after `k` rounds is stored. -/
theorem size_le_iteratePeak (p : α → ℕ) {n k : ℕ} (a : α) (hk : k ≤ n) :
    ⌜(n - k, f^[k] a)⌝ₜ.size ≤ iteratePeak f p n a := by
  induction k generalizing n a with
  | zero => cases n <;> simp
  | succ k ih =>
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have := ih (f a) (n := n) (by omega)
    simp only [Function.iterate_succ_apply, Nat.add_sub_add_right] at this ⊢
    exact this.trans ((le_max_right _ _).trans (le_max_right _ _))

/-- Every executed callback is charged at its actual state. -/
theorem peak_le_iteratePeak (p : α → ℕ) {n k : ℕ} (a : α) (hk : k < n) :
    p (f^[k] a) ≤ iteratePeak f p n a := by
  induction k generalizing n a with
  | zero =>
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact (le_max_left _ _).trans (le_max_right _ _)
  | succ k ih =>
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have := ih (f a) (n := n) (by omega)
    simp only [Function.iterate_succ_apply] at this ⊢
    exact this.trans ((le_max_right _ _).trans (le_max_right _ _))

/-- One source invariant bounds the remaining iteration time and every stored state. -/
theorem iterate_le_of_invariant {t p : α → ℕ} (I : ℕ → α → Prop) (remaining : ℕ → α → ℕ)
    (space n : ℕ) (a : α) (initial : I n a)
    (step : ∀ n a, I (n + 1) a → I n (f a) ∧
      t a + ⌜n + 1⌝ₜ.size + remaining n (f a) ≤ remaining (n + 1) a ∧
      ⌜(n + 1, a)⌝ₜ.size ≤ space ∧ p a ≤ space)
    (stop : ∀ a, I 0 a → ⌜((0 : ℕ), a)⌝ₜ.size ≤ space) :
    I 0 (f^[n] a) ∧ iterateTime f t n a ≤ remaining n a ∧ iteratePeak f p n a ≤ space := by
  induction n generalizing a with
  | zero => simpa using And.intro initial (stop a initial)
  | succ n ih =>
    obtain ⟨hi, ht, hs, hp⟩ := step n a initial
    obtain ⟨hi', ht', hs'⟩ := ih (f a) hi
    simp only [iterateTime_succ, iteratePeak_succ, Function.iterate_succ_apply, max_le_iff]
    exact ⟨hi', by omega, hs, hp, hs'⟩

/-- A potential may depend on the initial input, the remaining count and the current state.
The round and callback comparisons cover the active invariant family with one coefficient;
terminal states only require their stored size. -/
theorem Dominated.iterate_of_potential {ρ : Type*} {f : ρ → α → α} {t p : ρ → α → ℕ}
    (I : ρ → ℕ → α → Prop) (count : ρ → ℕ) (initial : ρ → α)
    (remaining : ρ → ℕ → α → ℕ) (peak : ρ → ℕ)
    (start : ∀ x, I x (count x) (initial x))
    (next : ∀ x n a, I x (n + 1) a → I x n (f x a))
    (hround : Dominated
      (fun z : {z : ρ × ℕ × α // I z.1 (z.2.1 + 1) z.2.2} =>
        t z.1.1 z.1.2.2 + ⌜z.1.2.1 + 1⌝ₜ.size)
      (fun z => remaining z.1.1 (z.1.2.1 + 1) z.1.2.2 -
        remaining z.1.1 z.1.2.1 (f z.1.1 z.1.2.2)))
    (hsize : Dominated (fun z : {z : ρ × ℕ × α // I z.1 z.2.1 z.2.2} => ⌜z.1.2⌝ₜ.size)
      (fun z => peak z.1.1))
    (hp : Dominated (fun z : {z : ρ × ℕ × α // I z.1 (z.2.1 + 1) z.2.2} => p z.1.1 z.1.2.2)
      (fun z => peak z.1.1)) :
    Dominated (fun x => iterateTime (f x) (t x) (count x) (initial x))
      (fun x => remaining x (count x) (initial x)) ∧
    Dominated (fun x => iteratePeak (f x) (p x) (count x) (initial x)) peak := by
  obtain ⟨C, hC⟩ := hround
  obtain ⟨D, hD⟩ := hsize
  obtain ⟨P, hP⟩ := hp
  have bound (x : ρ) := iterate_le_of_invariant (f := f x) (t := t x) (p := p x) (I x)
    (fun n a => C * remaining x n a) ((D + P) * peak x) (count x) (initial x) (start x)
    (fun n a ha => by
      have ht := hC ⟨(x, n, a), ha⟩
      have hs := hD ⟨(x, n + 1, a), ha⟩
      have hq := hP ⟨(x, n, a), ha⟩
      simp only [Nat.nsmul_eq_mul] at ht hs hq
      refine ⟨next x n a ha, ?_, ?_, ?_⟩
      · have := Tree.size_pos ⌜n + 1⌝ₜ
        have := add_mul_le_mul_of_le_mul_tsub (by omega) ht
        omega
      · rw [Nat.add_mul]; omega
      · rw [Nat.add_mul]; omega)
    (fun a ha => by
      have hs := hD ⟨(x, 0, a), ha⟩
      simp only [Nat.nsmul_eq_mul] at hs
      rw [Nat.add_mul]
      omega)
  exact ⟨Dominated.of_le_mul C fun x => (bound x).2.1,
    Dominated.of_le_mul (D + P) fun x => (bound x).2.2⟩

/-- A common round allowance is the potential `remaining count * round allowance`.
Callback allowances are compared only when the remaining count is positive. -/
theorem Dominated.iterate_of_invariant {ρ : Type*} {f : ρ → α → α} {t p : ρ → α → ℕ}
    (I : ρ → ℕ → α → Prop) (count : ρ → ℕ) (initial : ρ → α) (time peak : ρ → ℕ)
    (start : ∀ x, I x (count x) (initial x))
    (next : ∀ x n a, I x (n + 1) a → I x n (f x a))
    (hcount : Dominated (fun z : {z : ρ × ℕ × α // I z.1 z.2.1 z.2.2} => ⌜z.1.2.1⌝ₜ.size)
      (fun z => time z.1.1))
    (hsize : Dominated (fun z : {z : ρ × ℕ × α // I z.1 z.2.1 z.2.2} => ⌜z.1.2⌝ₜ.size)
      (fun z => peak z.1.1))
    (ht : Dominated (fun z : {z : ρ × ℕ × α // I z.1 (z.2.1 + 1) z.2.2} => t z.1.1 z.1.2.2)
      (fun z => time z.1.1))
    (hp : Dominated (fun z : {z : ρ × ℕ × α // I z.1 (z.2.1 + 1) z.2.2} => p z.1.1 z.1.2.2)
      (fun z => peak z.1.1)) :
    Dominated (fun x => iterateTime (f x) (t x) (count x) (initial x))
      (fun x => count x * time x) ∧
    Dominated (fun x => iteratePeak (f x) (p x) (count x) (initial x)) peak := by
  apply Dominated.iterate_of_potential I count initial (fun x n _ => n * time x) peak start next
    ?_ hsize hp
  let active (z : {z : ρ × ℕ × α // I z.1 (z.2.1 + 1) z.2.2}) :
      {z : ρ × ℕ × α // I z.1 z.2.1 z.2.2} := ⟨(z.1.1, z.1.2.1 + 1, z.1.2.2), z.2⟩
  have hround := ht.add_same (hcount.comp active)
  simpa only [Function.comp_def, active, Nat.add_mul, Nat.one_mul,
    Nat.add_sub_cancel_left] using hround

/-- A count polynomial in a scale of the initial input, and stored states and callbacks polynomial
in it over the invariant family, make the iteration polynomial in that scale. -/
theorem IsPoly.iterate_of_invariant {ρ : Type*} {f : ρ → α → α} {t p : ρ → α → ℕ}
    (I : ρ → ℕ → α → Prop) (count : ρ → ℕ) (initial : ρ → α) (S : ρ → ℕ)
    (start : ∀ x, I x (count x) (initial x))
    (next : ∀ x n a, I x (n + 1) a → I x n (f x a))
    (hcount : IsPoly S count)
    (hsize : IsPoly (fun z : {z : ρ × ℕ × α // I z.1 z.2.1 z.2.2} => S z.1.1)
      fun z => ⌜z.1.2⌝ₜ.size)
    (ht : IsPoly (fun z : {z : ρ × ℕ × α // I z.1 (z.2.1 + 1) z.2.2} => S z.1.1)
      fun z => t z.1.1 z.1.2.2)
    (hp : IsPoly (fun z : {z : ρ × ℕ × α // I z.1 (z.2.1 + 1) z.2.2} => S z.1.1)
      fun z => p z.1.1 z.1.2.2) :
    IsPoly S (fun x => iterateTime (f x) (t x) (count x) (initial x)) ∧
    IsPoly S (fun x => iteratePeak (f x) (p x) (count x) (initial x)) := by
  obtain ⟨d₁, h₁⟩ := hsize
  obtain ⟨d₂, h₂⟩ := ht
  obtain ⟨d₃, h₃⟩ := hp
  let D := d₁ + d₂ + d₃
  have lift {γ : Type _} {s t : γ → ℕ} {d : ℕ} (h : Dominated t fun x => (s x + 1) ^ d)
      (hd : d ≤ D) : Dominated t fun x => (s x + 1) ^ D :=
    h.mono_pow hd fun _ => Nat.succ_pos _
  have hcounter : Dominated (fun z : {z : ρ × ℕ × α // I z.1 z.2.1 z.2.2} => ⌜z.1.2.1⌝ₜ.size)
      (fun z => ⌜z.1.2⌝ₜ.size) := Dominated.of_le fun z => by
    simp only [Prod.size_encode_eq]
    omega
  have h := Dominated.iterate_of_invariant (f := f) (t := t) (p := p) I count initial
    (fun x => (S x + 1) ^ D) (fun x => (S x + 1) ^ D) start next
    (hcounter.trans (lift h₁ (by omega))) (lift h₁ (by omega)) (lift h₂ (by omega))
    (lift h₃ (by omega))
  have hD : IsPoly S fun x => (S x + 1) ^ D := (IsPoly.refl.add (.const 1)).pow D
  exact ⟨(hcount.mul hD).of_dominated h.1, hD.of_dominated h.2⟩

end Cost

section Reached

variable {ε α : Type*} [UniqueEncoding Tree α] {s : ε → ℕ} {f : ε → α → α} {n : ε → ℕ}
  {a : ε → α}

/-- An iteration is polynomial in a measure `s` of its input when its callbacks are polynomial in
`s` and the codes of their arguments, the states it reaches within its count are polynomial in
`s`, and so is its count. The invariant is that the state is reached after the rounds done. -/
theorem IsPoly.iterate_of_reached {t p : ε → α → ℕ}
    (ht : IsPoly (fun z : ε × α => s z.1 + ⌜z.2⌝ₜ.size) fun z => t z.1 z.2)
    (hp : IsPoly (fun z : ε × α => s z.1 + ⌜z.2⌝ₜ.size) fun z => p z.1 z.2)
    (hstate : IsPoly (fun z : {z : ε × ℕ // z.2 ≤ n z.1} => s z.1.1)
      fun z => ⌜(f z.1.1)^[z.1.2] (a z.1.1)⌝ₜ.size)
    (hn : IsPoly s n) :
    IsPoly s (fun x => iterateTime (f x) (t x) (n x) (a x)) ∧
      IsPoly s (fun x => iteratePeak (f x) (p x) (n x) (a x)) := by
  let I x m b := ∃ k, k + m = n x ∧ (f x)^[k] (a x) = b
  have hb := hstate.comp (h := fun z : {z : ε × ℕ × α // I z.1 z.2.1 z.2.2} =>
    ⟨(z.1.1, z.2.choose), (Nat.le_add_right _ _).trans_eq z.2.choose_spec.1⟩) IsPoly.refl
  have hm := hn.comp (h := fun z : {z : ε × ℕ × α // I z.1 z.2.1 z.2.2} => z.1.1) IsPoly.refl
  have hsize : IsPoly (fun z : {z : ε × ℕ × α // I z.1 z.2.1 z.2.2} => s z.1.1)
      fun z => ⌜z.1.2⌝ₜ.size := by
    refine ((((IsPoly.const 1).add (hm.mul (.const 4))).add (.const 1)).add hb).of_dominated
      (Dominated.of_le fun z => ?_)
    have := size_encode_nat_le z.1.2.1
    have := z.2.choose_spec.1
    simp only [Prod.size_encode_eq, z.2.choose_spec.2]
    omega
  have hstep : IsPoly (fun z : {z : ε × ℕ × α // I z.1 (z.2.1 + 1) z.2.2} => s z.1.1)
      fun z => s z.1.1 + ⌜z.1.2.2⌝ₜ.size :=
    IsPoly.refl.add ((hsize.comp (h := fun z : {z : ε × ℕ × α // I z.1 (z.2.1 + 1) z.2.2} =>
      ⟨(z.1.1, z.1.2.1 + 1, z.1.2.2), z.2⟩) IsPoly.refl).of_dominated
        (Dominated.of_le fun z => by simp only [Prod.size_encode_eq]; omega))
  let step (z : {z : ε × ℕ × α // I z.1 (z.2.1 + 1) z.2.2}) : ε × α := (z.1.1, z.1.2.2)
  exact IsPoly.iterate_of_invariant I n a s (fun _ => ⟨0, by simp, rfl⟩)
    (fun x m b ⟨k, h, hb⟩ => ⟨k + 1, by omega, by rw [Function.iterate_succ_apply', hb]⟩)
    hn hsize (ht.comp (h := step) hstep) (hp.comp (h := step) hstep)

/-- The time of `IsPoly.iterate_of_reached`, for a goal about the time alone. The premises come in
the order `dominated` tries them, the reached states first: they fail when no bound is known. -/
@[dominated_traversal] theorem IsPoly.iterateTime {t : ε → α → ℕ}
    (hstate : IsPoly (fun z : {z : ε × ℕ // z.2 ≤ n z.1} => s z.1.1)
      fun z => ⌜(f z.1.1)^[z.1.2] (a z.1.1)⌝ₜ.size)
    (hn : IsPoly s n)
    (ht : IsPoly (fun z : ε × α => s z.1 + ⌜z.2⌝ₜ.size) fun z => t z.1 z.2) :
    IsPoly s fun x => iterateTime (f x) (t x) (n x) (a x) :=
  (IsPoly.iterate_of_reached (p := fun _ _ => 0) ht (.const 0) hstate hn).1

/-- The peak of `IsPoly.iterate_of_reached`, for a goal about the peak alone, with the premises of
`IsPoly.iterateTime`. -/
@[dominated_traversal] theorem IsPoly.iteratePeak {p : ε → α → ℕ}
    (hstate : IsPoly (fun z : {z : ε × ℕ // z.2 ≤ n z.1} => s z.1.1)
      fun z => ⌜(f z.1.1)^[z.1.2] (a z.1.1)⌝ₜ.size)
    (hn : IsPoly s n)
    (hp : IsPoly (fun z : ε × α => s z.1 + ⌜z.2⌝ₜ.size) fun z => p z.1 z.2) :
    IsPoly s fun x => iteratePeak (f x) (p x) (n x) (a x) :=
  (IsPoly.iterate_of_reached (t := fun _ _ => 0) (.const 0) hp hstate hn).2

/-- The peak of an iteration is linear in a measure `s` of its input when the peak of its callback
is linear in `s` and the code of its argument, and the states it reaches within its count, and the
code of the count, are linear in `s`. The stored counters have no more bits than the count. -/
@[dominated_traversal] theorem Dominated.iteratePeak_of_reached {p : ε → α → ℕ}
    (hstate : Dominated (fun z : {z : ε × ℕ // z.2 ≤ n z.1} =>
      ⌜(f z.1.1)^[z.1.2] (a z.1.1)⌝ₜ.size) fun z => s z.1.1)
    (hn : Dominated (fun x => ⌜n x⌝ₜ.size) s)
    (hp : Dominated (fun z : ε × α => p z.1 z.2) fun z => s z.1 + ⌜z.2⌝ₜ.size) :
    Dominated (fun x => iteratePeak (f x) (p x) (n x) (a x)) s := by
  let I x m b := ∃ k, k + m = n x ∧ (f x)^[k] (a x) = b
  have hcount : Dominated (fun z : {z : ε × ℕ × α // I z.1 z.2.1 z.2.2} => ⌜z.1.2.1⌝ₜ.size)
      fun z => s z.1.1 := by
    refine (Dominated.of_le_mul 5 fun z => ?_).trans
      (hn.comp fun z : {z : ε × ℕ × α // I z.1 z.2.1 z.2.2} => z.1.1)
    obtain ⟨k, hk, -⟩ := z.2
    have := Nat.length_bits_le_length_bits ((Nat.le_add_left z.1.2.1 k).trans_eq hk)
    have := size_encode_nat_le_length_bits z.1.2.1
    have := length_bits_le_size_encode (n z.1.1)
    have := Tree.size_pos ⌜n z.1.1⌝ₜ
    simp only [Function.comp_apply]
    omega
  have hsize : Dominated (fun z : {z : ε × ℕ × α // I z.1 z.2.1 z.2.2} => ⌜z.1.2⌝ₜ.size)
      fun z => s z.1.1 := by
    have hb := hstate.comp fun z : {z : ε × ℕ × α // I z.1 z.2.1 z.2.2} =>
      ⟨(z.1.1, z.2.choose), (Nat.le_add_right _ _).trans_eq z.2.choose_spec.1⟩
    refine ((hcount.add_same hcount).add_same hb).mono_left fun z => ?_
    have := Tree.size_pos ⌜z.1.2.1⌝ₜ
    simp only [Function.comp_apply, Prod.size_encode_eq, z.2.choose_spec.2]
    omega
  have hstep : Dominated (fun z : {z : ε × ℕ × α // I z.1 (z.2.1 + 1) z.2.2} =>
      s z.1.1 + ⌜z.1.2.2⌝ₜ.size) fun z => s z.1.1 :=
    (Dominated.refl _).add_same ((hsize.comp fun z : {z : ε × ℕ × α //
      I z.1 (z.2.1 + 1) z.2.2} => ⟨(z.1.1, z.1.2.1 + 1, z.1.2.2), z.2⟩).mono_left
      fun z => by simp only [Function.comp_apply, Prod.size_encode_eq]; omega)
  exact (Dominated.iterate_of_invariant (t := fun _ _ => 0) I n a s s
    (fun _ => ⟨0, by simp, rfl⟩)
    (fun x m b ⟨k, h, hb⟩ => ⟨k + 1, by omega, by rw [Function.iterate_succ_apply', hb]⟩)
    hcount hsize (Dominated.of_le fun _ => Nat.zero_le _)
    ((hp.comp fun z : {z : ε × ℕ × α // I z.1 (z.2.1 + 1) z.2.2} =>
      (z.1.1, z.1.2.2)).trans hstep)).2

end Reached

section Lift

variable {ρ α : Type*} [UniqueEncoding Tree ρ] [UniqueEncoding Tree α] (g : ρ → α → α)

omit [UniqueEncoding Tree ρ] [UniqueEncoding Tree α] in
/-- An iteration whose state also carries a fixed environment charges the same callbacks. -/
theorem iterateTime_lift (t : ρ × α → ℕ) (n : ℕ) (e : ρ) (a : α) :
    iterateTime (fun x : ρ × α => (x.1, g x.1 x.2)) t n (e, a) =
      iterateTime (g e) (fun a => t (e, a)) n a := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp only [iterateTime_succ, ih]

/-- An iteration whose state carries a fixed environment stores it once more in every state. -/
theorem iteratePeak_lift_le (p : ρ × α → ℕ) (n : ℕ) (e : ρ) (a : α) :
    iteratePeak (fun x : ρ × α => (x.1, g x.1 x.2)) p n (e, a) ≤
      ⌜e⌝ₜ.size + 1 + iteratePeak (g e) (fun a => p (e, a)) n a := by
  induction n generalizing a with
  | zero => simp only [iteratePeak_zero, size_encode_prod]; omega
  | succ n ih =>
    have := ih (g e a)
    simp only [iteratePeak_succ, size_encode_prod, max_le_iff] at this ⊢
    omega

end Lift

/-- The test of the counted iteration: whether the counter, read through its binary digits, is
nonzero. -/
def Iteration.continues {α : Type*} (x : ℕ × α) := !x.1.bits.isEmpty

theorem Iteration.continues_eq_true {α : Type*} (x : ℕ × α) :
    Iteration.continues x = true ↔ x.1 ≠ 0 := by
  rcases x with ⟨n, a⟩
  cases n with
  | zero => simp [Iteration.continues]
  | succ n =>
    have hbits : (n + 1).bits ≠ [] := by
      intro h; have := BitList.toNat_bits (n + 1); simp [h, BitList.toNat] at this
    simp [Iteration.continues, hbits]

theorem Iteration.hasProgramIn_continues {α : Type*} [UniqueEncoding Tree α] :
    HasProgramIn (Iteration.continues (α := α)) hole(⊢ program) IsO(fun _ => 1)
      IsO(fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programContinues
  fill_hole program in source_fun_prop

/-- One counter step and one callback, with the counter's binary size charged. -/
theorem Internal.HasProgramInO.iteration_step {α : Type*} [UniqueEncoding Tree α] {f : α → α}
    {qf : Value → Code Value} {t p : α → ℕ} (hf : HasProgramInO f qf t p) :
    HasProgramInO (fun x : ℕ × α => (x.1.pred, f x.2)) hole(qf ⊢ program)
      (fun x => ⌜x.1⌝ₜ.size + t x.2) (fun x => max ⌜x⌝ₜ.size (p x.2)) := by
  have := Nat.hasProgramIn_pred.toHasProgramInO.size_encode.comp (Prod.fst : ℕ × α → ℕ)
  have := hf.size_encode.comp (Prod.snd : ℕ × α → α)
  fill_hole program in
    refine ((Prod.hasProgramIn_fst.toHasProgramInO.comp Nat.hasProgramIn_pred.toHasProgramInO).pair
      (Prod.hasProgramIn_snd.toHasProgramInO.comp hf)).mono ?_ ?_
  all_goals dominated

/-- Compile one callback for every count as a tail loop over the counter and the state. -/
theorem Internal.HasProgramInO.iterate {α : Type*} [UniqueEncoding Tree α] {f : α → α}
    {qf : Value → Code Value} {t p : α → ℕ} (hf : HasProgramInO f qf t p) :
    HasProgramInO (fun x : ℕ × α => f^[x.1] x.2) hole(qf ⊢ program)
      (fun x => iterateTime f t x.1 x.2 + 1) (fun x => iteratePeak f p x.1 x.2) := by
  let I (x y : ℕ × α) := ∃ k ≤ x.1, y = (x.1 - k, f^[k] x.2)
  have size (z : {p : (ℕ × α) × (ℕ × α) // I p.1 p.2}) :
      ⌜z.1.2⌝ₜ.size ≤ iteratePeak f p z.1.1.1 z.1.1.2 := by
    obtain ⟨k, hk, hy⟩ := z.2
    rw [hy]
    exact size_le_iteratePeak p _ hk
  fill_hole program in
    refine (HasProgramInO.tail_loop_potential Iteration.hasProgramIn_continues.toHasProgramInO
      hf.iteration_step
      Prod.hasProgramIn_snd.toHasProgramInO I (fun _ y => iterateTime f t y.1 y.2)
      (fun _ => 1) (fun x => iteratePeak f p x.1 x.2) ?_ ?_ ?_ (Dominated.of_le size)
      (Dominated.of_le size) ?_ (Dominated.of_le fun z => size ⟨z.1, z.2.1⟩)
      (Dominated.of_le_mul 2 fun _ => le_rfl) ?_).mono (Dominated.of_le_mul 3 fun x => by omega)
      (Dominated.refl _)
  · rintro ⟨n, a⟩
    cases n with
    | zero => simp [Iteration.continues]
    | succ n =>
      simp [(Iteration.continues_eq_true (n + 1, a)).mpr (Nat.succ_ne_zero n),
        Function.iterate_succ_apply]
  · intro x
    exact ⟨0, Nat.zero_le _, rfl⟩
  · rintro x y ⟨k, hk, rfl⟩ ht
    have hn := (Iteration.continues_eq_true _).mp ht
    refine ⟨k + 1, by simp only at hn; omega, ?_⟩
    simp only [Function.iterate_succ_apply', Nat.pred_eq_sub_one, Prod.mk.injEq, and_true]
    omega
  · apply Dominated.of_le
    intro z
    obtain ⟨k, hk, hy⟩ := z.2.1
    have hn := (Iteration.continues_eq_true _).mp z.2.2
    change max ⌜z.1.2⌝ₜ.size (p z.1.2.2) ≤ iteratePeak f p z.1.1.1 z.1.1.2
    rw [hy] at hn ⊢
    simp only at hn
    exact max_le (size_le_iteratePeak p _ hk) (peak_le_iteratePeak p _ (by omega))
  · apply Dominated.of_le_mul 3
    rintro ⟨⟨x, ⟨n, a⟩⟩, -, ht⟩
    have hn := (Iteration.continues_eq_true _).mp ht
    simp only at hn ⊢
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have := Tree.size_pos ⌜n + 1⌝ₜ
    simp only [iterateTime_succ, Nat.pred_succ]
    omega

/-- Captured values stay in the loop state; one callback covers all runtime environments. -/
theorem Internal.HasProgramInO.iterate_with {ρ α : Type*} [UniqueEncoding Tree ρ]
    [UniqueEncoding Tree α]
    {f : ρ → α → α} {count : ρ → ℕ} {initial : ρ → α} {qi qs : Value → Code Value}
    {ti pi : ρ → ℕ} {ts ps : ρ × α → ℕ}
    (hi : HasProgramInO (fun e => (count e, (e, initial e))) qi ti pi)
    (hs : HasProgramInO (fun x : ρ × α => f x.1 x.2) qs ts ps) :
    HasProgramInO (fun e => (f e)^[count e] (initial e)) hole(qi, qs ⊢ program)
      (fun e => ti e + (iterateTime (f e) (fun a => ts (e, a)) (count e) (initial e) + 1))
      (fun e => max (pi e) (⌜e⌝ₜ.size + 1 + iteratePeak (f e)
        (fun a => max ⌜(e, a)⌝ₜ.size (ps (e, a))) (count e) (initial e))) := by
  have hout := hs.size_encode
  have carry : HasProgramInO (fun x : ρ × α => (x.1, f x.1 x.2)) _ (fun x => ts x + 1)
      (fun x => max ⌜x⌝ₜ.size (ps x)) :=
    (Prod.hasProgramIn_fst.toHasProgramInO.pair hs).mono (by dominated) (by dominated)
  have hiter (n : ℕ) (e : ρ) (a : α) :
      (fun x : ρ × α => (x.1, f x.1 x.2))^[n] (e, a) = (e, (f e)^[n] a) :=
    (Function.Semiconj.iterate_right (f := fun a => (e, a)) (fun _ => rfl) n a).symm
  fill_hole program in
    refine ((hi.comp (carry.iterate.comp Prod.hasProgramIn_snd.toHasProgramInO)).congr ?_).mono
      ?_ ?_
  · funext e
    simp only [Function.comp_apply, hiter]
  · apply Dominated.of_le_mul 2
    intro e
    have := le_iterateTime (f := f e) (fun a => ts (e, a)) (count e) (initial e)
    simp only [iterateTime_lift, iterateTime_add_one]
    omega
  · apply Dominated.of_le_mul 3
    intro e
    have hlift := iteratePeak_lift_le f (fun x => max ⌜x⌝ₜ.size (ps x)) (count e) e (initial e)
    have hlast := size_le_iteratePeak (f := fun x : ρ × α => (x.1, f x.1 x.2))
      (fun x => max ⌜x⌝ₜ.size (ps x)) (e, initial e) (le_refl (count e))
    simp only [hiter, Nat.sub_self, size_encode_prod] at hlast
    simp only [hiter, max_le_iff, size_encode_prod] at hlift ⊢
    omega

attribute [fun_prop] HasProgramInO.iterate HasProgramInO.iterate_with

end Complexity.TreeProgram.Source
