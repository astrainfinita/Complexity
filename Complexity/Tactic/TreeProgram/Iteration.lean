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
theorem Dominated.iterate_of_potential {ρ : Type*} {t p : α → ℕ}
    (I : ρ → ℕ → α → Prop) (count : ρ → ℕ) (initial : ρ → α)
    (remaining : ρ → ℕ → α → ℕ) (peak : ρ → ℕ)
    (start : ∀ x, I x (count x) (initial x))
    (next : ∀ x n a, I x (n + 1) a → I x n (f a))
    (hround : Dominated
      (fun z : {z : ρ × ℕ × α // I z.1 (z.2.1 + 1) z.2.2} =>
        t z.1.2.2 + ⌜z.1.2.1 + 1⌝ₜ.size)
      (fun z => remaining z.1.1 (z.1.2.1 + 1) z.1.2.2 -
        remaining z.1.1 z.1.2.1 (f z.1.2.2)))
    (hsize : Dominated (fun z : {z : ρ × ℕ × α // I z.1 z.2.1 z.2.2} => ⌜z.1.2⌝ₜ.size)
      (fun z => peak z.1.1))
    (hp : Dominated (fun z : {z : ρ × ℕ × α // I z.1 (z.2.1 + 1) z.2.2} => p z.1.2.2)
      (fun z => peak z.1.1)) :
    Dominated (fun x => iterateTime f t (count x) (initial x))
      (fun x => remaining x (count x) (initial x)) ∧
    Dominated (fun x => iteratePeak f p (count x) (initial x)) peak := by
  obtain ⟨C, hC⟩ := hround
  obtain ⟨D, hD⟩ := hsize
  obtain ⟨P, hP⟩ := hp
  have bound (x : ρ) := iterate_le_of_invariant (f := f) (t := t) (p := p) (I x)
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
theorem Dominated.iterate_of_invariant {ρ : Type*} {t p : α → ℕ}
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
    Dominated (fun x => iterateTime f t (count x) (initial x)) (fun x => count x * time x) ∧
    Dominated (fun x => iteratePeak f p (count x) (initial x)) peak := by
  apply Dominated.iterate_of_potential I count initial (fun x n _ => n * time x) peak start next
    ?_ hsize hp
  let active (z : {z : ρ × ℕ × α // I z.1 (z.2.1 + 1) z.2.2}) :
      {z : ρ × ℕ × α // I z.1 z.2.1 z.2.2} := ⟨(z.1.1, z.1.2.1 + 1, z.1.2.2), z.2⟩
  have hround := ht.add_same (hcount.comp active)
  simpa only [Function.comp_def, active, Nat.add_mul, Nat.one_mul,
    Nat.add_sub_cancel_left] using hround

end Cost

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

def Iteration.continuesImplementation {α : Type*} [UniqueEncoding Tree α] :
    Implementation (Iteration.continues (α := α)) (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  source_fun_prop
  all_goals dominated

/-- One counter step and one callback, with the counter's binary size charged. -/
def Iteration.stepImplementation {α : Type*} [UniqueEncoding Tree α] {f : α → α}
    {t p : α → ℕ} (hf : Implementation f t p) :
    Implementation (fun x : ℕ × α => (x.1.pred, f x.2)) (fun x => ⌜x.1⌝ₜ.size + t x.2)
      (fun x => max ⌜x⌝ₜ.size (p x.2)) := by
  have := Implementation.pred.size_encode.comp (Prod.fst : ℕ × α → ℕ)
  have := hf.size_encode.comp (Prod.snd : ℕ × α → α)
  refine (((Implementation.fst (α := ℕ) (β := α)).comp Implementation.pred).pair
    ((Implementation.snd (α := ℕ) (β := α)).comp hf)).mono ?_ ?_
  all_goals dominated

/-- Compile one callback for every count as a tail loop over the counter and the state. -/
def Implementation.iterate {α : Type*} [UniqueEncoding Tree α] {f : α → α} {t p : α → ℕ}
    (hf : Implementation f t p) :
    Implementation (fun x : ℕ × α => f^[x.1] x.2) (fun x => iterateTime f t x.1 x.2 + 1)
      (fun x => iteratePeak f p x.1 x.2) := by
  let I (x y : ℕ × α) := ∃ k ≤ x.1, y = (x.1 - k, f^[k] x.2)
  have size (z : {p : (ℕ × α) × (ℕ × α) // I p.1 p.2}) :
      ⌜z.1.2⌝ₜ.size ≤ iteratePeak f p z.1.1.1 z.1.1.2 := by
    obtain ⟨k, hk, hy⟩ := z.2
    rw [hy]
    exact size_le_iteratePeak p _ hk
  refine (Implementation.tailLoopPotential (result := fun x : ℕ × α => f^[x.1] x.2)
    Iteration.continuesImplementation (Iteration.stepImplementation hf)
    (Implementation.snd (α := ℕ) (β := α)) I (fun _ y => iterateTime f t y.1 y.2) (fun _ => 1)
    (fun x => iteratePeak f p x.1 x.2) ?_ ?_ ?_ (Dominated.of_le size) (Dominated.of_le size)
    ?_ (Dominated.of_le fun z => size ⟨z.1, z.2.1⟩) (Dominated.of_le_mul 2 fun _ => le_rfl)
    ?_).mono (Dominated.of_le_mul 3 fun x => by omega) (Dominated.refl _)
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
def Implementation.iterateWith {ρ α : Type*} [UniqueEncoding Tree ρ] [UniqueEncoding Tree α]
    {f : ρ → α → α} {count : ρ → ℕ} {initial : ρ → α} {ti pi : ρ → ℕ} {ts ps : ρ × α → ℕ}
    (hi : Implementation (fun e => (count e, (e, initial e))) ti pi)
    (hs : Implementation (fun x : ρ × α => f x.1 x.2) ts ps) :
    Implementation (fun e => (f e)^[count e] (initial e))
      (fun e => ti e + (iterateTime (f e) (fun a => ts (e, a)) (count e) (initial e) + 1))
      (fun e => max (pi e) (⌜e⌝ₜ.size + 1 + iteratePeak (f e)
        (fun a => max ⌜(e, a)⌝ₜ.size (ps (e, a))) (count e) (initial e))) := by
  have hout := hs.size_encode
  let carry : Implementation (fun x : ρ × α => (x.1, f x.1 x.2)) (fun x => ts x + 1)
      (fun x => max ⌜x⌝ₜ.size (ps x)) :=
    ((Implementation.fst (α := ρ) (β := α)).pair hs).mono (by dominated) (by dominated)
  have hiter (n : ℕ) (e : ρ) (a : α) :
      (fun x : ρ × α => (x.1, f x.1 x.2))^[n] (e, a) = (e, (f e)^[n] a) :=
    (Function.Semiconj.iterate_right (f := fun a => (e, a)) (fun _ => rfl) n a).symm
  refine ((hi.comp (carry.iterate.comp (Implementation.snd (α := ρ) (β := α)))).congr ?_).mono
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

attribute [scoped fun_prop] Implementation.iterate Implementation.iterateWith

end Complexity.TreeProgram.Source
