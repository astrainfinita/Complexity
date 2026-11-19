/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.Program.Loop

/-! # A counted traversal with a final stopping iteration -/

@[expose] public section

namespace Complexity.Program

open Std.WP

variable {F : Type → Type} {O A Op S : Type} {Ret : Op → Type}

/-- A counted traversal may carry a different remaining-budget invariant at every index.
The dispatcher preserves the invariant at the same budget; each body entry then consumes
one dispatch credit before continuing or stopping. -/
theorem spec_repeatUntilWith_count_of_invariant (a : A) (p : Program F O A Op Ret Bool)
    (e : Semantics O A Op Ret S) (I : ℕ → S → ℕ → Prop) (Q : S → ℕ → Prop) (n : ℕ)
    (ha : ∀ i ≤ n, ∀ c b, I i c b → I i (e.act a c) b)
    (hp : ∀ i ≤ n, ∀ c b, I i c b → 0 < b)
    (hs : ∀ i < n, Triple (p.verify e) (fun c b ↦ I i c (b + 1))
      (fun r c b ↦ r = false ∧ I (i + 1) c b) ())
    (ht : Triple (p.verify e) (fun c b ↦ I n c (b + 1))
      (fun r c b ↦ r = true ∧ Q c b) ()) :
    Triple ((repeatUntilWith a p).verify e) (I 0) (fun _ ↦ Q) () := by
  let J : S → ℕ → Prop := fun c b ↦ ∃ i ≤ n, I i c b
  have h : Triple ((repeatUntilWith a p).verify e) J (fun _ ↦ Q) () := by
    apply spec_repeatUntilWith_of_invariant a p e J _ ()
    · rintro c b ⟨i, hi, hc⟩
      exact ⟨i, hi, ha i hi c b hc⟩
    · rintro c b ⟨i, hi, hc⟩
      exact hp i hi c b hc
    · constructor
      rintro c b ⟨i, hi, hc⟩
      by_cases hn : i < n
      · apply (Triple.entails_wp_of_post (hs i hn) ?_) c b hc
        rintro r d z ⟨rfl, hd⟩
        exact ⟨i + 1, hn, hd⟩
      · have he : i = n := by omega
        subst i
        apply (Triple.entails_wp_of_post ht ?_) c b hc
        rintro r d z ⟨rfl, hd⟩
        exact hd
  constructor
  intro c b hc
  exact h.le_wp c b ⟨0, Nat.zero_le _, hc⟩

/-- A traversal advances through `I 0` to `I n`, then executes its final stopping body.
Each body entry pays one dispatch transition in addition to its specified action cost. -/
theorem spec_repeatUntilWith_count (a : A) (p : Program F O A Op Ret Bool)
    (e : Semantics O A Op Ret S)
    (I : ℕ → S → Prop) (Q : S → Prop) (n u v q : ℕ)
    (ha : ∀ i ≤ n, ∀ c, I i c → I i (e.act a c))
    (hs : ∀ i < n, ∀ q, Triple (p.verify e) (fun c b ↦ I i c ∧ b = u + q)
      (fun r c b ↦ r = false ∧ I (i + 1) c ∧ b = q) ())
    (ht : ∀ q, Triple (p.verify e) (fun c b ↦ I n c ∧ b = v + q)
      (fun r c b ↦ r = true ∧ Q c ∧ b = q) ()) :
    Triple ((repeatUntilWith a p).verify e)
      (fun c b ↦ I 0 c ∧ b = (u + 1) * n + (v + 1) + q)
      (fun _ c b ↦ Q c ∧ b = q) () := by
  apply spec_repeatUntilWith_count_of_invariant a p e
    (fun i c b ↦ I i c ∧ b = (u + 1) * (n - i) + (v + 1) + q) _ n
  · intro i hi c b hc
    exact ⟨ha i hi c hc.1, hc.2⟩
  · rintro i hi c b ⟨hc, hb⟩
    omega
  · intro i hi
    constructor
    rintro c b ⟨hc, hb⟩
    have he : n - i = (n - (i + 1)) + 1 := by omega
    rw [he, Nat.mul_add, Nat.mul_one] at hb
    exact (hs i hi ((u + 1) * (n - (i + 1)) + (v + 1) + q)).le_wp c b
      ⟨hc, by omega⟩
  · constructor
    rintro c b ⟨hc, hb⟩
    simp only [Nat.sub_self, Nat.mul_zero, Nat.zero_add] at hb
    exact (ht q).le_wp c b ⟨hc, by omega⟩

end Complexity.Program
