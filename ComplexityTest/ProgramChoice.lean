/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

import Complexity.Control.BinaryChoice.Basic
import Complexity.Control.Program.Correctness
import Complexity.Models.StackMachine.Program.Basic

set_option experimental.vcgen true

open Complexity Std.WP
open Complexity.StackMachine (Cfg)
open Complexity.StackMachine.Program

namespace ProgramChoiceTest

/-- A deterministic preparation: push the marker `false`. -/
def prep : StackMachine.Program Id (Fin 1) Bool Unit := push 0 false

@[spec] theorem prep_spec (xs : Array Bool) (s : Cfg (Fin 1) Bool xs) (b : ℕ) (h : 0 < b) :
    Triple (prep.verify (semantics xs)) (fun t c ↦ t = s ∧ c = b)
      (fun _ t c ↦ t = s.setStack 0 (false :: s.stacks 0) ∧ c = b - 1) () := by
  unfold prep
  vcgen
  all_goals simp_all

/-- A deterministic check: whether the top of the stack is `true`. -/
def check : StackMachine.Program Id (Fin 1) Bool Bool := do
  let r ← read 0
  pure (r == some true)

@[spec] theorem check_spec (xs : Array Bool) (s : Cfg (Fin 1) Bool xs) (b : ℕ) (h : 0 < b) :
    Triple (check.verify (semantics xs)) (fun t c ↦ t = s ∧ c = b)
      (fun r t c ↦ r = ((s.stacks 0).head? == some true) ∧ t = s ∧ c = b - 1) () := by
  unfold check
  vcgen
  all_goals simp_all

/-- Guess `n` bits, pushing each, between the two deterministic parts. It accepts exactly when
the last guess is `true`, which some branch reaches if and only if `0 < n`. -/
def verifier (n : ℕ) : StackMachine.Program BinaryChoice (Fin 1) Bool Bool := do
  prep.ofId
  let _ ← Program.loop idle (fun i : Fin (n + 1) ↦
    if h : i.val < n then do
      let c ← choose fun j : Fin 2 ↦ j == 1
      push 0 c
      pure (.inl ⟨i.val + 1, by omega⟩)
    else pure (.inr (0 : Fin 1))) 0
  check.ofId

-- Guards that under `MonadQuant.all`, with the choices interpreted in `Multiset`, the registered
-- rules of `prep`, `choose` and `check` fire: neither deterministic part is unfolded and no
-- quantifier over the choices is split by hand.
theorem verifier_all (n : ℕ) (xs : Array Bool) (s₀ : Cfg (Fin 1) Bool xs) :
    Triple ((verifier n).verifyWith Multiset .all (semantics xs))
      (fun s b ↦ s = s₀ ∧ 3 * n + 3 ≤ b) (fun ok _ _ ↦ ok = true → 0 < n) () := by
  unfold verifier
  vcgen invariants
  | inv1 => fun i t c ↦ 3 * (n - i) + 2 ≤ c ∧ ((t.stacks 0).head? = some true → 0 < n)
  -- Records a limit shared with `verify`: the loop exit leaves its continuation `check.ofId` as a
  -- raw `wp`, for a second `vcgen`.
  case vc6 =>
    obtain ⟨_, _, rfl⟩ := ‹∃ t, _›
    vcgen
    all_goals first | omega | (simp_all; try omega)
  all_goals first | omega | (simp_all; try omega)

-- Guards that under `MonadQuant.any` the rule `spec_choose_any`, given the choice `true`, continues
-- after `choose` without a goal left under the quantifier.
theorem verifier_any (n : ℕ) (hn : 0 < n) (xs : Array Bool) (s₀ : Cfg (Fin 1) Bool xs) :
    Triple ((verifier n).verifyWith Multiset .any (semantics xs))
      (fun s b ↦ s = s₀ ∧ b = 3 * n + 3) (fun ok _ _ ↦ ok = true) () := by
  unfold verifier
  vcgen [spec_choose_any (F := BinaryChoice) (m := Multiset) (fun j ↦ j == 1) true (by simp)]
    invariants
  | inv1 => fun i t c ↦ c = 3 * (n - i) + 2 ∧ (n ≤ i.val → (t.stacks 0).head? = some true)
  case vc6 =>
    obtain ⟨_, _, rfl⟩ := ‹∃ t, _›
    vcgen
    all_goals first | omega | (simp_all; try omega)
  all_goals first | omega | (simp_all; try omega)

-- Guards the passage of both specifications to the compiled machine run on `Multiset`, stated as
-- the plain facts about the configurations it can return: after the budget, every branch has
-- halted at an exit whose answer is sound, ...
example (n : ℕ) (xs : List Bool) :
    ∀ cfg ∈ returns ((compile (verifier n)).runWith Multiset xs (3 * n + 3)),
      ∃ e t, cfg = (.inr e, t) ∧ ∃ b ≤ 3 * n + 3, (verifier n).result e = true → 0 < n :=
  Program.Syntax.ExecWithinWith.runFromWith_compile eval idle
    ((verifier_all n _ _).le_wp (Cfg.init (Fin 1) xs) _ ⟨rfl, le_rfl⟩)

-- ... and for `0 < n` some branch has halted at an exit whose answer is `true`.
example (n : ℕ) (hn : 0 < n) (xs : List Bool) :
    ∃ cfg ∈ returns ((compile (verifier n)).runWith Multiset xs (3 * n + 3)),
      ∃ e t, cfg = (.inr e, t) ∧ ∃ b ≤ 3 * n + 3, (verifier n).result e = true :=
  Program.Syntax.ExecWithinWith.runFromWith_compile eval idle
    ((verifier_any n hn _ _).le_wp (Cfg.init (Fin 1) xs) _ ⟨rfl, rfl⟩)

/-- A deterministic program choosing from the single alternative of a choice of shape `Id`. -/
def pickTrue : StackMachine.Program Id (Fin 1) Bool Unit := do
  let c ← choose (Pure.pure true : Id Bool)
  push 0 c

-- Guards that a choice of shape `Id` in a deterministic program is verified with `verify` by the
-- registered rule of `choose`, whose only choice is the alternative.
theorem pickTrue_spec (xs : Array Bool) (s : Cfg (Fin 1) Bool xs) :
    Triple (pickTrue.verify (semantics xs)) (fun t b ↦ t = s ∧ b = 2)
      (fun _ t b ↦ t = s.setStack 0 (true :: s.stacks 0) ∧ b = 0) () := by
  unfold pickTrue
  vcgen
  all_goals simp_all

/-! ## Alternating choices: a quantifier without `MonadReturns` -/

namespace Alternating

/-- Results with universal and existential branching. -/
inductive AltTree (α : Type) where
  | pure (a : α)
  | all (t : Fin 2 → AltTree α)
  | any (t : Fin 2 → AltTree α)

/-- Substitute each result. -/
def AltTree.bind {α β : Type} : AltTree α → (α → AltTree β) → AltTree β
  | .pure a, f => f a
  | .all t, f => .all fun i ↦ (t i).bind f
  | .any t, f => .any fun i ↦ (t i).bind f

instance : Monad AltTree where
  pure := .pure
  bind := AltTree.bind

theorem AltTree.bind_pure {α : Type} (x : AltTree α) : x.bind .pure = x := by
  induction x with | pure => rfl | all _ ih | any _ ih => simp only [AltTree.bind, ih]

theorem AltTree.bind_assoc {α β γ : Type} (x : AltTree α) (f : α → AltTree β)
    (g : β → AltTree γ) : (x.bind f).bind g = x.bind fun a ↦ (f a).bind g := by
  induction x with | pure => rfl | all _ ih | any _ ih => simp only [AltTree.bind, ih]

instance : LawfulMonad AltTree := .mk' _ AltTree.bind_pure (fun _ _ ↦ rfl) AltTree.bind_assoc

/-- The value of the game for `P`: the first player picks at `any`, the second at `all`. -/
def AltTree.Eval ⦃α : Type⦄ (P : α → Prop) : AltTree α → Prop
  | .pure a => P a
  | .all t => ∀ i, Eval P (t i)
  | .any t => ∃ i, Eval P (t i)

/-- The dual reading, with the players exchanged: `EvalDual P x ↔ ¬ Eval (¬ P ·) x`. -/
def AltTree.EvalDual ⦃α : Type⦄ (P : α → Prop) : AltTree α → Prop
  | .pure a => P a
  | .all t => ∃ i, EvalDual P (t i)
  | .any t => ∀ i, EvalDual P (t i)

/-- The quantifier `AltTree.Eval`. -/
def AltTree.eval : MonadQuant AltTree where
  toFun := AltTree.Eval
  mono {_ _ _ x} h := by
    induction x with
    | pure a => exact h a
    | all t ih => exact fun hx i ↦ ih i (hx i)
    | any t ih => exact fun ⟨i, hi⟩ ↦ ⟨i, ih i hi⟩
  pure_iff := Iff.rfl
  bind_iff {_ _ _ x _} := by
    induction x with
    | pure => exact Iff.rfl
    | all t ih => exact forall_congr' ih
    | any t ih => exact exists_congr ih

/-- The quantifier `AltTree.EvalDual`. -/
def AltTree.evalDual : MonadQuant AltTree where
  toFun := AltTree.EvalDual
  mono {_ _ _ x} h := by
    induction x with
    | pure a => exact h a
    | all t ih => exact fun ⟨i, hi⟩ ↦ ⟨i, ih i hi⟩
    | any t ih => exact fun hx i ↦ ih i (hx i)
  pure_iff := Iff.rfl
  bind_iff {_ _ _ x _} := by
    induction x with
    | pure => exact Iff.rfl
    | all t ih => exact exists_congr ih
    | any t ih => exact forall_congr' ih

/-- One alternating step: two alternatives for the universal or for the existential player. -/
inductive AltChoice (α : Type) where
  | all (f : Fin 2 → α)
  | any (f : Fin 2 → α)

instance : Functor AltChoice where
  map f
    | .all g => .all (f ∘ g)
    | .any g => .any (f ∘ g)

instance : Pure AltChoice where
  pure a := .all fun _ ↦ a

instance : MonadLift AltChoice AltTree where
  monadLift
    | .all g => .all fun i ↦ .pure (g i)
    | .any g => .any fun i ↦ .pure (g i)

instance : LawfulFunctorLift AltChoice AltTree where
  monadLift_map _ x := by cases x <;> rfl

@[simp] theorem eval_monadLift_all {α : Type} {P : α → Prop} {g : Fin 2 → α} :
    AltTree.eval P (monadLift (AltChoice.all g) : AltTree α) ↔ ∀ i, P (g i) := Iff.rfl

@[simp] theorem eval_monadLift_any {α : Type} {P : α → Prop} {g : Fin 2 → α} :
    AltTree.eval P (monadLift (AltChoice.any g) : AltTree α) ↔ ∃ i, P (g i) := Iff.rfl

@[simp] theorem evalDual_monadLift_all {α : Type} {P : α → Prop} {g : Fin 2 → α} :
    AltTree.evalDual P (monadLift (AltChoice.all g) : AltTree α) ↔ ∃ i, P (g i) := Iff.rfl

@[simp] theorem evalDual_monadLift_any {α : Type} {P : α → Prop} {g : Fin 2 → α} :
    AltTree.evalDual P (monadLift (AltChoice.any g) : AltTree α) ↔ ∀ i, P (g i) := Iff.rfl

instance : MonadQuant.PureLift AltChoice AltTree AltTree.eval where
  monadLift_pure_iff := ⟨fun h ↦ h 0, fun h _ ↦ h⟩

instance : MonadQuant.PureLift AltChoice AltTree AltTree.evalDual where
  monadLift_pure_iff := ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨0, h⟩⟩

/-- The first player picks `a`, then the second player picks `b`; the answer is `a || b`. -/
def game : StackMachine.Program AltChoice (Fin 1) Bool Bool := do
  let a ← choose (AltChoice.any fun i : Fin 2 ↦ i == 1)
  let b ← choose (AltChoice.all fun i : Fin 2 ↦ i == 1)
  pure (a || b)

-- Guards that `verifyWith` reads the choices through a quantifier of a monad without
-- `MonadReturns`, with the general rule `spec_choose`: the first player can force `true`.
theorem game_eval (xs : Array Bool) (s₀ : Cfg (Fin 1) Bool xs) :
    Triple (game.verifyWith AltTree AltTree.eval (semantics xs)) (fun s b ↦ s = s₀ ∧ b = 2)
      (fun r _ _ ↦ r = true) () := by
  unfold game
  vcgen [spec_choose]
  simp only [eval_monadLift_any]
  refine ⟨by omega, 1, ?_⟩
  vcgen [spec_choose]
  simp only [eval_monadLift_all]
  refine ⟨by omega, fun _ ↦ ?_⟩
  vcgen
  simp

-- Guards the dual reading of the same program: the second player can also force `true`
-- (so the first player cannot force `false`).
example (xs : Array Bool) (s₀ : Cfg (Fin 1) Bool xs) :
    Triple (game.verifyWith AltTree AltTree.evalDual (semantics xs)) (fun s b ↦ s = s₀ ∧ b = 2)
      (fun r _ _ ↦ r = true) () := by
  unfold game
  vcgen [spec_choose]
  simp only [evalDual_monadLift_any]
  refine ⟨by omega, fun _ ↦ ?_⟩
  vcgen [spec_choose]
  simp only [evalDual_monadLift_all]
  refine ⟨by omega, 1, ?_⟩
  vcgen
  simp

-- Guards the passage to the compiled machine run on `AltTree`.
example (xs : List Bool) :
    AltTree.Eval (fun cfg ↦ ∃ e t, cfg = (.inr e, t) ∧ ∃ b ≤ 2, game.result e = true)
      ((compile game).runWith AltTree xs 2) :=
  Program.Syntax.ExecWithinWith.runFromWith_compile eval idle
    ((game_eval _ _).le_wp (Cfg.init (Fin 1) xs) _ ⟨rfl, rfl⟩)

end Alternating

end ProgramChoiceTest
