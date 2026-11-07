/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Tactic.TreeProgram.Rules

/-! # Certified recursion with one recursive call per branch

The return type may depend on the input. Proof-constrained callbacks operate only on their
reachable inputs; the compiled program stores source arguments on a stack and erases the proofs.
-/

@[expose] public section

namespace Complexity.TreeProgram.Source

open Internal (HasProgram)

/-- Sequential time and the maximum size of an intermediate tree. -/
@[ext] structure Cost where
  /-- Time spent by an evaluation. -/
  time : ℕ
  /-- Largest intermediate tree of an evaluation. -/
  peak : ℕ

/-- A source recursion equation, including the work performed after the recursive return. -/
structure Recursion {α : Type*} {β : α → Type*} (f : (x : α) → β x) where
  test : α → Bool
  next : α → α
  finish : (x : {x // test x = false}) → β x.val
  resume : (x : {x // test x = true}) → β (next x.val) → β x.val
  finish_eq : ∀ x, finish x = f x.val
  resume_eq : ∀ x, resume x (f (next x.val)) = f x.val
  measure : α → ℕ
  decreases : ∀ x, test x = true → measure (next x) < measure x

namespace Recursion

variable {α : Type*} {β : α → Type*} {f : (x : α) → β x}
  [UniqueEncoding Tree α] [instβ : ∀ x, UniqueEncoding Tree (β x)] (r : Recursion f)

/-- One program serves every runtime index, including dependent recursive return values. -/
abbrev Return := (x : {x // r.test x = true}) × β (r.next x.val)

private inductive Path (r : Recursion f) : α → α → List α → Prop where
  | nil (x) : Path r x x []
  | cons {x y stack} : Path r x y stack → r.test y = true →
      Path r x (r.next y) (y :: stack)

private def pending (br : Bounds r.Return) (x : α) : ℕ :=
  if h : r.test x = true then br.time ⟨⟨x, h⟩, f (r.next x)⟩ + 8 else 0

omit [∀ x, UniqueEncoding Tree (β x)] in
private theorem path_bounds {b : Bounds α} {br : Bounds r.Return}
    (ht : ∀ x, r.test x = true → b.time (r.next x) + r.pending br x ≤ b.time x)
    (hs : ∀ x, r.test x = true → b.peak (r.next x) + ⌜x⌝ₜ.size + 1 ≤ b.peak x)
    {x y stack} (h : Path r x y stack) :
    b.time y + (stack.map (r.pending br)).sum ≤ b.time x ∧
      b.peak y + ⌜stack⌝ₜ.size ≤ b.peak x + 1 := by
  induction h with
  | nil => simp
  | @cons y stack h hy ih =>
    have := ht y hy
    have := hs y hy
    simp only [List.map_cons, List.sum_cons, encode_list_cons, size_encode_prod]
    constructor <;> omega

/-- The three reserved registers hold the argument, saved callers, and test/result respectively. -/
def code (test next finish resume : Value → Code Value) (v : Value) : Code Value :=
  ⟨fun n =>
    let check := callInto (test (.var n)) (n + 3) (n + 2)
    let advance := callInto (next (.var n)) (n + 3) n
    let base := callInto (finish (.var n)) (n + 3) (n + 2)
    let join := callInto (resume (.var n)) (n + 3) (n + 2)
    (.var (n + 2), max ((test (.var n)).build (n + 3)).2.1
      (max ((next (.var n)).build (n + 3)).2.1
        (max ((finish (.var n)).build (n + 3)).2.1 ((resume (.var n)).build (n + 3)).2.1)),
      [.assign n v.expression, .assign (n + 1) .nil, check,
       .while (.var (n + 2))
         (.seq (.assign (n + 1) (.pair (.var n) (.var (n + 1)))) (.seq advance check)),
       base,
       .while (.var (n + 1))
         (.seq (.assign n (.pair (.left (.var (n + 1))) (.var (n + 2))))
           (.seq join (.assign (n + 1) (.right (.var (n + 1))))))])⟩

/-- Certify the stack implementation using source recursion equations and local resource credit.
Saved arguments are charged to the peak allowance; time pays for each actual callback separately. -/
theorem implements {pc ps pd pr : Value → Code Value}
    {bc bs : Bounds α} {bd : Bounds {x // r.test x = false}} {br : Bounds r.Return}
    (hc : Implements pc r.test bc) (hs : Implements ps r.next bs)
    (hd : Implements pd (fun x => ⌜r.finish x⌝ₜ) bd)
    (hr : Implements pr (fun x : r.Return => ⌜r.resume x.1 x.2⌝ₜ) br)
    (b : Bounds α) (hsize : ∀ x, ⌜x⌝ₜ.size ≤ b.peak x)
    (hcheck : ∀ x, bc.peak x ≤ b.peak x)
    (hstop : ∀ x (h : r.test x = false),
      bd.time ⟨x, h⟩ + 2 ≤ b.time x ∧ bd.peak ⟨x, h⟩ ≤ b.peak x)
    (hstep : ∀ x (h : r.test x = true),
      bs.peak x ≤ b.peak x ∧ br.peak ⟨⟨x, h⟩, f (r.next x)⟩ ≤ b.peak x ∧
      b.peak (r.next x) + ⌜x⌝ₜ.size + 1 ≤ b.peak x ∧
      bs.time x + bc.time (r.next x) + br.time ⟨⟨x, h⟩, f (r.next x)⟩ + 16 +
        b.time (r.next x) ≤ b.time x) :
    Implements (code pc ps pd pr) (fun x => ⌜f x⌝ₜ)
      ⟨fun x => bc.time x + 3 * b.time x + 10, fun x => b.peak x + 1⟩ := by
  have output (x : α) : ⌜f x⌝ₜ.size ≤ b.peak x := by
    induction h : b.peak x using Nat.strong_induction_on generalizing x with
    | h k ih =>
      cases ht : r.test x with
      | false =>
        have := hd.size_le ⟨x, ht⟩
        simpa only [Tree.encode_self, r.finish_eq, h] using
          this.trans (max_le (hsize x) (hstop x ht).2)
      | true =>
        have next := ih (b.peak (r.next x)) (by have := (hstep x ht).2.2.1; omega)
          (r.next x) rfl
        have := hr.size_le ⟨⟨x, ht⟩, f (r.next x)⟩
        simp only [Tree.encode_self, r.resume_eq, Sigma.encode_mk, size_encode_prod,
          UniqueEncoding.encode_subtype] at this
        have := (hstep x ht).2.1
        have := (hstep x ht).2.2.1
        omega
  have path {x y stack} (hp : Path r x y stack) :=
    r.path_bounds (br := br)
      (fun a ha => by simp only [pending, ha, ↓reduceDIte]; have := (hstep a ha).2.2.2; omega)
      (fun a ha => (hstep a ha).2.2.1) hp
  constructor
  · intro v n hv
    have := (hc.1 (.var n) (n + 3) (by change n + 1 ≤ n + 3; omega)).1
    dsimp only [code, Value.expression, Expr.bound]
    constructor <;> omega
  · intro v n s x hv hx
    let J (t : ℕ → Tree) (k : ℕ) := ∃ y stack,
      Path r x y stack ∧ t n = ⌜y⌝ₜ ∧ t (n + 1) = ⌜stack⌝ₜ ∧
      t (n + 2) = ⌜r.test y⌝ₜ ∧ k = b.time y ∧ ∀ j < n, t j = s j
    let K (t : ℕ → Tree) (k : ℕ) := ∃ y stack,
      Path r x y stack ∧ t (n + 1) = ⌜stack⌝ₜ ∧ t (n + 2) = ⌜f y⌝ₜ ∧
      k = (stack.map (r.pending br)).sum + 2 ∧ ∀ j < n, t j = s j
    have check (t : ℕ → Tree) (y : α) (stack : List α) (hp : Path r x y stack)
        (hy : t n = ⌜y⌝ₜ) :=
      callInto_bounded hc (.var n) (n + 3) (n + 2) t y (space := b.peak x + 1)
        (by change n + 1 ≤ n + 3; omega) hy le_rfl
        ((hcheck y).trans (by have := (path hp).2; omega))
        ((hsize y).trans (by have := (path hp).2; omega))
    have descend (t : ℕ → Tree) (k : ℕ) (hj : J t k) :
        (Cmd.while (.var (n + 2))
          (.seq (.assign (n + 1) (.pair (.var n) (.var (n + 1))))
            (.seq (callInto (ps (.var n)) (n + 3) n)
              (callInto (pc (.var n)) (n + 3) (n + 2))))).Bounded t k (b.peak x + 1)
          (fun u => (∃ k, J u k) ∧ (u (n + 2)).root = false) := by
      apply Cmd.Bounded.loop_budget (.var (n + 2)) J k hj
      · rintro u k ⟨y, stack, hp, hy, hstack, ht, _, _⟩
        have hb := (hc.size_le y).trans (max_le (hsize y) (hcheck y))
        have := (path hp).2
        simp only [Expr.maxSize, ht]
        omega
      · rintro u k ⟨y, stack, hp, hy, hstack, ht, rfl, _⟩ h
        have := (hstop y (by simpa [ht] using h)).1
        simpa only [Expr.steps] using (by omega : 2 ≤ b.time y)
      · rintro u k ⟨y, stack, hp, hy, hstack, ht, rfl, hf⟩ h
        have ht : r.test y = true := by simpa [ht] using h
        have hp' := Path.cons hp ht
        have hb := (path hp).2
        have hb' := (path hp').2
        simp only [encode_list_cons, size_encode_prod] at hb'
        have hy' := hsize y
        have hn := (hstep y ht).2.2.1
        refine ⟨1 + ((bs.time y + 2) + (bc.time (r.next y) + 2)), ?_⟩
        refine Cmd.Bounded.seq (Q := fun w =>
          w = Function.update u (n + 1) ⌜y :: stack⌝ₜ) ?_ ?_
        · simp only [Cmd.bounded_assign_iff, Expr.assignSteps, Expr.steps, Expr.maxSize,
            Expr.eval, hy, hstack, encode_list_cons, encode_prod, Tree.size_pair]
          refine ⟨by rfl, ?_, trivial⟩
          exact max_le (by omega) (max_le (by omega) (by omega))
        rintro w rfl
        apply Cmd.Bounded.seq (callInto_bounded hs (.var n) (n + 3) n _ y
          (by change n + 1 ≤ n + 3; omega) (by simp [hy]) le_rfl
          ((hstep y ht).1.trans (by omega)) (by omega))
        rintro w ⟨hw, hwf⟩
        apply (check w (r.next y) (y :: stack) hp' hw).mono le_rfl le_rfl
        rintro z ⟨hz, hzf⟩
        refine ⟨b.time (r.next y), ⟨r.next y, y :: stack, hp', ?_, ?_, hz, rfl, ?_⟩, ?_⟩
        · exact (hzf n (by omega) (by omega)).trans hw
        · simpa using (hzf (n + 1) (by omega) (by omega)).trans
            (hwf (n + 1) (by omega) (by omega))
        · intro j hj
          exact (hzf j (by omega) (by omega)).trans ((hwf j (by omega) (by omega)).trans
            (by simpa [show j ≠ n + 1 by omega] using hf j hj))
        · have := (hstep y ht).2.2.2
          simp only [Expr.steps]
          omega
    have ascend (t : ℕ → Tree) (k : ℕ) (hk : K t k) :
        (Cmd.while (.var (n + 1))
          (.seq (.assign n (.pair (.left (.var (n + 1))) (.var (n + 2))))
            (.seq (callInto (pr (.var n)) (n + 3) (n + 2))
              (.assign (n + 1) (.right (.var (n + 1))))))).Bounded t k (b.peak x + 1)
          (fun u => (∃ k, K u k) ∧ (u (n + 1)).root = false) := by
      apply Cmd.Bounded.loop_budget (.var (n + 1)) K k hk
      · rintro u k ⟨y, stack, hp, hstack, ht, _, _⟩
        have := (path hp).2
        simp only [Expr.maxSize, hstack]
        omega
      · rintro u k ⟨y, stack, hp, hstack, ht, rfl, _⟩ _
        simp only [Expr.steps]
        omega
      · rintro u k ⟨y, stack, hp, hstack, ht, rfl, hf⟩ h
        cases hp with
        | nil => simp [hstack] at h
        | @cons parent rest hp hz =>
          have hb := (path hp).2
          have hb' := (path (Path.cons hp hz)).2
          simp only [encode_list_cons, size_encode_prod] at hb'
          have ho := output (r.next parent)
          have hs := (hstep parent hz).2.2.1
          let arg : r.Return := ⟨⟨parent, hz⟩, f (r.next parent)⟩
          have ha : ⌜arg⌝ₜ.size ≤ b.peak x + 1 := by
            simp only [arg, Sigma.encode_mk, size_encode_prod, UniqueEncoding.encode_subtype]
            omega
          refine ⟨2 + ((br.time arg + 2) + 1), ?_⟩
          refine Cmd.Bounded.seq (Q := fun w => w = Function.update u n ⌜arg⌝ₜ) ?_ ?_
          · simp only [Cmd.bounded_assign_iff, Expr.assignSteps, Expr.steps, Expr.maxSize,
              Expr.eval, hstack, ht, encode_list_cons, encode_prod, Tree.left_pair,
              Tree.size_pair, arg, Sigma.encode_mk, UniqueEncoding.encode_subtype]
            refine ⟨by rfl, ?_, trivial⟩
            exact max_le (by omega) (max_le (by omega) (by omega))
          rintro w rfl
          apply Cmd.Bounded.seq (callInto_bounded hr (.var n) (n + 3) (n + 2) _ arg
            (by change n + 1 ≤ n + 3; omega) (by simp) le_rfl
            ((hstep parent hz).2.1.trans (by omega)) ha)
          rintro w ⟨hw, hwf⟩
          have hws : w (n + 1) = ⌜parent :: rest⌝ₜ := by
            simpa [hstack] using hwf (n + 1) (by omega) (by omega)
          simp only [Cmd.bounded_assign_iff, Expr.assignSteps, Expr.steps, Expr.maxSize,
            Expr.eval, hws, encode_list_cons, encode_prod, Tree.right_pair, Tree.size_pair]
          refine ⟨by rfl, by omega, (rest.map (r.pending br)).sum + 2,
            ⟨parent, rest, hp, by simp, ?_, rfl, ?_⟩, ?_⟩
          · simpa [arg, r.resume_eq] using hw
          · intro j hj
            simpa [show j ≠ n + 1 by omega, show j ≠ n by omega] using
              (hwf j (by omega) (by omega)).trans (by
                simpa [show j ≠ n by omega] using hf j hj)
          · simp only [List.map_cons, List.sum_cons, pending, hz, ↓reduceDIte, arg]
            omega
    change (Code.block _).Bounded _ _ _ _
    simp only [code, Code.block]
    apply Cmd.Bounded.mono
      (time := 2 + (1 + ((bc.time x + 2) + (b.time x + (b.time x + (b.time x + 2)))))) ?_
      (by omega) le_rfl (fun _ h => h)
    refine Cmd.Bounded.seq (Q := fun t => t = Function.update s n ⌜x⌝ₜ) ?_ ?_
    · simp only [Cmd.bounded_assign_iff, Value.maxSize_expression, Value.eval_expression, hx]
      exact ⟨v.assignSteps_le, (hsize x).trans (by omega), trivial⟩
    rintro t rfl
    apply Cmd.Bounded.seq (Q := fun t => t = Function.update (Function.update s n ⌜x⌝ₜ)
      (n + 1) ⌜([] : List α)⌝ₜ) (by simp [encode_unit])
    rintro t rfl
    apply Cmd.Bounded.seq (check _ x [] (.nil x) (by simp))
    rintro t ⟨ht, hf⟩
    have hj : J t (b.time x) := ⟨x, [], .nil x, by simpa using hf n (by omega) (by omega),
      by simpa using hf (n + 1) (by omega) (by omega), ht, rfl,
      fun j hj => by
        simpa [show j ≠ n by omega, show j ≠ n + 1 by omega] using
          hf j (by omega) (by omega)⟩
    apply Cmd.Bounded.seq (descend t _ hj)
    rintro u ⟨⟨_, y, stack, hp, hy, hstack, hflag, _, hf⟩, hfalse⟩
    have hyfalse : r.test y = false := by simpa [hflag] using hfalse
    have ht := (path hp).1
    have hb := (path hp).2
    apply Cmd.Bounded.seq ((callInto_bounded hd (.var n) (n + 3) (n + 2) u ⟨y, hyfalse⟩
      (by change n + 1 ≤ n + 3; omega) (by simpa using hy) le_rfl
      ((hstop y hyfalse).2.trans (by omega)) ((hsize y).trans (by omega))).mono
        (by have := (hstop y hyfalse).1; omega) le_rfl (fun _ h => h))
    rintro w ⟨hw, hwf⟩
    rw [Cmd.bounded_seq_skip_iff]
    have hk : K w ((stack.map (r.pending br)).sum + 2) := ⟨y, stack, hp,
      (hwf (n + 1) (by omega) (by omega)).trans hstack,
      by simpa [r.finish_eq] using hw, rfl,
      fun j hj => (hwf j (by omega) (by omega)).trans (hf j hj)⟩
    apply (ascend w _ hk).mono (by omega) le_rfl
    rintro z ⟨⟨_, y, stack, hp, hstack, hr, _, hf⟩, hfalse⟩
    cases hp with
    | nil => exact ⟨by simpa using hr, hf⟩
    | cons hp h => simp [hstack] at hfalse

/-- Sum the calls along the actual recursion, retaining space for all saved source arguments. -/
def cost (bc bs : Bounds α) (bd : Bounds {x // r.test x = false}) (br : Bounds r.Return)
    (x : α) : Cost :=
  if h : r.test x = true then
    let tail := cost bc bs bd br (r.next x)
    let arg : r.Return := ⟨⟨x, h⟩, f (r.next x)⟩
    ⟨bs.time x + bc.time (r.next x) + br.time arg + 16 + tail.time,
      max ⌜x⌝ₜ.size (max (bc.peak x) (max (bs.peak x)
        (max (br.peak arg) (tail.peak + ⌜x⌝ₜ.size + 1))))⟩
  else
    let arg : {x // r.test x = false} := ⟨x, by simpa using h⟩
    ⟨bd.time arg + 2, max ⌜x⌝ₜ.size (max (bc.peak x) (bd.peak arg))⟩
termination_by r.measure x
decreasing_by exact r.decreases x h

omit [∀ x, UniqueEncoding Tree (β x)] in
theorem cost_stop (bc bs : Bounds α) (bd : Bounds {x // r.test x = false})
    (br : Bounds r.Return) (x : α) (h : r.test x = false) :
    r.cost bc bs bd br x =
      ⟨bd.time ⟨x, h⟩ + 2, max ⌜x⌝ₜ.size (max (bc.peak x) (bd.peak ⟨x, h⟩))⟩ := by
  rw [cost]
  simp only [h, Bool.false_eq_true, ↓reduceDIte]

omit [∀ x, UniqueEncoding Tree (β x)] in
theorem cost_step (bc bs : Bounds α) (bd : Bounds {x // r.test x = false})
    (br : Bounds r.Return) (x : α) (h : r.test x = true) :
    r.cost bc bs bd br x =
      ⟨bs.time x + bc.time (r.next x) + br.time ⟨⟨x, h⟩, f (r.next x)⟩ + 16 +
          (r.cost bc bs bd br (r.next x)).time,
        max ⌜x⌝ₜ.size (max (bc.peak x) (max (bs.peak x)
          (max (br.peak ⟨⟨x, h⟩, f (r.next x)⟩)
            ((r.cost bc bs bd br (r.next x)).peak + ⌜x⌝ₜ.size + 1))))⟩ := by
  rw [cost]
  simp only [h, ↓reduceDIte]

omit [∀ x, UniqueEncoding Tree (β x)] in
/-- One coefficient covers every callback and is fixed before induction on the recursion. -/
theorem cost_le_mul
    {bc bs bc' bs' : Bounds α} {bd bd' : Bounds {x // r.test x = false}}
    {br br' : Bounds r.Return} (C : ℕ) (hC : 1 ≤ C)
    (hc : ∀ x, bc.time x ≤ C * bc'.time x ∧ bc.peak x ≤ C * bc'.peak x)
    (hs : ∀ x, bs.time x ≤ C * bs'.time x ∧ bs.peak x ≤ C * bs'.peak x)
    (hd : ∀ x, bd.time x ≤ C * bd'.time x ∧ bd.peak x ≤ C * bd'.peak x)
    (hr : ∀ x, br.time x ≤ C * br'.time x ∧ br.peak x ≤ C * br'.peak x)
    (x : α) :
    (r.cost bc bs bd br x).time ≤ C * (r.cost bc' bs' bd' br' x).time ∧
    (r.cost bc bs bd br x).peak ≤ C * (r.cost bc' bs' bd' br' x).peak := by
  have scale (n : ℕ) : n ≤ C * n := by simpa using Nat.mul_le_mul_right n hC
  induction hm : r.measure x using Nat.strong_induction_on generalizing x with
  | h n ih =>
    cases ht : r.test x with
    | false =>
      rw [r.cost_stop _ _ _ _ x ht, r.cost_stop _ _ _ _ x ht]
      dsimp only
      rw [Nat.mul_add, mul_max, mul_max]
      exact ⟨Nat.add_le_add (hd ⟨x, ht⟩).1 (scale 2),
        max_le_max (scale _) (max_le_max (hc x).2 (hd ⟨x, ht⟩).2)⟩
    | true =>
      have hi := ih (r.measure (r.next x)) (by have := r.decreases x ht; omega)
        (r.next x) rfl
      rw [r.cost_step _ _ _ _ x ht, r.cost_step _ _ _ _ x ht]
      dsimp only
      simp only [Nat.mul_add, mul_max]
      exact ⟨Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
        (Nat.add_le_add (hs x).1 (hc (r.next x)).1) (hr ⟨⟨x, ht⟩, f (r.next x)⟩).1)
        (scale 16)) hi.1,
        max_le_max (scale _) (max_le_max (hc x).2 (max_le_max (hs x).2
          (max_le_max (hr ⟨⟨x, ht⟩, f (r.next x)⟩).2
            (Nat.add_le_add (Nat.add_le_add hi.2 (scale _)) (scale 1)))))⟩

omit [∀ x, UniqueEncoding Tree (β x)] in
/-- Replace callback allowances in the existing cost expression, without changing its
additions, controller costs, unique terminal call, or accumulated stack space. -/
theorem dominated_cost_congr
    {bc bs bc' bs' : Bounds α} {bd bd' : Bounds {x // r.test x = false}}
    {br br' : Bounds r.Return}
    (hc : Dominated bc.time bc'.time ∧ Dominated bc.peak bc'.peak)
    (hs : Dominated bs.time bs'.time ∧ Dominated bs.peak bs'.peak)
    (hd : Dominated bd.time bd'.time ∧ Dominated bd.peak bd'.peak)
    (hr : Dominated br.time br'.time ∧ Dominated br.peak br'.peak) :
    Dominated (fun x => (r.cost bc bs bd br x).time)
      (fun x => (r.cost bc' bs' bd' br' x).time) ∧
    Dominated (fun x => (r.cost bc bs bd br x).peak)
      (fun x => (r.cost bc' bs' bd' br' x).peak) := by
  obtain ⟨C₁, h₁⟩ := dominated_iff.mp hc.1
  obtain ⟨C₂, h₂⟩ := dominated_iff.mp hc.2
  obtain ⟨C₃, h₃⟩ := dominated_iff.mp hs.1
  obtain ⟨C₄, h₄⟩ := dominated_iff.mp hs.2
  obtain ⟨C₅, h₅⟩ := dominated_iff.mp hd.1
  obtain ⟨C₆, h₆⟩ := dominated_iff.mp hd.2
  obtain ⟨C₇, h₇⟩ := dominated_iff.mp hr.1
  obtain ⟨C₈, h₈⟩ := dominated_iff.mp hr.2
  simp only [Nat.nsmul_eq_mul] at h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈
  let C := C₁ + C₂ + C₃ + C₄ + C₅ + C₆ + C₇ + C₈ + 1
  have lift {a b c : ℕ} (hc : c ≤ C) (h : a ≤ c * b) : a ≤ C * b :=
    h.trans (Nat.mul_le_mul_right b hc)
  have h := r.cost_le_mul C (by dsimp [C]; omega)
    (fun x => ⟨lift (by dsimp [C]; omega) (h₁ x), lift (by dsimp [C]; omega) (h₂ x)⟩)
    (fun x => ⟨lift (by dsimp [C]; omega) (h₃ x), lift (by dsimp [C]; omega) (h₄ x)⟩)
    (fun x => ⟨lift (by dsimp [C]; omega) (h₅ x), lift (by dsimp [C]; omega) (h₆ x)⟩)
    (fun x => ⟨lift (by dsimp [C]; omega) (h₇ x), lift (by dsimp [C]; omega) (h₈ x)⟩)
  exact ⟨Dominated.of_le_mul C (fun x => (h x).1),
    Dominated.of_le_mul C (fun x => (h x).2)⟩

omit [∀ x, UniqueEncoding Tree (β x)] in
/-- Bound a recursive evaluation with separate terminal and per-round allowances.
The final term explicitly pays for every saved caller in the stack. -/
theorem cost_le_of_steps
    (bc bs : Bounds α) (bd : Bounds {x // r.test x = false}) (br : Bounds r.Return)
    (I : α → Prop) (size stop step peak : ℕ)
    (hsize : ∀ x, I x → ⌜x⌝ₜ.size ≤ size)
    (hcheck : ∀ x, I x → bc.peak x ≤ peak)
    (hstop : ∀ x (h : r.test x = false), I x →
      bd.time ⟨x, h⟩ + 2 ≤ stop ∧ bd.peak ⟨x, h⟩ ≤ peak)
    (hstep : ∀ x (h : r.test x = true), I x →
      I (r.next x) ∧ bs.peak x ≤ peak ∧
      br.peak ⟨⟨x, h⟩, f (r.next x)⟩ ≤ peak ∧
      bs.time x + bc.time (r.next x) + br.time ⟨⟨x, h⟩, f (r.next x)⟩ + 16 ≤ step)
    (x : α) (hx : I x) :
    (r.cost bc bs bd br x).time ≤ r.measure x * step + stop ∧
      (r.cost bc bs bd br x).peak ≤ peak + (r.measure x + 1) * (size + 1) := by
  induction hm : r.measure x using Nat.strong_induction_on generalizing x with
  | h n ih =>
    cases ht : r.test x with
    | false =>
      have := hstop x ht hx
      have := hcheck x hx
      have := hsize x hx
      rw [r.cost_stop _ _ _ _ x ht]
      dsimp only
      constructor
      · nlinarith
      · simp only [max_le_iff]
        (repeat' apply And.intro) <;> nlinarith
    | true =>
      obtain ⟨hi, hs, hr, htime⟩ := hstep x ht hx
      have hm' := r.decreases x ht
      have hc := ih (r.measure (r.next x)) (by omega) (r.next x) hi rfl
      have := hcheck x hx
      have := hsize x hx
      rw [r.cost_step _ _ _ _ x ht]
      dsimp only
      constructor
      · nlinarith [hc.1]
      · simp only [max_le_iff]
        (repeat' apply And.intro) <;> nlinarith [hc.2]


variable {tc pc ts ps : α → ℕ} {td pd : {x // r.test x = false} → ℕ} {tr pr : r.Return → ℕ}

/-- Callback programs and the source recursion equation determine one program.
Its growth is the structural recursion cost of the callback growths; controller constants
and the factor for the descending and ascending passes are hidden. -/
theorem hasProgram
    {instD : ∀ x : {x // r.test x = false}, UniqueEncoding Tree (β x.1)}
    {instR : ∀ x : r.Return, UniqueEncoding Tree (β x.1.1)} {qc qs qd qr : Value → Code Value}
    (hc : HasProgram r.test qc tc pc) (hs : HasProgram r.next qs ts ps)
    (hd : HasProgram r.finish qd td pd)
    (hr : HasProgram (fun x : r.Return => r.resume x.1 x.2) qr tr pr)
    -- The callbacks' encodings, elaborated with their own types, are those of `f`.
    (hD : ∀ x, instD x = instβ x.1 := by intros; rfl)
    (hR : ∀ x, instR x = instβ x.1.1 := by intros; rfl) :
    HasProgram f (code qc qs qd qr)
      (fun x => tc x + (r.cost ⟨tc, pc⟩ ⟨ts, ps⟩ ⟨td, pd⟩ ⟨tr, pr⟩ x).time + 1)
      (fun x => (r.cost ⟨tc, pc⟩ ⟨ts, ps⟩ ⟨td, pd⟩ ⟨tr, pr⟩ x).peak + 1) := by
  obtain rfl : instD = _ := funext hD
  obtain rfl : instR = _ := funext hR
  obtain ⟨bc, hbc, hct, hcp⟩ := hc.sound
  obtain ⟨bs, hbs, hst, hsp⟩ := hs.sound
  obtain ⟨bd, hbd, hdt, hdp⟩ := hd.sound
  obtain ⟨br, hbr, hrt, hrp⟩ := hr.sound
  have hcost := r.dominated_cost_congr (bc' := ⟨tc, pc⟩) (bs' := ⟨ts, ps⟩)
    (bd' := ⟨td, pd⟩) (br' := ⟨tr, pr⟩) ⟨hct, hcp⟩ ⟨hst, hsp⟩ ⟨hdt, hdp⟩ ⟨hrt, hrp⟩
  -- The program reads the callbacks' results as trees.
  refine ⟨_, (r.implements hbc hbs (hbd.of_encode fun _ => Tree.encode_self _)
    (hbr.of_encode fun _ => Tree.encode_self _)
    ⟨fun x => (r.cost bc bs bd br x).time, fun x => (r.cost bc bs bd br x).peak⟩
    ?_ ?_ ?_ ?_).of_encode fun _ => (Tree.encode_self _).symm,
    (hct.add (hcost.1.const_mul_left 3)).add (Dominated.const 10),
    hcost.2.add (Dominated.refl _)⟩
  · intro x
    cases h : r.test x <;>
      simp only [cost_stop, cost_step, h, le_sup_left]
  · intro x
    cases h : r.test x <;>
      simp only [cost_stop, cost_step, h] <;> omega
  · intro x h
    simp only [cost_stop, h]
    exact ⟨le_rfl, (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)⟩
  · intro x h
    simp only [cost_step, h]
    exact ⟨(Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _)),
      (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans
        ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))),
      (Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans
        ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))), le_rfl⟩

end Recursion
end Complexity.TreeProgram.Source

namespace Complexity.TreeProgram.Source.Recursion

open Internal (HasProgram)

variable {α ρ : Type*} {β : α → Type*} [UniqueEncoding Tree α]
  {f : (x : α) → β x} (r : Recursion f)

/-- A round excludes the recursive tail and the unique terminal computation. -/
def roundTime (bc bs : Bounds α) (br : Bounds r.Return) (x : α) : ℕ :=
  if h : r.test x = true then
    bs.time x + bc.time (r.next x) + br.time ⟨⟨x, h⟩, f (r.next x)⟩ + 16
  else 0

def stopTime (bd : Bounds {x // r.test x = false}) (x : α) : ℕ :=
  if h : r.test x = false then bd.time ⟨x, h⟩ + 2 else 0

def localPeak (bc bs : Bounds α) (bd : Bounds {x // r.test x = false})
    (br : Bounds r.Return) (x : α) : ℕ :=
  if h : r.test x = true then
    max (bc.peak x) (max (bs.peak x) (br.peak ⟨⟨x, h⟩, f (r.next x)⟩))
  else max (bc.peak x) (bd.peak ⟨x, by simpa using h⟩)

/-- Every reachable state of every outer input belongs to one family. The witnesses in the
four estimates are uniform across that entire family, not chosen inside the recursion. -/
theorem dominated_cost (bc bs : Bounds α) (bd : Bounds {x // r.test x = false})
    (br : Bounds r.Return) (I : ρ → α → Prop) (start : ρ → α)
    (size stop step peak : ρ → ℕ)
    (initial : ∀ a, I a (start a))
    (next : ∀ a x, I a x → r.test x = true → I a (r.next x))
    (hsize : Dominated (fun z : {p : ρ × α // I p.1 p.2} => ⌜z.1.2⌝ₜ.size)
      (fun z => size z.1.1))
    (hpeak : Dominated (fun z : {p : ρ × α // I p.1 p.2} =>
      r.localPeak bc bs bd br z.1.2) (fun z => peak z.1.1))
    (hstop : Dominated (fun z : {p : ρ × α // I p.1 p.2} => r.stopTime bd z.1.2)
      (fun z => stop z.1.1))
    (hstep : Dominated (fun z : {p : ρ × α // I p.1 p.2} => r.roundTime bc bs br z.1.2)
      (fun z => step z.1.1)) :
    Dominated (fun a => (r.cost bc bs bd br (start a)).time)
      (fun a => r.measure (start a) * step a + stop a) ∧
    Dominated (fun a => (r.cost bc bs bd br (start a)).peak)
      (fun a => peak a + (r.measure (start a) + 1) * (size a + 1)) := by
  obtain ⟨Cs, hs⟩ := dominated_iff.mp hsize
  obtain ⟨Cp, hp⟩ := dominated_iff.mp hpeak
  obtain ⟨Ct, ht⟩ := dominated_iff.mp hstop
  obtain ⟨Cr, hr⟩ := dominated_iff.mp hstep
  simp only [Nat.nsmul_eq_mul] at hs hp ht hr
  have bound (a : ρ) := r.cost_le_of_steps bc bs bd br (I a)
    (Cs * size a) (Ct * stop a) (Cr * step a) (Cp * peak a)
    (fun x hx => hs ⟨(a, x), hx⟩)
    (by
      intro x hx
      have h := hp ⟨(a, x), hx⟩
      unfold localPeak at h
      split at h <;> exact (Nat.le_max_left _ _).trans h)
    (by
      intro x hx hi
      have ht' := ht ⟨(a, x), hi⟩
      have hp' := hp ⟨(a, x), hi⟩
      simp only [stopTime, localPeak, hx, Bool.false_eq_true, ↓reduceDIte,
        Nat.max_le] at ht' hp'
      exact ⟨ht', hp'.2⟩)
    (by
      intro x hx hi
      have hp' := hp ⟨(a, x), hi⟩
      have hr' := hr ⟨(a, x), hi⟩
      simp only [localPeak, roundTime, hx, ↓reduceDIte, Nat.max_le] at hp' hr'
      exact ⟨next a x hi hx, hp'.2.1, hp'.2.2, hr'⟩)
    (start a) (initial a)
  constructor
  · refine dominated_iff.mpr ⟨Cr + Ct, fun a => ?_⟩
    have h := (bound a).1
    simp only [Nat.nsmul_eq_mul]
    apply h.trans
    calc
      _ = Cr * (r.measure (start a) * step a) + Ct * stop a := by ring
      _ ≤ (Cr + Ct) * (r.measure (start a) * step a) + (Cr + Ct) * stop a :=
        Nat.add_le_add (Nat.mul_le_mul_right _ (by omega))
          (Nat.mul_le_mul_right _ (by omega))
      _ = _ := by ring
  · refine dominated_iff.mpr ⟨Cp + Cs + 1, fun a => ?_⟩
    have h := (bound a).2
    simp only [Nat.nsmul_eq_mul]
    apply h.trans
    have hs' : Cs * size a + 1 ≤ (Cp + Cs + 1) * (size a + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      exact Nat.add_le_add (Nat.mul_le_mul_right _ (by omega)) (by omega)
    calc
      _ ≤ (Cp + Cs + 1) * peak a +
          (r.measure (start a) + 1) * ((Cp + Cs + 1) * (size a + 1)) :=
        Nat.add_le_add (Nat.mul_le_mul_right _ (by omega)) (Nat.mul_le_mul_left _ hs')
      _ = _ := by ring

/-- Separate callback estimates are combined by the original recursion cost theorem.
Branch restrictions and controller constants are discharged here, with one coefficient
for the entire invariant family. The terminal allowance is paid once. -/
theorem dominated_cost_of_bounds
    (bc bs : Bounds α) (bd : Bounds {x // r.test x = false}) (br : Bounds r.Return)
    (I : ρ → α → Prop) (start : ρ → α) (size stop step peak : ρ → ℕ)
    (initial : ∀ a, I a (start a))
    (next : ∀ a x, I a x → r.test x = true → I a (r.next x))
    (hsize : Dominated (fun z : {p : ρ × α // I p.1 p.2} => ⌜z.1.2⌝ₜ.size)
      (fun z => size z.1.1))
    (hcpeak : Dominated (fun z : {p : ρ × α // I p.1 p.2} => bc.peak z.1.2)
      (fun z => peak z.1.1))
    (hspeak : Dominated (fun z : {p : ρ × α // I p.1 p.2} => bs.peak z.1.2)
      (fun z => peak z.1.1))
    (hdpeak : Dominated (fun z : {p : {p : ρ × α // I p.1 p.2} //
        r.test p.1.2 = false} => bd.peak ⟨z.1.1.2, z.2⟩) (fun z => peak z.1.1.1))
    (hrpeak : Dominated (fun z : {p : {p : ρ × α // I p.1 p.2} //
        r.test p.1.2 = true} => br.peak ⟨⟨z.1.1.2, z.2⟩, f (r.next z.1.1.2)⟩)
      (fun z => peak z.1.1.1))
    (hdtime : Dominated (fun z : {p : {p : ρ × α // I p.1 p.2} //
        r.test p.1.2 = false} => bd.time ⟨z.1.1.2, z.2⟩) (fun z => stop z.1.1.1))
    (hstime : Dominated (fun z : {p : ρ × α // I p.1 p.2} => bs.time z.1.2)
      (fun z => step z.1.1))
    (hctime : Dominated (fun z : {p : {p : ρ × α // I p.1 p.2} //
        r.test p.1.2 = true} => bc.time (r.next z.1.1.2)) (fun z => step z.1.1.1))
    (hrtime : Dominated (fun z : {p : {p : ρ × α // I p.1 p.2} //
        r.test p.1.2 = true} => br.time ⟨⟨z.1.1.2, z.2⟩, f (r.next z.1.1.2)⟩)
      (fun z => step z.1.1.1))
    (stop_pos : ∀ a, 0 < stop a) (step_pos : ∀ a, 0 < step a) :
    Dominated (fun a => (r.cost bc bs bd br (start a)).time)
      (fun a => r.measure (start a) * step a + stop a) ∧
    Dominated (fun a => (r.cost bc bs bd br (start a)).peak)
      (fun a => peak a + (r.measure (start a) + 1) * (size a + 1)) := by
  let Z := {p : ρ × α // I p.1 p.2}
  apply r.dominated_cost bc bs bd br I start size stop step peak initial next hsize
  · apply Dominated.of_cases (fun z : Z => r.test z.1.2 = true)
    · apply ((hcpeak.comp Subtype.val).max_same
        ((hspeak.comp Subtype.val).max_same hrpeak)).mono_left
      intro z
      simp only [localPeak, z.2, ↓reduceDIte, Function.comp_apply, le_refl]
    · let u (z : {z : Z // ¬r.test z.1.2 = true}) : {z : Z // r.test z.1.2 = false} :=
        ⟨z.1, by simpa using z.2⟩
      apply ((hcpeak.comp Subtype.val).max_same (hdpeak.comp u)).mono_left
      intro z
      simp only [localPeak, z.2, Function.comp_apply]
      exact le_rfl
  · apply Dominated.of_cases (fun z : Z => r.test z.1.2 = false)
    · apply (hdtime.add_same (Dominated.const_of_pos 2 fun z => stop_pos z.1.1.1)).mono_left
      intro z
      simp only [stopTime, z.2, ↓reduceDIte, Function.comp_apply, le_refl]
    · apply Dominated.of_le
      intro z
      simp only [stopTime, z.2, ↓reduceDIte, Function.comp_apply, Bool.true_eq_false, Nat.zero_le]
  · apply Dominated.of_cases (fun z : Z => r.test z.1.2 = true)
    · apply ((((hstime.comp Subtype.val).add_same hctime).add_same
        hrtime).add_same (Dominated.const_of_pos 16 fun z => step_pos z.1.1.1)).mono_left
      intro z
      simp only [roundTime, z.2, ↓reduceDIte, Function.comp_apply, le_refl]
    · apply Dominated.of_le
      intro z
      simp only [roundTime, z.2, ↓reduceDIte, Function.comp_apply, Bool.false_eq_true, Nat.zero_le]


omit [UniqueEncoding Tree α] in
private theorem dominated_pow_comp {γ δ : Type*} {g S : γ → ℕ} {T : δ → ℕ} (u : δ → γ) {d : ℕ}
    (h : Dominated g (fun y => S y ^ d)) (hu : ∀ z, S (u z) ≤ T z) :
    Dominated (fun z => g (u z)) (fun z => T z ^ d) :=
  (h.comp u).trans (Dominated.of_le fun z => Nat.pow_le_pow_left (hu z) d)

/-- A scale that does not grow along the recursion bounds every reachable state by the outer
input. Each callback is bounded by a power of the scale of its source state: a round costs
`S ^ a`, the terminal call `S ^ c`, every callback space `S ^ b`, and a saved input `S ^ e`. -/
theorem dominated_cost_of_scale (bc bs : Bounds α) (bd : Bounds {x // r.test x = false})
    (br : Bounds r.Return) (S : α → ℕ) (hS : ∀ x, 0 < S x)
    (hnext : ∀ x, r.test x = true → S (r.next x) ≤ S x) {e a b c : ℕ}
    (hsize : Dominated (fun x => ⌜x⌝ₜ.size) (fun x => S x ^ e))
    (hc : Dominated bc.time (fun x => S x ^ a) ∧ Dominated bc.peak (fun x => S x ^ b))
    (hs : Dominated bs.time (fun x => S x ^ a) ∧ Dominated bs.peak (fun x => S x ^ b))
    (hd : Dominated bd.time (fun x => S x.1 ^ c) ∧ Dominated bd.peak (fun x => S x.1 ^ b))
    (hr : Dominated (fun x : {x // r.test x = true} => br.time ⟨x, f (r.next x.1)⟩)
        (fun x => S x.1 ^ a) ∧
      Dominated (fun x : {x // r.test x = true} => br.peak ⟨x, f (r.next x.1)⟩)
        (fun x => S x.1 ^ b)) :
    Dominated (fun x => (r.cost bc bs bd br x).time)
      (fun x => r.measure x * S x ^ a + S x ^ c) ∧
    Dominated (fun x => (r.cost bc bs bd br x).peak)
      (fun x => S x ^ b + (r.measure x + 1) * (S x ^ e + 1)) := by
  let Z := {p : α × α // S p.2 ≤ S p.1}
  let Stop := {z : Z // r.test z.1.2 = false}
  let Step := {z : Z // r.test z.1.2 = true}
  let S₀ (x : {x // r.test x = false}) := S x.1
  let S₁ (x : {x // r.test x = true}) := S x.1
  exact r.dominated_cost_of_bounds _ _ _ _ (fun a x => S x ≤ S a) (fun x => x)
    (fun x => S x ^ e) (fun x => S x ^ c) (fun x => S x ^ a) (fun x => S x ^ b) (fun _ => le_rfl)
    (fun _ x hx h => (hnext x h).trans hx)
    (dominated_pow_comp (fun z : Z => z.1.2) hsize fun z => z.2 :)
    (dominated_pow_comp (fun z : Z => z.1.2) hc.2 fun z => z.2 :)
    (dominated_pow_comp (fun z : Z => z.1.2) hs.2 fun z => z.2 :)
    (dominated_pow_comp (fun z : Stop => ⟨z.1.1.2, z.2⟩) hd.2 fun z => z.1.2 :)
    (dominated_pow_comp (fun z : Step => ⟨z.1.1.2, z.2⟩) hr.2 fun z => z.1.2 :)
    (dominated_pow_comp (fun z : Stop => ⟨z.1.1.2, z.2⟩) hd.1 fun z => z.1.2 :)
    (dominated_pow_comp (fun z : Z => z.1.2) hs.1 fun z => z.2 :)
    (dominated_pow_comp (fun z : Step => r.next z.1.1.2) hc.1
      fun z => (hnext _ z.2).trans z.1.2 :)
    (dominated_pow_comp (fun z : Step => ⟨z.1.1.2, z.2⟩) hr.1 fun z => z.1.2 :)
    (fun x => Nat.pow_pos (hS x)) (fun x => Nat.pow_pos (hS x))

variable [instβ : ∀ x, UniqueEncoding Tree (β x)]
  {tc pc ts ps : α → ℕ} {td pd : {x // r.test x = false} → ℕ} {tr pr : r.Return → ℕ}

/-- The recursive program, with the growth of `dominated_cost_of_scale`. -/
theorem hasProgram_of_scale
    {instD : ∀ x : {x // r.test x = false}, UniqueEncoding Tree (β x.1)}
    {instR : ∀ x : r.Return, UniqueEncoding Tree (β x.1.1)} {qc qs qd qr : Value → Code Value}
    (hc : HasProgram r.test qc tc pc) (hs : HasProgram r.next qs ts ps)
    (hd : HasProgram r.finish qd td pd)
    (hr : HasProgram (fun x : r.Return => r.resume x.1 x.2) qr tr pr)
    (S : α → ℕ) (hS : ∀ x, 0 < S x)
    (hnext : ∀ x, r.test x = true → S (r.next x) ≤ S x) {e a b c : ℕ}
    (hsize : Dominated (fun x => ⌜x⌝ₜ.size) (fun x => S x ^ e))
    (htc : Dominated tc (fun x => S x ^ a)) (hpc : Dominated pc (fun x => S x ^ b))
    (hts : Dominated ts (fun x => S x ^ a)) (hps : Dominated ps (fun x => S x ^ b))
    (htd : Dominated td (fun x => S x.1 ^ c)) (hpd : Dominated pd (fun x => S x.1 ^ b))
    (htr : Dominated (fun x : {x // r.test x = true} => tr ⟨x, f (r.next x.1)⟩)
      (fun x => S x.1 ^ a))
    (hpr : Dominated (fun x : {x // r.test x = true} => pr ⟨x, f (r.next x.1)⟩)
      (fun x => S x.1 ^ b))
    (hD : ∀ x, instD x = instβ x.1 := by intros; rfl)
    (hR : ∀ x, instR x = instβ x.1.1 := by intros; rfl) :
    HasProgram f (code qc qs qd qr) (fun x => (r.measure x + 1) * S x ^ a + S x ^ c)
      (fun x => S x ^ b + (r.measure x + 1) * (S x ^ e + 1)) :=
  have h := r.dominated_cost_of_scale ⟨tc, pc⟩ ⟨ts, ps⟩ ⟨td, pd⟩ ⟨tr, pr⟩ S hS hnext hsize
    ⟨htc, hpc⟩ ⟨hts, hps⟩ ⟨htd, hpd⟩ ⟨htr, hpr⟩
  have hpos x : 0 < (r.measure x + 1) * S x ^ a + S x ^ c :=
    Nat.add_pos_right _ (Nat.pow_pos (hS x))
  (r.hasProgram hc hs hd hr hD hR).mono
    (((htc.trans (Dominated.of_le fun _ => (Nat.le_mul_of_pos_left _ (Nat.succ_pos _)).trans
        (Nat.le_add_right _ _))).add_same (h.1.trans (Dominated.of_le fun _ =>
          Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.le_succ _)) _))).add_same
      (Dominated.one hpos))
    (h.2.add_same (Dominated.one fun x => Nat.add_pos_left (Nat.pow_pos (hS x)) _))

/-- Bounds of a recursive result by the scale of its source state, for callbacks whose
allowances are powers of their input sizes. -/
theorem dominated_size_return (S : α → ℕ) (hS : ∀ x, 0 < S x)
    (hnext : ∀ x, r.test x = true → S (r.next x) ≤ S x) {e : ℕ}
    (hsize : Dominated (fun x => ⌜x⌝ₜ.size) (fun x => S x ^ e))
    (hout : Dominated (fun x => ⌜f x⌝ₜ.size) (fun x => S x ^ e)) (d : ℕ) :
    Dominated (fun x : {x // r.test x = true} => ⌜(⟨x, f (r.next x.1)⟩ : r.Return)⌝ₜ.size ^ d)
      (fun x => S x.1 ^ (e * d)) := by
  have h : Dominated (fun x : {x // r.test x = true} =>
      1 + ⌜x.1⌝ₜ.size + ⌜f (r.next x.1)⌝ₜ.size) (fun x => S x.1 ^ e) :=
    ((Dominated.one fun x => Nat.pow_pos (hS x.1)).add_same (hsize.comp Subtype.val)).add_same
      (dominated_pow_comp (fun x : {x // r.test x = true} => r.next x.1) hout
        fun x => hnext x.1 x.2)
  have heq (x : {x // r.test x = true}) : ⌜(⟨x, f (r.next x.1)⟩ : r.Return)⌝ₜ.size =
      1 + ⌜x.1⌝ₜ.size + ⌜f (r.next x.1)⌝ₜ.size := rfl
  simpa only [pow_mul, heq] using h.pow d

end Complexity.TreeProgram.Source.Recursion
