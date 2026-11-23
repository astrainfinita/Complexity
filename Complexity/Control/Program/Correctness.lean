/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.Program.Compiler
public import Complexity.Control.Program.Semantics

/-! # Preservation of source executions by compilation

A program meets a specification exactly when its compiled control graph, run within the budget
with its choices interpreted in `m` and read by the same quantifier, reaches exits whose results
meet the postcondition (`Syntax.execWithinWith_iff_runWithinWith`). This needs the quantifier to
read the lift of `Pure.pure a` as `a`: a deterministic transition of the compiled graph is a lifted
`Pure.pure`. Hence the compiled controller reaches, within the budget, the outcomes that a
specification describes (`Syntax.ExecWithinWith.runFromWith_compile`); a deterministic one is,
after the budget, at an exit satisfying the postcondition (`Syntax.ExecWithin.runFrom_compile`).
-/

@[expose] public section

namespace Complexity.Program

namespace Syntax

variable {F : Type → Type} {O A Op S α : Type} {Ret : Op → Type} [Functor F] [Pure F]
  {m : Type → Type} [Monad m] [MonadLiftT F m] {Q : MonadQuant m} {u : Kind}
  (eval : (o : Op) → O → A × Ret o) {observe : S → O} {act : A → S → S}

/-! The compiled graph at the entry of a node (`toControl` is not unfolded by `rfl`). -/

private theorem start_step (o : Op) (k : Ret o → Syntax F O A Op Ret α u) :
    (toControl eval (.step o k)).start = .inl (.inl PUnit.unit) := by simp only [toControl]

private theorem next_step (o : Op) (k : Ret o → Syntax F O A Op Ret α u) (v : O) :
    (toControl eval (.step o k)).next (.inl PUnit.unit) v = Pure.pure ((eval o v).1,
      stepLabel o k (eval o v).2 (toControl eval (k (eval o v).2)).start) := by
  simp only [toControl]

private theorem start_choice {d : ℕ} (x : F (A × Fin d)) (k : Fin d → Syntax F O A Op Ret α u) :
    (toControl eval (.choice x k)).start = .inl (.inl PUnit.unit) := by simp only [toControl]

private theorem next_choice {d : ℕ} (x : F (A × Fin d)) (k : Fin d → Syntax F O A Op Ret α u)
    (v : O) :
    (toControl eval (.choice x k)).next (.inl PUnit.unit) v =
      (fun r ↦ (r.1, choiceLabel x k r.2 (toControl eval (k r.2)).start)) <$> x := by
  simp only [toControl]

private theorem start_loop {n r : ℕ} (a : A) (i : Fin n)
    (b : Fin n → Syntax F O A Op Ret α (.branch n r)) (k : Fin r → Syntax F O A Op Ret α u) :
    (toControl eval (.loop a i b k)).start = .inl (.inl i) := by simp only [toControl]

private theorem next_loop {n r : ℕ} (a : A) (i : Fin n)
    (b : Fin n → Syntax F O A Op Ret α (.branch n r)) (k : Fin r → Syntax F O A Op Ret α u)
    (j : Fin n) (v : O) :
    (toControl eval (.loop a i b k)).next (.inl j) v =
      Pure.pure (a, loopLabel a i b k (fun j ↦ (toControl eval (k j)).start) j
        (toControl eval (b j)).start) := by simp only [toControl]

private theorem start_call {c d : ℕ} (blk : Control Id O A (Fin c) (Fin d))
    (k : Fin d → Syntax F O A Op Ret α u) :
    (toControl eval (.call blk k)).start =
      callLabel blk k (fun j ↦ (toControl eval (k j)).start) blk.start := by
  simp only [toControl]

omit [Functor F] [Pure F] in
/-- A graph entered at an internal state takes a transition first. -/
private theorem runWithinWith_start_of_eq_inl_iff {St E : Type} {c : Control F O A St E} {q : St}
    (h : c.start = .inl q) {R : E → S → ℕ → Prop} {s : S} {b : ℕ} :
    c.RunWithinWith Q observe act R c.start s (b + 1) ↔
      Q (fun r ↦ c.RunWithinWith Q observe act R r.2 (act r.1 s) b)
        (monadLift (c.next q (observe s)) : m (A × (St ⊕ E))) := by
  rw [h]
  exact Iff.rfl

/-! The compiled graph of a node, entered at a label of a continuation, runs the continuation. -/

variable [LawfulMonad m] [LawfulFunctorLiftT F m]

private theorem runWithinWith_stepLabel_iff (o : Op) (k : Ret o → Syntax F O A Op Ret α u)
    (j : Ret o) {R : (Syntax.step o k).Exit → S → ℕ → Prop} {q : (k j).State ⊕ (k j).Exit}
    {s : S} {b : ℕ} :
    (toControl eval (.step o k)).RunWithinWith Q observe act R (stepLabel o k j q) s b ↔
      (toControl eval (k j)).RunWithinWith Q observe act (fun x ↦ R ⟨j, x⟩) q s b := by
  rw [show stepLabel o k j q = Sum.map (fun q ↦ Sum.inr ⟨j, q⟩) (fun x ↦ ⟨j, x⟩) q by
    cases q <;> rfl]
  refine Control.runWithinWith_relabel_iff _ _ fun q v ↦ ?_
  simp only [toControl]
  exact congrArg (· <$> _) (funext fun r ↦ by rcases r with ⟨_, _ | _⟩ <;> rfl)

private theorem runWithinWith_choiceLabel_iff {d : ℕ} (x : F (A × Fin d))
    (k : Fin d → Syntax F O A Op Ret α u) (j : Fin d)
    {R : (Syntax.choice x k).Exit → S → ℕ → Prop} {q : (k j).State ⊕ (k j).Exit} {s : S}
    {b : ℕ} :
    (toControl eval (.choice x k)).RunWithinWith Q observe act R (choiceLabel x k j q) s b ↔
      (toControl eval (k j)).RunWithinWith Q observe act (fun y ↦ R ⟨j, y⟩) q s b := by
  rw [show choiceLabel x k j q = Sum.map (fun q ↦ Sum.inr ⟨j, q⟩) (fun x ↦ ⟨j, x⟩) q by
    cases q <;> rfl]
  refine Control.runWithinWith_relabel_iff _ _ fun q v ↦ ?_
  simp only [toControl]
  exact congrArg (· <$> _) (funext fun r ↦ by rcases r with ⟨_, _ | _⟩ <;> rfl)

private theorem runWithinWith_loopCont_iff {n r : ℕ} (a : A) (i : Fin n)
    (b0 : Fin n → Syntax F O A Op Ret α (.branch n r)) (k : Fin r → Syntax F O A Op Ret α u)
    (j : Fin r) {R : (Syntax.loop a i b0 k).Exit → S → ℕ → Prop}
    {q : (k j).State ⊕ (k j).Exit} {s : S} {b : ℕ} :
    (toControl eval (.loop a i b0 k)).RunWithinWith Q observe act R (loopCont a i b0 k j q) s b ↔
      (toControl eval (k j)).RunWithinWith Q observe act (fun x ↦ R ⟨j, x⟩) q s b := by
  rw [show loopCont a i b0 k j q = Sum.map (fun q ↦ Sum.inr (.inr ⟨j, q⟩)) (fun x ↦ ⟨j, x⟩) q by
    cases q <;> rfl]
  refine Control.runWithinWith_relabel_iff _ _ fun q v ↦ ?_
  simp only [toControl]
  exact congrArg (· <$> _) (funext fun r ↦ by rcases r with ⟨_, _ | _⟩ <;> rfl)

private theorem runWithinWith_callCont_iff {c d : ℕ} (blk : Control Id O A (Fin c) (Fin d))
    (k : Fin d → Syntax F O A Op Ret α u) (j : Fin d)
    {R : (Syntax.call blk k).Exit → S → ℕ → Prop} {q : (k j).State ⊕ (k j).Exit} {s : S}
    {b : ℕ} :
    (toControl eval (.call blk k)).RunWithinWith Q observe act R (callCont blk k j q) s b ↔
      (toControl eval (k j)).RunWithinWith Q observe act (fun x ↦ R ⟨j, x⟩) q s b := by
  rw [show callCont blk k j q = Sum.map (fun q ↦ Sum.inr ⟨j, q⟩) (fun x ↦ ⟨j, x⟩) q by
    cases q <;> rfl]
  refine Control.runWithinWith_relabel_iff _ _ fun q v ↦ ?_
  simp only [toControl]
  exact congrArg (· <$> _) (funext fun r ↦ by rcases r with ⟨_, _ | _⟩ <;> rfl)

/-- The exits of a loop body continue at the next dispatch or after the loop. -/
private theorem runWithinWith_loopLabel_iff {n r : ℕ} (a : A) (i : Fin n)
    (b0 : Fin n → Syntax F O A Op Ret α (.branch n r)) (k : Fin r → Syntax F O A Op Ret α u)
    (j : Fin n) {R : (Syntax.loop a i b0 k).Exit → S → ℕ → Prop}
    {q : (b0 j).State ⊕ (b0 j).Exit} {s : S} {b : ℕ} :
    (toControl eval (.loop a i b0 k)).RunWithinWith Q observe act R
      (loopLabel a i b0 k (fun j ↦ (toControl eval (k j)).start) j q) s b ↔
      (toControl eval (b0 j)).RunWithinWith Q observe act (fun x t b' ↦
        (toControl eval (.loop a i b0 k)).RunWithinWith Q observe act R
          (loopRoute a i b0 k (fun j ↦ (toControl eval (k j)).start) ((b0 j).result x)) t b')
        q s b := by
  rw [show loopLabel a i b0 k (fun j ↦ (toControl eval (k j)).start) j q =
      Sum.elim (fun q ↦ Sum.inl (Sum.inr (Sum.inl ⟨j, q⟩)))
        (loopRoute a i b0 k (fun j ↦ (toControl eval (k j)).start) ∘ (b0 j).result) q by
    cases q <;> rfl]
  refine Control.runWithinWith_link_iff _ _ fun q v ↦ ?_
  simp only [toControl]
  exact congrArg (· <$> _) (funext fun r ↦ by rcases r with ⟨_, _ | _⟩ <;> rfl)

variable [MonadQuant.PureLiftT F m Q]

/-- The block of a call makes deterministic transitions, and passes to the continuation at its
exit. -/
private theorem runWithinWith_callLabel_iff {c d : ℕ} (blk : Control Id O A (Fin c) (Fin d))
    (k : Fin d → Syntax F O A Op Ret α u) {R : (Syntax.call blk k).Exit → S → ℕ → Prop}
    {q : Fin c ⊕ Fin d} {s : S} {b : ℕ} :
    (toControl eval (.call blk k)).RunWithinWith Q observe act R
      (callLabel blk k (fun j ↦ (toControl eval (k j)).start) q) s b ↔
      blk.RunWithin observe act (fun j t b' ↦ (toControl eval (k j)).RunWithinWith Q observe act
        (fun x ↦ R ⟨j, x⟩) (toControl eval (k j)).start t b') q s b := by
  induction b generalizing q s with
  | zero =>
    rcases q with q | j
    · exact Iff.rfl
    · rw [callLabel, runWithinWith_callCont_iff]
      exact Iff.rfl
  | succ b ih =>
    rcases q with q | j
    · refine (Control.runWithinWith_inl_succ_iff (c := toControl eval (.call blk k))).trans ?_
      rw [next_call_inl, Q.monadLift_pure_iff, Control.runWithin_inl_succ_iff]
      exact ih
    · rw [callLabel, runWithinWith_callCont_iff]
      exact Iff.rfl

/-- A program meets a specification exactly when its compiled graph, run within the budget,
reaches exits whose results meet the postcondition. -/
theorem execWithinWith_iff_runWithinWith {e : Semantics O A Op Ret S}
    {p : Syntax F O A Op Ret α u} {s : S} {b : ℕ} {R : Kind.Value α u → S → ℕ → Prop} :
    p.ExecWithinWith m Q e s b R ↔ (toControl e.eval p).RunWithinWith Q e.observe e.act
      (fun x t b' ↦ R (p.result x) t b') (toControl e.eval p).start s b := by
  induction p generalizing s b with
  | ret a =>
    rw [execWithinWith_ret_iff, start_ret]
    cases b <;> exact Iff.rfl
  | step o k ih =>
    rw [execWithinWith_step_iff]
    rcases b with _ | b
    · rw [start_step]
      exact iff_of_false (fun h ↦ Nat.lt_irrefl 0 h.1) id
    · rw [runWithinWith_start_of_eq_inl_iff (start_step e.eval o k), next_step,
        Q.monadLift_pure_iff]
      dsimp only
      rw [runWithinWith_stepLabel_iff]
      exact (and_iff_right b.succ_pos).trans (ih _)
  | choice x k ih =>
    rw [execWithinWith_choice_iff]
    rcases b with _ | b
    · rw [start_choice]
      exact iff_of_false (fun h ↦ Nat.lt_irrefl 0 h.1) id
    · rw [runWithinWith_start_of_eq_inl_iff (start_choice e.eval x k), next_choice,
        LawfulFunctorLiftT.monadLift_map, Q.map_iff]
      simp only [runWithinWith_choiceLabel_iff]
      exact (and_iff_right b.succ_pos).trans
        ⟨Q.mono fun r h ↦ (ih r.2).1 h, Q.mono fun r h ↦ (ih r.2).2 h⟩
  | «loop» a i body k ihb ihk =>
    induction b using Nat.strong_induction_on generalizing i s with
    | h b ihl =>
      rw [execWithinWith_loop_iff]
      rcases b with _ | b
      · rw [start_loop]
        exact iff_of_false (fun h ↦ Nat.lt_irrefl 0 h.1) id
      · rw [runWithinWith_start_of_eq_inl_iff (start_loop e.eval a i body k), next_loop,
          Q.monadLift_pure_iff]
        dsimp only
        rw [runWithinWith_loopLabel_iff, ← ihb i (R := fun y t b' ↦
          (toControl e.eval (.loop a i body k)).RunWithinWith Q e.observe e.act
            (fun x t b' ↦ R ((Syntax.loop a i body k).result x) t b')
            (loopRoute a i body k (fun j ↦ (toControl e.eval (k j)).start) y) t b'),
          and_iff_right b.succ_pos]
        have key : ∀ y t b', b' ≤ b → ((match y with
            | .inl j => (Syntax.loop a j body k).ExecWithinWith m Q e t b' R
            | .inr j => (k j).ExecWithinWith m Q e t b' R) ↔
            (toControl e.eval (.loop a i body k)).RunWithinWith Q e.observe e.act
              (fun x t b' ↦ R ((Syntax.loop a i body k).result x) t b')
              (loopRoute a i body k (fun j ↦ (toControl e.eval (k j)).start) y) t b') := by
          rintro (j | j) t b' hb'
          · have hn : (toControl e.eval (.loop a j body k)).next =
                (toControl e.eval (.loop a i body k)).next := by
              funext q o
              rcases q with j | (⟨j, q⟩ | ⟨j, q⟩)
              all_goals simp only [toControl, loopLabel, loopRoute, loopCont, Syntax.State,
                Syntax.Exit]
            refine (ihl b' (by omega) j).trans ?_
            rw [start_loop, Control.runWithinWith_congr_next hn]
            exact Iff.rfl
          · refine (ihk j).trans ?_
            rw [loopRoute, runWithinWith_loopCont_iff]
            exact Iff.rfl
        refine ⟨fun h ↦ h.with_le.mono fun y t b' ⟨hb', hy⟩ ↦ ?_,
          fun h ↦ h.with_le.mono fun y t b' ⟨hb', hy⟩ ↦ ?_⟩
        · rcases y with j | j <;> exact (key _ t b' (by omega)).1 hy
        · rcases y with j | j <;> exact (key _ t b' hb').2 hy
  | call blk k ih =>
    rw [start_call, runWithinWith_callLabel_iff, execWithinWith_call_iff]
    exact ⟨fun h ↦ h.mono fun j t b' hj ↦ (ih j).1 hj, fun h ↦ h.mono fun j t b' hj ↦ (ih j).2 hj⟩

/-- A specification of a program describes its compiled controller, when the semantics observes
and acts through the storage's controller instances: the quantifier holds of the configurations
that the controller reaches after the budget, each an exit carrying a result that satisfies the
postcondition with some remaining budget. -/
theorem ExecWithinWith.runFromWith_compile [Controller.Observe S O] [Controller.Apply S A]
    {p : Syntax F O A Op Ret α u} {s : S} {n : ℕ} {R : Kind.Value α u → S → ℕ → Prop} (idle : A)
    (h : p.ExecWithinWith m Q ⟨eval, Controller.observe, Controller.apply⟩ s n R) :
    Q (fun cfg ↦ ∃ x t, cfg = (.inr x, t) ∧ ∃ b ≤ n, R (p.result x) t b)
      ((compile eval idle p).runFromWith m ((compile eval idle p).q₀, s) n) := by
  rw [compile, Control.toController_q₀]
  exact (Control.runWithinWith_iff_runFromWith_toController idle).1
    ((execWithinWith_iff_runWithinWith.1 h.with_le).mono fun x t b ⟨hb, hR⟩ ↦ ⟨b, hb, hR⟩)

/-- When the semantics observes and acts through the storage's controller instances, a
deterministic execution within a budget describes the compiled controller: after the budget it is
at an exit carrying a result that satisfies the postcondition with some remaining budget. -/
theorem ExecWithin.runFrom_compile [Controller.Observe S O] [Controller.Apply S A]
    {eval : (o : Op) → O → A × Ret o} {p : Syntax Id O A Op Ret α u} {s : S} {b : ℕ}
    {R : Kind.Value α u → S → ℕ → Prop} (idle : A)
    (h : p.ExecWithin ⟨eval, Controller.observe, Controller.apply⟩ s b R) :
    ∃ x t, (compile eval idle p).runFrom ((compile eval idle p).q₀, s) b = (.inr x, t) ∧
      ∃ b' ≤ b, R (p.result x) t b' :=
  ExecWithinWith.runFromWith_compile eval idle h _ rfl

end Syntax

end Complexity.Program
