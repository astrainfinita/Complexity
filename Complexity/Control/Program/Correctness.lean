/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.Program.Compiler
public import Complexity.Control.Program.Semantics

/-! # Exact preservation of source executions by compilation -/

@[expose] public section

namespace Complexity.Program

variable {O A Op S α : Type} {Ret : Op → Type}

namespace Syntax

variable {u : Kind} (e : Semantics O A Op Ret S)

private theorem run_step (o : Op) (k : Ret o → Syntax O A Op Ret α u) (j : Ret o)
    {q : (k j).State ⊕ (k j).Exit} {s t : S} {n : ℕ} {x : Kind.Value α u}
    (h : Control.Run (toControl e.eval (k j)) (k j).result e.observe e.act q s n x t) :
    Control.Run (toControl e.eval (.step o k)) (Syntax.step o k).result e.observe e.act
      (stepLabel o k j q) s n x t := by
  have hh := h.relabel (d := toControl e.eval (.step o k))
    (out' := (Syntax.step o k).result) (fun q ↦ Sum.inr ⟨j, q⟩) (fun x ↦ ⟨j, x⟩)
    (by
      intro q v
      simp only [toControl]
      cases hnext : (toControl e.eval (k j)).next q v with
      | mk a q => cases q <;> simp only [hnext] <;> rfl)
    (fun _ ↦ rfl)
  cases q <;> exact hh

private theorem run_loop_cont {n r : ℕ} (a : A) (i : Fin n)
    (b : Fin n → Syntax O A Op Ret α (.branch n r))
    (k : Fin r → Syntax O A Op Ret α u) (j : Fin r)
    {q : (k j).State ⊕ (k j).Exit} {s t : S} {m : ℕ} {x : Kind.Value α u}
    (h : Control.Run (toControl e.eval (k j)) (k j).result e.observe e.act q s m x t) :
    Control.Run (toControl e.eval (.loop a i b k)) (Syntax.loop a i b k).result e.observe e.act
      (loopCont a i b k j q) s m x t := by
  have hh := h.relabel (d := toControl e.eval (.loop a i b k))
    (out' := (Syntax.loop a i b k).result)
    (fun q ↦ Sum.inr (.inr ⟨j, q⟩)) (fun x ↦ ⟨j, x⟩)
    (by
      intro q v
      simp only [toControl]
      cases hnext : (toControl e.eval (k j)).next q v with
      | mk a q => cases q <;> simp only [hnext] <;> rfl)
    (fun _ ↦ rfl)
  cases q <;> exact hh

private theorem run_loop_body {n r : ℕ} (a : A) (i : Fin n)
    (b : Fin n → Syntax O A Op Ret α (.branch n r))
    (k : Fin r → Syntax O A Op Ret α u) (j : Fin n)
    {q : (b j).State ⊕ (b j).Exit} {s t z : S} {m l : ℕ}
    {v : Fin n ⊕ Fin r} {x : Kind.Value α u}
    (h : Control.Run (toControl e.eval (b j)) (b j).result e.observe e.act q s m v t)
    (ht : Control.Run (toControl e.eval (.loop a i b k)) (Syntax.loop a i b k).result
      e.observe e.act (loopRoute a i b k (fun j ↦ (toControl e.eval (k j)).start) v) t l x z) :
    Control.Run (toControl e.eval (.loop a i b k)) (Syntax.loop a i b k).result e.observe e.act
      (loopLabel a i b k (fun j ↦ (toControl e.eval (k j)).start) j q) s (m + l) x z := by
  have hh := h.link (d := toControl e.eval (.loop a i b k))
    (fun q ↦ Sum.inr (.inl ⟨j, q⟩))
    (fun q ↦ loopRoute a i b k (fun j ↦ (toControl e.eval (k j)).start) ((b j).result q))
    (by
      intro q o
      simp only [toControl]
      cases hnext : (toControl e.eval (b j)).next q o with
      | mk a q => cases q <;> simp only [hnext] <;> rfl)
    (by intro q hq; simpa only [hq] using ht)
  cases q <;> exact hh

private theorem run_call_cont {c d : ℕ} (b : Control O A (Fin c) (Fin d))
    (k : Fin d → Syntax O A Op Ret α u) (j : Fin d)
    {q : (k j).State ⊕ (k j).Exit} {s t : S} {m : ℕ} {x : Kind.Value α u}
    (h : Control.Run (toControl e.eval (k j)) (k j).result e.observe e.act q s m x t) :
    Control.Run (toControl e.eval (.call b k)) (Syntax.call b k).result e.observe e.act
      (callCont b k j q) s m x t := by
  have hh := h.relabel (d := toControl e.eval (.call b k))
    (out' := (Syntax.call b k).result)
    (fun q ↦ Sum.inr ⟨j, q⟩) (fun x ↦ ⟨j, x⟩)
    (by
      intro q v
      simp only [toControl]
      cases hnext : (toControl e.eval (k j)).next q v with
      | mk a q => cases q <;> simp only [hnext] <;> rfl)
    (fun _ ↦ rfl)
  cases q <;> exact hh

private theorem run_call_block {c d : ℕ} (b : Control O A (Fin c) (Fin d))
    (k : Fin d → Syntax O A Op Ret α u)
    {q : Fin c ⊕ Fin d} {s t z : S} {m l : ℕ} {j : Fin d} {x : Kind.Value α u}
    (h : Control.Run b id e.observe e.act q s m j t)
    (ht : Control.Run (toControl e.eval (k j)) (k j).result e.observe e.act
      (toControl e.eval (k j)).start t l x z) :
    Control.Run (toControl e.eval (.call b k)) (Syntax.call b k).result e.observe e.act
      (callLabel b k (fun j ↦ (toControl e.eval (k j)).start) q) s (m + l) x z := by
  have hh := h.link (d := toControl e.eval (.call b k))
    Sum.inl
    (fun j ↦ callCont b k j (toControl e.eval (k j)).start)
    (by
      intro q v
      simp only [toControl]
      cases hnext : b.next q v with
      | mk a q => cases q <;> simp only [hnext] <;> rfl)
    (by intro j' hj; cases hj; exact run_call_cont e b k j' ht)
  cases q <;> exact hh

variable {e}

/-- Compilation preserves the exact action count, result, and final semantic state.

The execution proof determines the semantics, so the theorem is used as `h.toControl`.
It applies directly to `Program` as well as general `Syntax`. -/
theorem Exec.toControl {p : Syntax O A Op Ret α u} {s t : S} {n : ℕ} {x : Kind.Value α u}
    (h : Exec e p s n x t) :
    Control.Run (Syntax.toControl e.eval p) p.result e.observe e.act
      (Syntax.toControl e.eval p).start s n x t := by
  induction h with
  | ret a s =>
    simp only [Syntax.toControl]
    exact .done PUnit.unit s
  | step o k s h ih =>
    simp only [Syntax.toControl]
    apply Control.Run.step
    simpa only [Syntax.toControl] using run_step e o k _ ih
  | loop_done a i b k hb hk ihb ihk =>
    simp only [Syntax.toControl]
    apply Control.Run.step
    simpa only [Syntax.toControl] using
      run_loop_body e a i b k i ihb (run_loop_cont e a i b k _ ihk)
  | loop_next a i b k hb hk ihb ihk =>
    have hloop := ihk.congr_next (d := Syntax.toControl e.eval (.loop a i b k))
      (by
        funext q o
        rcases q with j | (⟨j, q⟩ | ⟨j, q⟩)
        all_goals simp only [Syntax.toControl, loopLabel, loopRoute, loopCont, State, Exit])
    simp only [Syntax.toControl]
    apply Control.Run.step
    simpa only [Syntax.toControl] using
      run_loop_body e a i b k i ihb
        (by simpa only [Syntax.toControl, loopRoute, result, State, Exit] using hloop)
  | call b k hb hk ih =>
    simpa only [Syntax.toControl] using run_call_block e b k hb ih

end Syntax

end Complexity.Program
