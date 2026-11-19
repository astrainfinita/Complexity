/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.Program.Syntax

/-! # Compiling syntax to a controller with structural labels

The control and exit types are parameters of the compiled controller. Neither the source
program nor the controller stores a type as a field. Compilation does not enumerate labels.
The compiled controller has the choice shape `F` of the source syntax.
-/

@[expose] public section

namespace Complexity.Program

namespace Syntax

variable {F : Type → Type} {O A Op α : Type} {Ret : Op → Type} {u : Kind}

/-- Include the continuation of an operation. -/
def stepLabel (o : Op) (k : Ret o → Syntax F O A Op Ret α u) (x : Ret o) :
    (k x).State ⊕ (k x).Exit → (Syntax.step o k).State ⊕ (Syntax.step o k).Exit
  | .inl q => .inl (.inr ⟨x, q⟩)
  | .inr e => .inr ⟨x, e⟩

/-- Include the continuation selected by a choice. -/
def choiceLabel {d : ℕ} (x : F (A × Fin d)) (k : Fin d → Syntax F O A Op Ret α u) (j : Fin d) :
    (k j).State ⊕ (k j).Exit → (Syntax.choice x k).State ⊕ (Syntax.choice x k).Exit
  | .inl q => .inl (.inr ⟨j, q⟩)
  | .inr e => .inr ⟨j, e⟩

/-- Include a continuation after a loop. -/
def loopCont {n r : ℕ} (a : A) (i : Fin n)
    (b : Fin n → Syntax F O A Op Ret α (.branch n r))
    (k : Fin r → Syntax F O A Op Ret α u) (j : Fin r) :
    (k j).State ⊕ (k j).Exit → (Syntax.loop a i b k).State ⊕ (Syntax.loop a i b k).Exit
  | .inl q => .inl (.inr (.inr ⟨j, q⟩))
  | .inr e => .inr ⟨j, e⟩

/-- Continue at a dispatcher or at a continuation after the loop. -/
def loopRoute {n r : ℕ} (a : A) (i : Fin n)
    (b : Fin n → Syntax F O A Op Ret α (.branch n r))
    (k : Fin r → Syntax F O A Op Ret α u)
    (c : (j : Fin r) → (k j).State ⊕ (k j).Exit) :
    Fin n ⊕ Fin r → (Syntax.loop a i b k).State ⊕ (Syntax.loop a i b k).Exit
  | .inl j => .inl (.inl j)
  | .inr j => loopCont a i b k j (c j)

/-- Include the states of a loop body and connect its exits to back edges. -/
def loopLabel {n r : ℕ} (a : A) (i : Fin n)
    (b : Fin n → Syntax F O A Op Ret α (.branch n r))
    (k : Fin r → Syntax F O A Op Ret α u)
    (c : (j : Fin r) → (k j).State ⊕ (k j).Exit) (j : Fin n) :
    (b j).State ⊕ (b j).Exit → (Syntax.loop a i b k).State ⊕ (Syntax.loop a i b k).Exit
  | .inl q => .inl (.inr (.inl ⟨j, q⟩))
  | .inr e => loopRoute a i b k c ((b j).result e)

/-- Include the continuation of an external controller. -/
def callCont {c d : ℕ} (b : Control Id O A (Fin c) (Fin d))
    (k : Fin d → Syntax F O A Op Ret α u) (j : Fin d) :
    (k j).State ⊕ (k j).Exit → (Syntax.call b k).State ⊕ (Syntax.call b k).Exit
  | .inl q => .inl (.inr ⟨j, q⟩)
  | .inr e => .inr ⟨j, e⟩

/-- External exits connect to their continuation without an extra transition. -/
def callLabel {c d : ℕ} (b : Control Id O A (Fin c) (Fin d))
    (k : Fin d → Syntax F O A Op Ret α u)
    (f : (j : Fin d) → (k j).State ⊕ (k j).Exit) :
    Fin c ⊕ Fin d → (Syntax.call b k).State ⊕ (Syntax.call b k).Exit
  | .inl q => .inl (.inl q)
  | .inr j => callCont b k j (f j)

/-- Convert finite syntax to a control graph, sharing loop bodies through back edges.

`eval` maps an operation and observation to an action and a result. It is explicit because
the syntax does not choose its interpreter. The graph has separate internal and exit labels,
with returned values recovered by `p.result`; it neither stores nor numbers the label types.

Both general syntax and `Program`, its value-returning specialization, use `p.toControl eval`.
`compile` turns the graph into a controller with initial state, halting test, and
transitions. -/
def toControl [Functor F] [Pure F] (eval : (o : Op) → O → A × Ret o) :
    {u : Kind} → (p : Syntax F O A Op Ret α u) → Control F O A p.State p.Exit
  | _, .ret _ =>
      { start := .inr ⟨⟩
        next := PEmpty.elim }
  | _, .step o k =>
      { start := .inl (.inl ⟨⟩)
        next := fun q v ↦ match q with
          | .inl _ =>
              let (a, x) := eval o v
              Pure.pure (a, stepLabel o k x (toControl eval (k x)).start)
          | .inr ⟨x, q⟩ =>
              (fun (a, q') ↦ (a, stepLabel o k x q')) <$> (toControl eval (k x)).next q v }
  | _, .choice x k =>
      { start := .inl (.inl ⟨⟩)
        next := fun q v ↦ match q with
          | .inl _ => (fun (a, j) ↦ (a, choiceLabel x k j (toControl eval (k j)).start)) <$> x
          | .inr ⟨j, q⟩ =>
              (fun (a, q') ↦ (a, choiceLabel x k j q')) <$> (toControl eval (k j)).next q v }
  | _, .loop a i b k =>
      let c := fun j ↦ (toControl eval (k j)).start
      { start := .inl (.inl i)
        next := fun q v ↦ match q with
          | .inl j => Pure.pure (a, loopLabel a i b k c j (toControl eval (b j)).start)
          | .inr (.inl ⟨j, q⟩) =>
              (fun (a', q') ↦ (a', loopLabel a i b k c j q')) <$> (toControl eval (b j)).next q v
          | .inr (.inr ⟨j, q⟩) =>
              (fun (a', q') ↦ (a', loopCont a i b k j q')) <$> (toControl eval (k j)).next q v }
  | _, .call b k =>
      let c := fun j ↦ (toControl eval (k j)).start
      { start := callLabel b k c b.start
        next := fun q v ↦ match q with
          | .inl q =>
              let (a, q') := (b.next q v).run
              Pure.pure (a, callLabel b k c q')
          | .inr ⟨j, q⟩ =>
              (fun (a, q') ↦ (a, callCont b k j q')) <$> (toControl eval (k j)).next q v }

/-- A returned value enters directly at its unique terminal label. -/
@[simp] theorem start_ret [Functor F] [Pure F] (eval : (o : Op) → O → A × Ret o)
    (a : Kind.Value α u) :
    (toControl eval (Syntax.ret a : Syntax F O A Op Ret α u)).start = .inr PUnit.unit := by
  simp only [toControl]

/-- An imported controller takes its own transition before routing its destination. -/
@[simp] theorem next_call_inl [Functor F] [Pure F] (eval : (o : Op) → O → A × Ret o)
    {c d : ℕ} (b : Control Id O A (Fin c) (Fin d)) (k : Fin d → Syntax F O A Op Ret α u)
    (q : Fin c) (o : O) :
    (toControl eval (Syntax.call b k)).next (.inl q) o = Pure.pure ((b.next q o).run.1,
      callLabel b k (fun j ↦ (toControl eval (k j)).start) (b.next q o).run.2) := by
  simp only [toControl]

/-- Compile finite syntax to a controller with the same choice shape: `toControl eval` gives the
control graph and `Control.toController` runs it. Exits halt, so `idle` only fills their
transition. A model fixes `eval` and `idle` once in its own `compile`. -/
def compile [Functor F] [Pure F] (eval : (o : Op) → O → A × Ret o) (idle : A)
    (p : Syntax F O A Op Ret α u) : Controller F O A (p.State ⊕ p.Exit) :=
  (p.toControl eval).toController idle

end Syntax

end Complexity.Program
