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
-/

@[expose] public section

namespace Complexity.Program

namespace Syntax

variable {O A Op α : Type} {Ret : Op → Type} {u : Kind}

/-- Include the continuation of an operation. -/
def stepLabel (o : Op) (k : Ret o → Syntax O A Op Ret α u) (x : Ret o) :
    (k x).State ⊕ (k x).Exit → (Syntax.step o k).State ⊕ (Syntax.step o k).Exit
  | .inl q => .inl (.inr ⟨x, q⟩)
  | .inr e => .inr ⟨x, e⟩

/-- Include a continuation after a loop. -/
def loopCont {n r : ℕ} (a : A) (i : Fin n)
    (b : Fin n → Syntax O A Op Ret α (.branch n r))
    (k : Fin r → Syntax O A Op Ret α u) (j : Fin r) :
    (k j).State ⊕ (k j).Exit → (Syntax.loop a i b k).State ⊕ (Syntax.loop a i b k).Exit
  | .inl q => .inl (.inr (.inr ⟨j, q⟩))
  | .inr e => .inr ⟨j, e⟩

/-- Continue at a dispatcher or at a continuation after the loop. -/
def loopRoute {n r : ℕ} (a : A) (i : Fin n)
    (b : Fin n → Syntax O A Op Ret α (.branch n r))
    (k : Fin r → Syntax O A Op Ret α u)
    (c : (j : Fin r) → (k j).State ⊕ (k j).Exit) :
    Fin n ⊕ Fin r → (Syntax.loop a i b k).State ⊕ (Syntax.loop a i b k).Exit
  | .inl j => .inl (.inl j)
  | .inr j => loopCont a i b k j (c j)

/-- Include the states of a loop body and connect its exits to back edges. -/
def loopLabel {n r : ℕ} (a : A) (i : Fin n)
    (b : Fin n → Syntax O A Op Ret α (.branch n r))
    (k : Fin r → Syntax O A Op Ret α u)
    (c : (j : Fin r) → (k j).State ⊕ (k j).Exit) (j : Fin n) :
    (b j).State ⊕ (b j).Exit → (Syntax.loop a i b k).State ⊕ (Syntax.loop a i b k).Exit
  | .inl q => .inl (.inr (.inl ⟨j, q⟩))
  | .inr e => loopRoute a i b k c ((b j).result e)

/-- Include the continuation of an external controller. -/
def callCont {c d : ℕ} (b : Control O A (Fin c) (Fin d))
    (k : Fin d → Syntax O A Op Ret α u) (j : Fin d) :
    (k j).State ⊕ (k j).Exit → (Syntax.call b k).State ⊕ (Syntax.call b k).Exit
  | .inl q => .inl (.inr ⟨j, q⟩)
  | .inr e => .inr ⟨j, e⟩

/-- External exits connect to their continuation without an extra transition. -/
def callLabel {c d : ℕ} (b : Control O A (Fin c) (Fin d))
    (k : Fin d → Syntax O A Op Ret α u)
    (f : (j : Fin d) → (k j).State ⊕ (k j).Exit) :
    Fin c ⊕ Fin d → (Syntax.call b k).State ⊕ (Syntax.call b k).Exit
  | .inl q => .inl (.inl q)
  | .inr j => callCont b k j (f j)

/-- Compile a finite syntax tree, sharing loop bodies through back edges. -/
def compile (eval : (o : Op) → O → A × Ret o) :
    {u : Kind} → (p : Syntax O A Op Ret α u) → Control O A p.State p.Exit
  | _, .ret _ =>
      { start := .inr ⟨⟩
        next := PEmpty.elim }
  | _, .step o k =>
      { start := .inl (.inl ⟨⟩)
        next := fun q v ↦ match q with
          | .inl _ =>
              let (a, x) := eval o v
              (a, stepLabel o k x (compile eval (k x)).start)
          | .inr ⟨x, q⟩ =>
              let (a, q') := (compile eval (k x)).next q v
              (a, stepLabel o k x q') }
  | _, .loop a i b k =>
      let c := fun j ↦ (compile eval (k j)).start
      { start := .inl (.inl i)
        next := fun q v ↦ match q with
          | .inl j => (a, loopLabel a i b k c j (compile eval (b j)).start)
          | .inr (.inl ⟨j, q⟩) =>
              let (a', q') := (compile eval (b j)).next q v
              (a', loopLabel a i b k c j q')
          | .inr (.inr ⟨j, q⟩) =>
              let (a', q') := (compile eval (k j)).next q v
              (a', loopCont a i b k j q') }
  | _, .call b k =>
      let c := fun j ↦ (compile eval (k j)).start
      { start := callLabel b k c b.start
        next := fun q v ↦ match q with
          | .inl q =>
              let (a, q') := b.next q v
              (a, callLabel b k c q')
          | .inr ⟨j, q⟩ =>
              let (a, q') := (compile eval (k j)).next q v
              (a, callCont b k j q') }

/-- A returned value enters directly at its unique terminal label. -/
@[simp] theorem start_ret (eval : (o : Op) → O → A × Ret o) (a : Kind.Value α u) :
    (compile eval (Syntax.ret a : Syntax O A Op Ret α u)).start = .inr PUnit.unit := by
  simp only [compile]

/-- An imported controller takes its own transition before routing its destination. -/
@[simp] theorem next_call_inl (eval : (o : Op) → O → A × Ret o)
    {c d : ℕ} (b : Control O A (Fin c) (Fin d)) (k : Fin d → Syntax O A Op Ret α u)
    (q : Fin c) (o : O) :
    (compile eval (Syntax.call b k)).next (.inl q) o =
      ((b.next q o).1, callLabel b k (fun j ↦ (compile eval (k j)).start) (b.next q o).2) := by
  simp only [compile]

end Syntax

variable {O A Op α : Type} {Ret : Op → Type}

/-- Compile a program without storing or numbering its generated control types. -/
def compile (eval : (o : Op) → O → A × Ret o) (p : Program O A Op Ret α) :
    Control O A p.State p.Exit := Syntax.compile eval p

end Complexity.Program
