/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.Program.Control
public import Complexity.Data.FinEnum
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Basic.Finite.Sigma
public import Mathlib.Basic.Finite.Sum

/-! # Program syntax with finite branching

The operation signature is fixed before forming a program. No syntax constructor stores an
arbitrary intermediate type. Loops charge a dispatch action, so an immediately returning body
does not introduce an unguarded cycle. A choice node selects an action and a numbered
continuation under the choice shape `F` of one controller transition; deterministic programs use
`F = Id`.
-/

@[expose] public section

namespace Complexity
namespace Program

/-- The small set of return shapes used inside syntax. -/
inductive Kind where
  | value
  | branch (n r : ℕ)

/-- Interpret a return shape with a fixed external result type. -/
abbrev Kind.Value (α : Type) : Kind → Type
  | .value => α
  | .branch n r => Fin n ⊕ Fin r

/-- Syntax indexed by a small return shape, with the external type fixed as a parameter. -/
inductive Syntax (F : Type → Type) (O A Op : Type) (Ret : Op → Type) (α : Type) :
    Kind → Type where
  | ret {u : Kind} (a : Kind.Value α u) : Syntax F O A Op Ret α u
  | step {u : Kind} (o : Op) (k : Ret o → Syntax F O A Op Ret α u) :
      Syntax F O A Op Ret α u
  | choice {u : Kind} {d : ℕ} (x : F (A × Fin d))
      (k : Fin d → Syntax F O A Op Ret α u) : Syntax F O A Op Ret α u
  | loop {u : Kind} {n r : ℕ} (a : A) (i : Fin n)
      (body : Fin n → Syntax F O A Op Ret α (.branch n r))
      (k : Fin r → Syntax F O A Op Ret α u) : Syntax F O A Op Ret α u
  | call {u : Kind} {c d : ℕ} (b : Control Id O A (Fin c) (Fin d))
      (k : Fin d → Syntax F O A Op Ret α u) : Syntax F O A Op Ret α u

end Program

/-- A program has an arbitrary fixed external result type and lives in `Type`. -/
abbrev Program (F : Type → Type) (O A Op : Type) (Ret : Op → Type) (α : Type) : Type :=
  Program.Syntax F O A Op Ret α .value

namespace Program
namespace Syntax

variable {F : Type → Type} {O A Op α β γ : Type} {Ret : Op → Type} {u v w : Kind}

/-- Change the external type and result shape while preserving the operations. -/
def mapResult {u : Kind} (p : Syntax F O A Op Ret α u) (β : Type) (v : Kind)
    (f : Kind.Value α u → Kind.Value β v) : Syntax F O A Op Ret β v :=
  match p with
  | .ret a => .ret (f a)
  | .step o k => .step o (fun x ↦ (k x).mapResult β v f)
  | .choice x k => .choice x (fun j ↦ (k j).mapResult β v f)
  | .loop a i body k =>
      .loop a i (fun j ↦ (body j).mapResult β (.branch _ _) id)
        (fun x ↦ (k x).mapResult β v f)
  | .call b k => .call b (fun x ↦ (k x).mapResult β v f)

/-- Substitute returns without saving an arbitrary intermediate type in syntax. -/
def bindTo {u v : Kind} (p : Syntax F O A Op Ret α u)
    (f : Kind.Value α u → Syntax F O A Op Ret β v) : Syntax F O A Op Ret β v :=
  match p with
  | .ret a => f a
  | .step o k => .step o (fun x ↦ bindTo (k x) f)
  | .choice x k => .choice x (fun j ↦ bindTo (k j) f)
  | .loop a i body k =>
      .loop a i (fun j ↦ (body j).mapResult β (.branch _ _) id) (fun x ↦ bindTo (k x) f)
  | .call b k => .call b (fun x ↦ bindTo (k x) f)

@[simp] theorem mapResult_id (p : Syntax F O A Op Ret α u) : p.mapResult α u id = p := by
  induction p with
  | ret a => rfl
  | step o k ih => simp only [mapResult, ih]
  | choice x k ih => simp only [mapResult, ih]
  | loop a i body k hb hk => simp only [mapResult, hb, hk]
  | call b k ih => simp only [mapResult, ih]

theorem mapResult_comp (p : Syntax F O A Op Ret α u) (f : Kind.Value α u → Kind.Value β v)
    (g : Kind.Value β v → Kind.Value γ w) :
    (p.mapResult β v f).mapResult γ w g = p.mapResult γ w (g ∘ f) := by
  induction p generalizing β γ v w with
  | ret a => rfl
  | step o k ih => simp only [mapResult, ih]
  | choice x k ih => simp only [mapResult, ih]
  | @loop u n r a i body k hb hk =>
    simp only [mapResult, hk]
    congr 1
    funext j
    apply hb j
  | call b k ih => simp only [mapResult, ih]

@[simp] theorem ret_bindTo (a : Kind.Value α u) (f : Kind.Value α u → Syntax F O A Op Ret β v) :
    bindTo (.ret a) f = f a := rfl

@[simp] theorem bindTo_ret (p : Syntax F O A Op Ret α u) : bindTo p .ret = p := by
  induction p with
  | ret a => rfl
  | step o k ih => simp only [bindTo, ih]
  | choice x k ih => simp only [bindTo, ih]
  | loop a i body k _ ih =>
    simp only [bindTo, ih]
    congr 1
    funext j
    exact mapResult_id (body j)
  | call b k ih => simp only [bindTo, ih]

theorem bindTo_assoc (p : Syntax F O A Op Ret α u)
    (f : Kind.Value α u → Syntax F O A Op Ret β v) (g : Kind.Value β v → Syntax F O A Op Ret γ w) :
    bindTo (bindTo p f) g = bindTo p (fun a ↦ bindTo (f a) g) := by
  induction p generalizing β γ v w with
  | ret a => rfl
  | step o k ih => simp only [bindTo, ih]
  | choice x k ih => simp only [bindTo, ih]
  | @loop u n r a i body k _ ih =>
    simp only [bindTo, ih]
    congr 1
    funext j
    apply mapResult_comp (body j)
  | call b k ih => simp only [bindTo, ih]

/-- Native control states generated from syntax. -/
def State : {u : Kind} → Syntax F O A Op Ret α u → Type
  | _, .ret _ => PEmpty
  | _, .step _ k => PUnit ⊕ ((x : _) × State (k x))
  | _, .choice _ k => PUnit ⊕ ((j : _) × State (k j))
  | _, .loop (n := n) _ _ body k =>
      Fin n ⊕ (((i : _) × State (body i)) ⊕ ((j : _) × State (k j)))
  | _, .call (c := c) _ k => Fin c ⊕ ((j : _) × State (k j))

/-- Native exit labels generated from continuations. -/
def Exit : {u : Kind} → Syntax F O A Op Ret α u → Type
  | _, .ret _ => PUnit
  | _, .step _ k => (x : _) × Exit (k x)
  | _, .choice _ k => (j : _) × Exit (k j)
  | _, .loop _ _ _ k => (j : _) × Exit (k j)
  | _, .call _ k => (j : _) × Exit (k j)

/-- Read the result attached to an exit label. -/
def result : {u : Kind} → (p : Syntax F O A Op Ret α u) → p.Exit → Kind.Value α u
  | _, .ret a => fun _ ↦ a
  | _, .step _o k => fun e ↦ result (k e.1) e.2
  | _, .choice _ k => fun e ↦ result (k e.1) e.2
  | _, .loop _ _ _ k => fun e ↦ result (k e.1) e.2
  | _, .call _ k => fun e ↦ result (k e.1) e.2

instance [∀ o, Finite (Ret o)] (p : Syntax F O A Op Ret α u) : Finite p.State := by
  induction p with
  | ret a => exact inferInstanceAs (Finite PEmpty)
  | step o k ih =>
    let := ih
    exact inferInstanceAs (Finite (PUnit ⊕ ((x : Ret o) × State (k x))))
  | choice x k ih =>
    let := ih
    exact inferInstanceAs (Finite (PUnit ⊕ ((j : _) × State (k j))))
  | loop a i body k hb hk =>
    let := hb
    let := hk
    exact inferInstanceAs (Finite (_ ⊕ (((i : _) × State (body i)) ⊕
      ((j : _) × State (k j)))))
  | call b k ih =>
    let := ih
    exact inferInstanceAs (Finite (_ ⊕ ((j : _) × State (k j))))

instance [∀ o, Finite (Ret o)] (p : Syntax F O A Op Ret α u) : Finite p.Exit := by
  induction p with
  | ret a => exact inferInstanceAs (Finite PUnit)
  | step o k ih =>
    let := ih
    exact inferInstanceAs (Finite ((x : Ret o) × Exit (k x)))
  | choice x k ih =>
    let := ih
    exact inferInstanceAs (Finite ((j : _) × Exit (k j)))
  | loop a i body k _ ih =>
    let := ih
    exact inferInstanceAs (Finite ((j : _) × Exit (k j)))
  | call b k ih =>
    let := ih
    exact inferInstanceAs (Finite ((j : _) × Exit (k j)))

/-- Transform the choice shape of every choice node while preserving operations and control. -/
def mapChoice {G : Type → Type} (φ : ∀ {β : Type}, F β → G β) :
    {u : Kind} → Syntax F O A Op Ret α u → Syntax G O A Op Ret α u
  | _, .ret a => .ret a
  | _, .step o k => .step o (fun x ↦ (k x).mapChoice φ)
  | _, .choice x k => .choice (φ x) (fun j ↦ (k j).mapChoice φ)
  | _, .loop a i body k =>
      .loop a i (fun j ↦ (body j).mapChoice φ) (fun j ↦ (k j).mapChoice φ)
  | _, .call b k => .call b (fun j ↦ (k j).mapChoice φ)

/-- Embed a deterministic syntax tree into any choice shape with `Pure`: each choice node
becomes the constant choice of its unique alternative. -/
def ofId [Pure F] (p : Syntax Id O A Op Ret α u) : Syntax F O A Op Ret α u :=
  p.mapChoice fun x ↦ pure x.run

@[simp] theorem mapChoice_id (p : Syntax F O A Op Ret α u) : p.mapChoice (fun x ↦ x) = p := by
  induction p with
  | ret a => rfl
  | step o k ih => simp only [mapChoice, ih]
  | choice x k ih => simp only [mapChoice, ih]
  | loop a i body k hb hk => simp only [mapChoice, hb, hk]
  | call b k ih => simp only [mapChoice, ih]

theorem mapChoice_comp {G H : Type → Type} (φ : ∀ {β : Type}, F β → G β)
    (ψ : ∀ {β : Type}, G β → H β) (p : Syntax F O A Op Ret α u) :
    (p.mapChoice φ).mapChoice ψ = p.mapChoice (fun x ↦ ψ (φ x)) := by
  induction p with
  | ret a => rfl
  | step o k ih => simp only [mapChoice, ih]
  | choice x k ih => simp only [mapChoice, ih]
  | loop a i body k hb hk => simp only [mapChoice, hb, hk]
  | call b k ih => simp only [mapChoice, ih]

theorem mapChoice_mapResult {G : Type → Type} (φ : ∀ {β : Type}, F β → G β)
    (p : Syntax F O A Op Ret α u) (f : Kind.Value α u → Kind.Value β v) :
    (p.mapResult β v f).mapChoice φ = (p.mapChoice φ).mapResult β v f := by
  induction p generalizing β v with
  | ret a => rfl
  | step o k ih => simp only [mapResult, mapChoice, ih]
  | choice x k ih => simp only [mapResult, mapChoice, ih]
  | loop a i body k hb hk => simp only [mapResult, mapChoice, hb, hk]
  | call b k ih => simp only [mapResult, mapChoice, ih]

theorem mapChoice_bindTo {G : Type → Type} (φ : ∀ {β : Type}, F β → G β)
    (p : Syntax F O A Op Ret α u) (f : Kind.Value α u → Syntax F O A Op Ret β v) :
    (p.bindTo f).mapChoice φ = (p.mapChoice φ).bindTo (fun a ↦ (f a).mapChoice φ) := by
  induction p generalizing β v with
  | ret a => rfl
  | step o k ih => simp only [bindTo, mapChoice, ih]
  | choice x k ih => simp only [bindTo, mapChoice, ih]
  | loop a i body k _ hk => simp only [bindTo, mapChoice, mapChoice_mapResult, hk]
  | call b k ih => simp only [bindTo, mapChoice, ih]

end Syntax

variable {F : Type → Type} {O A Op α β γ : Type} {Ret : Op → Type}

/-- Return without taking an action. -/
def ret (a : α) : Program F O A Op Ret α := Syntax.ret a

/-- Return without taking an action. -/
abbrev pure (a : α) : Program F O A Op Ret α := ret a

/-- Perform an operation and continue with its result. -/
def step (o : Op) (k : Ret o → Program F O A Op Ret α) : Program F O A Op Ret α :=
  Syntax.step o k

/-- Perform one primitive operation and return its result. -/
def perform (o : Op) : Program F O A Op Ret (Ret o) := step o ret

/-- A finite loop with an explicit dispatch action.

`dispatch` runs before every body entry, including the first, and costs one transition.
The action type `A` need not have a no-op, so the caller chooses the action; it may change
the configuration. The dispatch also gives a continuing pure body a positive iteration cost. -/
def loop {n r : ℕ} (dispatch : A) (body : Fin n → Program F O A Op Ret (Fin n ⊕ Fin r))
    (i : Fin n) : Program F O A Op Ret (Fin r) :=
  Syntax.loop dispatch i (fun j ↦ (body j).mapResult (Fin r) (.branch n r) id)
    (fun j ↦ Syntax.ret j)

/-- Call an external control graph and select a continuation by its numbered exit.

The block and its continuation use the caller's current configuration. Connecting an exit
to its continuation adds no transition. This interface takes a `Control` and an explicit
continuation; `TM.Program.call` instead takes a machine and returns its halting state. -/
def callControl {c d : ℕ} (b : Control Id O A (Fin c) (Fin d))
    (k : Fin d → Program F O A Op Ret α) : Program F O A Op Ret α := Syntax.call b k

/-- Perform one choice, under `F`, of an action and a numbered continuation, and return the
number. The choice costs one transition. -/
def chooseAct {d : ℕ} (x : F (A × Fin d)) : Program F O A Op Ret (Fin d) :=
  Syntax.choice x (fun j ↦ Syntax.ret j)

/-- Select a finite result under `F` while executing an explicit dispatch action.

As in `loop`, the caller chooses `dispatch` because `A` has no assumed no-op; the choice costs
one transition. Only the result needs `FinEnum`, which numbers the continuations. -/
def chooseWith [Functor F] {β : Type} [FinEnum β] (dispatch : A) (c : F β) :
    Program F O A Op Ret β :=
  Syntax.choice ((fun b ↦ (dispatch, FinEnum.equiv b)) <$> c)
    (fun j ↦ Syntax.ret (FinEnum.equiv.symm j))

/-- Replace every ordinary return by the chosen continuation. -/
def bind (p : Program F O A Op Ret α) (f : α → Program F O A Op Ret β) :
    Program F O A Op Ret β := Syntax.bindTo p f

instance : Monad (Program F O A Op Ret) where
  pure := ret
  bind := bind

@[simp] theorem ret_bind (a : α) (f : α → Program F O A Op Ret β) : bind (ret a) f = f a := rfl

@[simp] theorem bind_ret (p : Program F O A Op Ret α) : bind p ret = p := Syntax.bindTo_ret p

theorem bind_assoc (p : Program F O A Op Ret α) (f : α → Program F O A Op Ret β)
    (g : β → Program F O A Op Ret γ) : bind (bind p f) g = bind p (fun a ↦ bind (f a) g) :=
  Syntax.bindTo_assoc p f g

instance : LawfulMonad (Program F O A Op Ret) :=
  LawfulMonad.mk' _ (fun p ↦ bind_ret p) (fun a f ↦ ret_bind a f)
    (fun p f g ↦ bind_assoc p f g)

/-- Repeat the body until it returns `true`, using an explicit dispatch action.

`dispatch` runs before every body execution, including the first, and costs one transition.
It may change the configuration: the generic action type `A` has no assumed no-op.
`TM.Program.repeatUntil` fixes this choice to the machine's `idle` action. -/
def repeatUntilWith (dispatch : A) (p : Program F O A Op Ret Bool) :
    Program F O A Op Ret Unit := do
  let _ ← loop dispatch (fun _ : Fin 1 ↦ do
    let b ← p
    pure (if b then Sum.inr (0 : Fin 1) else Sum.inl (0 : Fin 1))) 0
  pure ()

/-- Internal control states generated from the source syntax. -/
abbrev State (p : Program F O A Op Ret α) := Syntax.State p
/-- Terminal labels generated from the source syntax. -/
abbrev Exit (p : Program F O A Op Ret α) := Syntax.Exit p
/-- The value associated with a terminal label. -/
abbrev result (p : Program F O A Op Ret α) : p.Exit → α := Syntax.result p

end Program
end Complexity
