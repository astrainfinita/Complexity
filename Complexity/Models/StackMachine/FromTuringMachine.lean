/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.StackMachine.Deterministic
public import Complexity.Models.StackMachine.Tape
public import Complexity.Models.TuringMachine.Deterministic
public import Complexity.Control.Controller.Simulation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Simulating work tapes by Boolean stacks

The current symbols belong to finite control. Each tape's left and right sides use two
synchronized Boolean stacks, encoding a blank flag and a data bit. One tape transition is
one stack transition; the total stack length is bounded by twice the visited tape space.
The correspondence of histories (`Stack.HistRep`) holds for every choice shape and every
interpretation of the choices, and carries computations along (`ComputesWithinCostWith.toStack`).
-/

@[expose] public section

namespace Complexity.TM

namespace Stack

/-- The first track distinguishes blank from nonblank; the second carries its bit. -/
def bit (v : Option Bool) (track : Bool) : Bool :=
  if track then v.getD false else v.isSome

/-- Decode the nonblank flag and data bit at the stack tops. -/
def symbol (top : Bool → Option Bool) : Option Bool :=
  if top false == some true then top true else none

@[simp] theorem symbol_map (v : Option (Option Bool)) :
    symbol (fun b ↦ v.map (fun w ↦ bit w b)) = v.getD none := by
  cases v with
  | none => rfl
  | some v => cases v <;> simp [symbol, bit]

/-- Select the local update for one side and one bit track. -/
def op (dir : SignType) (v : Option Bool) (side track : Bool) : StackMachine.Op Bool :=
  match dir, side with
  | .neg, false | .pos, true => .pop
  | .neg, true | .pos, false => .push (bit v track)
  | .zero, _ => .nop

end Stack

variable {κ Q : Type} {xs : List Bool}

/-- The two sides of each tape are updated simultaneously. Blank output symbols are omitted;
on a valid bit-string computation every emitted source symbol is nonblank. -/
@[simps]
def Action.toStack (a : Action κ (Option Bool)) (head : κ → Option Bool) :
    StackMachine.Action (κ × Bool × Bool) Bool where
  inputMove := a.inputMove
  work i := Stack.op (a.work i.1).2 ((a.work i.1).1.getD (head i.1)) i.2.1 i.2.2
  output := a.output.bind id

/-- The symbols under the heads after an action: the written symbol for a head that stays, and
the decoded stack top on the side a moving head enters. -/
def Action.heads (a : Action κ (Option Bool)) (head : κ → Option Bool)
    (top : (κ × Bool × Bool) → Option Bool) (i : κ) : Option Bool :=
  match (a.work i).2 with
  | .zero => (a.work i).1.getD (head i)
  | .neg => Stack.symbol (fun b ↦ top (i, false, b))
  | .pos => Stack.symbol (fun b ↦ top (i, true, b))

/-- Simulate each bit-alphabet Turing transition with one Boolean-stack transition. The
current head symbols are part of the control state. Every choice is translated separately,
so the choice shape `F` is unchanged. -/
@[simps]
def toStack {F : Type → Type*} [Functor F] (M : TM F κ (Option Bool) Q) :
    StackMachine F (κ × Bool × Bool) Bool (Q × (κ → Option Bool)) where
  q₀ := (M.q₀, fun _ ↦ none)
  halt q := M.halt q.1
  transition q v := (fun a ↦ ((a.1, a.2.heads q.2 v.2), a.2.toStack q.2)) <$>
    M.transition q.1 (v.1, q.2)

namespace Stack

/-- The encoded tape segments lie in the intervals `V`. The simulation takes `V` to be the
intervals visited by the source history ending in `c`. -/
structure Rep (V : κ → NonemptyInterval ℤ)
    (c : Q × Cfg κ (Option Bool) (xs.map some).toArray)
    (d : (Q × (κ → Option Bool)) × StackMachine.Cfg (κ × Bool × Bool) Bool xs.toArray) :
    Prop where
  state_eq : d.1.1 = c.1
  input_eq : d.2.inputPos.val = c.2.inputPos.val
  output_eq : d.2.output = c.2.output.filterMap id
  tapes : ∀ i, ∃ l r : List (Option Bool),
    (∀ b, d.2.stacks (i, false, b) = l.map (fun v ↦ bit v b)) ∧
    (∀ b, d.2.stacks (i, true, b) = r.map (fun v ↦ bit v b)) ∧
    StackMachine.Tape.Rep (c.2.workTapes i) (c.2.workPos i) l (d.1.2 i) r ∧
    (V i).fst ≤ c.2.workPos i - l.length ∧ c.2.workPos i + r.length ≤ (V i).snd

variable {V : κ → NonemptyInterval ℤ}
  {c : Q × Cfg κ (Option Bool) (xs.map some).toArray}
  {d : (Q × (κ → Option Bool)) × StackMachine.Cfg (κ × Bool × Bool) Bool xs.toArray}

theorem Rep.observe (h : Rep V c d) :
    observe c.2 =
      ((observe d.2 : Option Bool × ((κ × Bool × Bool) → Option Bool)).1, d.1.2) := by
  apply Prod.ext
  · cases hp : c.2.inputPos.val with
    | zero =>
      simp [Cfg.observe_def, Cfg.inputSymbol, StackMachine.observe_def, h.input_eq, hp,
        show (default : Option Bool) = none from rfl]
    | succ n =>
      cases hx : xs[n]? <;>
        simp [Cfg.observe_def, Cfg.inputSymbol, StackMachine.observe_def, h.input_eq, hp, hx,
          show (default : Option Bool) = none from rfl]
  · funext i
    obtain ⟨l, r, _, _, ht, _⟩ := h.tapes i
    exact ht.head_eq

theorem Rep.init {F : Type → Type*} [Functor F] (M : TM F κ (Option Bool) Q)
    (hv : ∀ i, (0 : ℤ) ∈ V i) :
    Rep V (M.init (xs.map some)) (M.toStack.init xs) where
  state_eq := rfl
  input_eq := rfl
  output_eq := rfl
  tapes i := ⟨[], [], fun _ ↦ rfl, fun _ ↦ rfl, .empty _, by
    simpa using show (V i).fst ≤ 0 ∧ 0 ≤ (V i).snd from hv i⟩

/-- Simultaneous stack updates represent a source tape action inside the chosen bounds. -/
theorem Rep.apply (h : Rep V c d) (a : Q × Action κ (Option Bool))
    (hv : ∀ i, (apply a.2 c.2).workPos i ∈ V i) :
    Rep V (apply a c)
      (apply ((a.1, a.2.heads d.1.2 (fun i ↦ (d.2.stacks i).head?)), a.2.toStack d.1.2) d) where
  state_eq := rfl
  input_eq := by cases hi : a.2.inputMove <;> simp [Input.movePos, h.input_eq, hi]
  output_eq := by
    cases ho : a.2.output <;> simp [ho, h.output_eq, Array.filterMap_push]
    rfl
  tapes i := by
    obtain ⟨l, r, hl, hr, ht, hleft, hright⟩ := h.tapes i
    let w := (a.2.work i).1.getD (d.1.2 i)
    have hw : (Controller.apply a.2 c.2).workTapes i = (c.2.workTapes i).set (c.2.workPos i) w := by
      cases ho : (a.2.work i).1 <;> simp [ho, w, ← ht.head_eq]
    have hp : (V i).fst ≤ (Controller.apply a.2 c.2).workPos i ∧
        (Controller.apply a.2 c.2).workPos i ≤ (V i).snd := hv i
    simp only [Controller.apply_prod]
    cases hd : (a.2.work i).2 with
    | neg =>
      refine ⟨l.tail, w :: r, ?_, ?_, ?_, ?_, ?_⟩
      · intro b; simp [op, hd, hl, StackMachine.Op.apply]
      · intro b; simp [op, hd, hr, w, StackMachine.Op.apply]
      · rw [hw]
        simpa only [apply_workPos, Action.heads, hd, hl,
          List.head?_map, symbol_map, SignType.cast, sub_eq_add_neg,
          show (default : Option Bool) = none from rfl] using ht.move_left w
      · simp only [apply_workPos, hd, SignType.cast, List.length_tail] at hp ⊢
        omega
      · simp only [apply_workPos, hd, SignType.cast, List.length_cons] at hp ⊢
        omega
    | zero =>
      refine ⟨l, r, ?_, ?_, ?_, ?_, ?_⟩
      · intro b; simp [op, hd, hl, StackMachine.Op.apply]
      · intro b; simp [op, hd, hr, StackMachine.Op.apply]
      · rw [hw]
        simpa only [apply_workPos, Action.heads, hd,
          SignType.cast, add_zero] using ht.write w
      · simpa [hd, SignType.cast] using hleft
      · simpa [hd, SignType.cast] using hright
    | pos =>
      refine ⟨w :: l, r.tail, ?_, ?_, ?_, ?_, ?_⟩
      · intro b; simp [op, hd, hl, w, StackMachine.Op.apply]
      · intro b; simp [op, hd, hr, StackMachine.Op.apply]
      · rw [hw]
        simpa only [apply_workPos, Action.heads, hd, hr,
          List.head?_map, symbol_map, SignType.cast,
          show (default : Option Bool) = none from rfl] using ht.move_right w
      · simp only [apply_workPos, hd, SignType.cast, List.length_cons] at hp ⊢
        omega
      · simp only [apply_workPos, hd, SignType.cast, List.length_tail] at hp ⊢
        omega

/-- A larger window still contains the encoded tape segments. -/
theorem Rep.mono {V' : κ → NonemptyInterval ℤ} (h : Rep V c d) (hV : V ≤ V') : Rep V' c d where
  state_eq := h.state_eq
  input_eq := h.input_eq
  output_eq := h.output_eq
  tapes i := by
    obtain ⟨l, r, hl, hr, ht, hL, hR⟩ := h.tapes i
    have hi := NonemptyInterval.le_def.mp (hV i)
    exact ⟨l, r, hl, hr, ht, hi.1.trans hL, hR.trans hi.2⟩

theorem Rep.mass_le [Fintype κ] (h : Rep V c d) :
    d.2.mass ≤ 2 * ∑ i, ((V i).snd + 1 - (V i).fst).toNat := by
  rw [StackMachine.Cfg.mass, Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  obtain ⟨l, r, hl, hr, _, hL, hR⟩ := h.tapes i
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, hl, hr, List.length_map]
  omega

/-- A source history and a stack history of the same length: the last stack configuration
represents the last source configuration, and every stack configuration along the history
represents some source configuration, all inside the intervals the source history visited. -/
structure HistRep (p : Controller.History (Q × Cfg κ (Option Bool) (xs.map some).toArray)
      (Q × Action κ (Option Bool)))
    (q : Controller.History
      ((Q × (κ → Option Bool)) × StackMachine.Cfg (κ × Bool × Bool) Bool xs.toArray)
      ((Q × (κ → Option Bool)) × StackMachine.Action (κ × Bool × Bool) Bool)) : Prop where
  rep : Rep p.snd.visited p.last q.last
  length_eq : q.length = p.length
  forall_rep : ∀ d ∈ q.configs, ∃ c, Rep p.snd.visited c d

/-- The peak stack mass is at most twice the space of the source history. -/
theorem HistRep.configSup_mass_le [Fintype κ] {p q}
    (h : HistRep (κ := κ) (Q := Q) (xs := xs) p q) :
    q.snd.configSup StackMachine.Cfg.mass ≤ 2 * p.snd.space := by
  rw [Controller.History.configSup_le_iff, Controller.History.configs_snd]
  intro _ hd
  obtain ⟨d, hq, rfl⟩ := List.mem_map.1 hd
  obtain ⟨c, hc⟩ := h.forall_rep d hq
  exact hc.mass_le

/-- Each source step and the stack step are images of the same choice, for every choice shape
`F` and every interpretation `m`. Each branch is represented inside the intervals visited by its
own history. -/
theorem HistRep.liftRel_stepWith {F : Type → Type*} [Functor F] (m : Type → Type*) [Monad m]
    [LawfulMonad m] [MonadLiftT F m] [LawfulFunctorLiftT F m] (M : TM F κ (Option Bool) Q)
    {p q} (h : HistRep (xs := xs) p q) :
    LiftRel HistRep (M.stepWith m p) (M.toStack.stepWith m q) := by
  have ht : (Controller.observe q.last.2 : Option Bool × ((κ × Bool × Bool) → Option Bool)).2 =
      fun i ↦ (q.last.2.stacks i).head? := rfl
  refine Controller.liftRel_stepWith_of_map m h (by simp [Controller.Halted, h.rep.state_eq])
    (fun a ↦ ((a.1, a.2.heads q.last.1.2 fun i ↦ (q.last.2.stacks i).head?),
      a.2.toStack q.last.1.2))
    (by simp only [toStack_transition, Controller.History.state_def,
      Controller.History.observe_def, Controller.state_prod, Controller.observe_prod,
      h.rep.state_eq, ← h.rep.observe, ht]) fun a ↦ ?_
  have hv : p.snd.visited ≤ (p.snd.snoc a.2).visited := by
    rw [Controller.History.visited_snoc]
    exact le_sup_left
  have hr := (h.rep.mono hv).apply a fun i ↦ by
    simpa only [Controller.History.last_snoc, Controller.History.last_snd]
      using (p.snd.snoc a.2).head_mem i
  refine ⟨?_, ?_, ?_⟩
  · rw [Controller.History.apply_last, Controller.History.apply_last,
      Controller.History.snd_apply]
    exact hr
  · simp [Controller.History.apply_def, h.length_eq]
  · rw [Controller.History.snd_apply, Controller.History.apply_def,
      Controller.History.configs_snoc]
    intro d hd
    rcases List.mem_append.1 hd with hd | hd
    · obtain ⟨c, hc⟩ := h.forall_rep d hd
      exact ⟨c, hc.mono hv⟩
    · exact ⟨_, List.mem_singleton.1 hd ▸ hr⟩

end Stack

/-- Runs match for every choice shape `F` and every interpretation `m`: the source history and
the stack history are images of the same run. Each branch is represented inside the intervals
visited by its own history. With `m = Multiset`, every source branch corresponds to exactly one
stack branch, retaining multiplicities (`LiftRel.multisetRel`). -/
theorem liftRel_runHistoryWith_toStack {F : Type → Type*} [Functor F] (m : Type → Type*)
    [Monad m] [LawfulMonad m] [MonadLiftT F m] [LawfulFunctorLiftT F m]
    (M : TM F κ (Option Bool) Q) (xs : List Bool) (n : ℕ) :
    LiftRel Stack.HistRep (M.runHistoryWith m (xs.map some) n)
      (M.toStack.runHistoryWith m xs n) := by
  have h : Stack.Rep (Controller.History.nil (Action := Q × Action κ (Option Bool))
      (M.init (xs.map some))).snd.visited (M.init (xs.map some)) (M.toStack.init xs) := by
    rw [Controller.History.snd_nil, Controller.History.visited_nil]
    exact Stack.Rep.init M fun _ ↦ NonemptyInterval.mem_pure_self _
  refine Controller.liftRel_runFromWith m M M.toStack (fun _ _ h ↦ h.liftRel_stepWith m M)
    ⟨h, rfl, fun d hd ↦ ?_⟩ n
  rw [Controller.History.configs_nil, List.mem_singleton] at hd
  exact ⟨_, hd ▸ h⟩

/-- Boolean-stack simulation passes a computation along, for every choice shape and every
interpretation: it preserves time and bounds the peak stack mass by twice the visited tape space.
On `Multiset` the outputs of the branches correspond with their multiplicities. -/
theorem _root_.Complexity.Controller.ComputesWithinCostWith.toStack [Fintype κ] {F : Type → Type*}
    [Functor F] {m : Type → Type*} [Monad m] [LawfulMonad m] [MonadLiftT F m]
    [LawfulFunctorLiftT F m] [MonadReturns m] {M : TM F κ (Option Bool) Q} {outs : m (List Bool)}
    {t s : ℕ}
    (h : M.ComputesWithinCostWith m (xs.map some) ((·.map some) <$> outs) Controller.History.length
      Controller.History.space t s) :
    M.toStack.ComputesWithinCostWith m xs outs Controller.History.length
      (fun h ↦ h.configSup StackMachine.Cfg.mass) t (2 * s) := by
  rw [← show (·.filterMap id) <$> (·.map some) <$> outs = outs by simp [Functor.map_map]]
  exact h.of_liftRel (liftRel_runHistoryWith_toStack m M xs) (fun c ↦ c.2.output.toList)
    (fun _ _ _ ↦ by simp_all)
    (fun _ _ hr hb ↦ ⟨by simpa only [Controller.History.length_snd, hr.length_eq] using hb.1,
      hr.configSup_mass_le.trans (Nat.mul_le_mul_left 2 hb.2)⟩)
    (fun _ _ hr hp ↦ by simpa [Controller.Halted, hr.rep.state_eq] using hp)
    (fun _ _ _ hr _ ↦ by simp_all [hr.rep.output_eq])

/-- Boolean-stack simulation preserves time and bounds space by twice the source visits. -/
theorem ComputesWithin.toStack [Fintype κ] {M : TM Id κ (Option Bool) Q}
    {xs ys : List Bool} {t s : ℕ}
    (h : M.ComputesWithin (xs.map some) (ys.map some) t s) :
    M.toStack.ComputesWithin xs ys t (2 * s) :=
  Controller.ComputesWithinCostWith.toStack h

end Complexity.TM
