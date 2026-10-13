/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Tactic.TreeProgram.Translation

/-! # Source-guided tail loops

Callbacks are selected once. Remaining time pays for the next round or the final result;
space bounds every reachable state relative to the initial input, without a saved-call stack.
-/

@[expose] public section

namespace Complexity.TreeProgram.Source

/-- Source equations discharge the loop's functional invariant. Time itself proves termination. -/
theorem Implements.tailLoop {α β : Type*} [UniqueEncoding Tree α] [UniqueEncoding Tree β]
    {pc ps pd : TreeProgram.Value → TreeProgram.Code TreeProgram.Value}
    {test : α → Bool} {next : α → α} {finish result : α → β} {bc bs bd : Bounds α}
    (hc : Implements pc test bc) (hs : Implements ps next bs) (hd : Implements pd finish bd)
    (I : α → α → Prop) (time : α → α → ℕ) (space : α → ℕ)
    (equation : ∀ y, result y = if test y then result (next y) else finish y)
    (initial : ∀ x, I x x)
    (input_size : ∀ x y, I x y → result y = result x → ⌜y⌝ₜ.size ≤ space x)
    (check_space : ∀ x y, I x y → result y = result x → bc.peak y ≤ space x)
    (stop_bounds : ∀ x y, I x y → result y = result x → test y = false →
      bd.time y + 2 ≤ time x y ∧ bd.peak y ≤ space x)
    (step_bounds : ∀ x y, I x y → result y = result x → test y = true →
      bs.peak y ≤ space x ∧ I x (next y) ∧
        bs.time y + bc.time (next y) + 6 + time x (next y) ≤ time x y) :
    Implements (loopCode pc ps pd) result ⟨fun x => bc.time x + time x x + 4, space⟩ := by
  apply hc.loop_budget_finish hs hd (fun x y => I x y ∧ result y = result x) time space
    (fun x => ⟨initial x, rfl⟩) (fun x y h => input_size x y h.1 h.2)
    (fun x y h => check_space x y h.1 h.2)
    (fun x y h ht => (stop_bounds x y h.1 h.2 ht).1) ?_ ?_
  · intro x y hi ht
    obtain ⟨hp, hi', hb⟩ := step_bounds x y hi.1 hi.2 ht
    refine ⟨hp, ⟨hi', ?_⟩, hb⟩
    simpa only [ht, ↓reduceIte] using (equation y).symm.trans hi.2
  · intro x y hi ht
    refine ⟨(stop_bounds x y hi.1 hi.2 ht).2, ?_⟩
    simpa only [ht, Bool.false_eq_true, ↓reduceIte] using (equation y).symm.trans hi.2

end Complexity.TreeProgram.Source

end

public meta section

namespace Complexity.TreeProgram.Source

/-- A tail loop supplies ordinary callbacks, a reachable-state invariant and remaining credit.
No independent termination measure is needed when the remaining time is already defined. -/
syntax "model_fun_prop" " using " &"loop"
  " (" &"test" " := " term ")" " (" &"next" " := " term ")"
  " (" &"finish" " := " term ")" " (" &"invariant" " := " term ")"
  " (" &"time" " := " term ")" " (" &"space" " := " term ")"
  (" (" &"next_bound" " := " term ")")?
  (" using " ident)? : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| model_fun_prop using loop (test := $test) (next := $next)
      (finish := $finish) (invariant := $inv) (time := $time) (space := $space)
      $[(next_bound := $nextBound)]?
      $[using $scope:ident]?) => modelFunProp do
    withMainContext do
      let goal ← getMainGoal
      let rest := (← getGoals).drop 1
      let args := (← instantiateMVars (← goal.getType)).getAppArgs
      let source := args[4]!
      let domain := args[0]!
      let test ← elabTermEnsuringType test (← mkArrow domain (mkConst ``Bool))
      let next ← elabTermEnsuringType next (← mkArrow domain domain)
      let finish ← elabTermEnsuringType finish (← inferType source)
      let inv ← elabTermEnsuringType inv (← mkArrow domain (← mkArrow domain (mkSort .zero)))
      let time ← elabTermEnsuringType time (← mkArrow domain (← mkArrow domain (mkConst ``Nat)))
      let space ← elabTermEnsuringType space (← mkArrow domain (mkConst ``Nat))
      Term.synthesizeSyntheticMVarsNoPostponing
      let certify (name : Name) (callback : Lean.Expr) : TacticM Lean.Expr := do
        let callback ← instantiateMVars callback
        if callback.hasExprMVar then throwError "source loop: provide a concrete `{name}` callback"
        let g ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``Implementation #[callback])
        setGoals [g.mvarId!]
        evalTactic (← `(tactic| source_fun_prop $[using $scope:ident]?))
        let mut impl ← instantiateMVars g
        if impl.hasExprMVar || impl.hasSorry then
          throwError "source loop: the `{name}` callback has unfinished obligations"
        -- Apply a pointwise estimate to the already selected callback. Only the allowance
        -- changes; a failed estimate never starts another implementation search.
        if name == `next then
          if let some estimate := nextBound then
            let estimate ← elabTerm estimate none
            Term.synthesizeSyntheticMVarsNoPostponing
            let allowance ← forallTelescopeReducing (← inferType estimate) fun xs body => do
              let body ← whnf body
              unless xs.size == 1 && body.isAppOfArity ``And 2 do
                throwError "source loop: `next_bound` must prove both bounds for every input"
              let rhs (p : Lean.Expr) : MetaM Lean.Expr := do
                let p ← whnf p
                unless p.isAppOfArity ``Nat.le 2 do
                  throwError "source loop: `next_bound` must be a pointwise upper bound"
                return ← mkLambdaFVars xs p.appArg!
              mkAppM ``Bounds.mk #[← rhs body.getAppArgs[0]!, ← rhs body.getAppArgs[1]!]
            impl ← mkAppM ``Implementation.rebudget #[impl, allowance, estimate]
        let (bounds, equality) ← normalizeSourceBounds impl
        setGoals [goal]
        let ctx ← mkSimpContext (← `(tactic| simp -implicitDefEqProofs only
          [source_bounds, Tree.encode_self])) false
        let (_, expansion) ← withLocalDeclD `x domain fun x => do
          let (rt, _) ← simp (← mkAppM ``Bounds.time #[bounds, x]) ctx.ctx ctx.simprocs
          let (rs, _) ← simp (← mkAppM ``Bounds.peak #[bounds, x]) ctx.ctx ctx.simprocs
          let expanded ← mkAppM ``Bounds.mk
            #[← mkLambdaFVars #[x] rt.expr, ← mkLambdaFVars #[x] rs.expr]
          let ht ← mkFunExt (← mkLambdaFVars #[x] (← rt.getProof))
          let hs ← mkFunExt (← mkLambdaFVars #[x] (← rs.getProof))
          let equation ← mkAppOptM ``Bounds.ext
            #[some domain, some bounds, some expanded, some ht, some hs]
          return (expanded, equation)
        let equality ← mkEqTrans equality expansion
        let proof ← mkAppM ``Implementation.implements #[impl]
        let target ← inferType proof
        let property ← withLocalDeclD `b (← inferType target.getAppArgs[6]!) fun b =>
          mkLambdaFVars #[b] (target.setArg 6 b)
        return ← mkEqMP (← mkCongrArg property equality) proof
      let hc ← certify `test test
      let hs ← certify `next next
      let hd ← certify `finish finish
      let mut proof ← mkAppOptM ``Implements.tailLoop #[some domain, some args[1]!,
        some args[2]!, some args[3]!, none, none, none, some test, some next, some finish,
        some source, none, none, none, some hc, some hs, some hd, some inv, some time, some space]
      let mut obligations := []
      -- Only eliminate the wrappers introduced by instantiating the loop rule.
      -- Budget computation above retains its explicit equality proof.
      let obligationCtx ← Simp.mkContext
        (config := { iota := false, zeta := false, zetaDelta := false })
      for tag in #[`equation, `initial, `input_size, `check_space, `stop_bounds, `step_bounds] do
        let type ← whnf (← inferType proof)
        let (type, _) ← dsimp type.bindingDomain! obligationCtx
        let h ← mkFreshExprSyntheticOpaqueMVar type (tag := tag)
        proof := mkApp proof h
        obligations := obligations ++ [h.mvarId!]
      let actual := (← inferType proof).getAppArgs
      goal.assign (← mkAppM ``Implementation.ofImplements #[actual[4]!, actual[6]!, proof])
      setGoals rest
      return (#[], false, source, obligations)

end Complexity.TreeProgram.Source
