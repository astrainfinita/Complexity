/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Tactic.TreeProgram.Implementation
public import Complexity.Models.TreeMachine.Language.CaseView
public import Complexity.Encoding.Sigma
public import Complexity.Tactic.TreeProgram.Attributes
public meta import Complexity.Tactic.TreeProgram.Search
public meta import Lean.Meta.Match.MatcherApp.Transform

/-! # Translating `match`

`HasProgram.cases` is the elimination rule of every type with a `CaseView`: a value computed from
the input selects a constructor, and the branch of that constructor receives the input with the
constructor's fields. Its growth is stated by branch (`CaseView.atBranch`). `casesRule` translates a
`match` on a part of the input by this rule: the branch of a constructor is the source at the input
rebuilt with the constructor at that part, reduced.
-/

@[expose] public section

universe u

namespace Complexity.TreeProgram.CaseView

variable {α : Type*} {T : α → Type u} [∀ x, UniqueEncoding Tree (T x)] {k : ℕ}
  [∀ x, CaseView (T x) k]

/-- The inputs at which `d` has the constructor `i`, with the constructor's fields. -/
abbrev Branch (d : (x : α) → T x) (i : Fin k) :=
  {y : Σ x, Payload (T x) i // d y.1 = ofPayload i y.2}

/-- A quantity of the branch taken at `x`, from one for each branch. -/
abbrev atBranch (d : (x : α) → T x) (g : (i : Fin k) → Branch d i → ℕ) (x : α) : ℕ :=
  elim (d x) fun i p h => g i ⟨⟨x, p⟩, h⟩

theorem atBranch_eq (d : (x : α) → T x) (g : (i : Fin k) → Branch d i → ℕ) {x : α}
    {i : Fin k} {p : Payload (T x) i} (h : d x = ofPayload i p) :
    atBranch d g x = g i ⟨⟨x, p⟩, h⟩ :=
  elim_eq _ h

end Complexity.TreeProgram.CaseView

namespace Complexity.TreeProgram.Source

open Internal (HasProgram)

open TreeProgram CaseView

variable {α : Type*} {T : α → Type u} [UniqueEncoding Tree α] [∀ x, UniqueEncoding Tree (T x)]
  {k : ℕ} [∀ x, CaseView (T x) k]

omit [UniqueEncoding Tree α] in
/-- Domination at the branch taken, from domination on every branch. -/
theorem Dominated.atBranch (d : (x : α) → T x) {a b : (i : Fin k) → Branch d i → ℕ}
    (h : ∀ i, Dominated (a i) (b i)) : Dominated (atBranch d a) (atBranch d b) := by
  choose C hC using fun i => dominated_iff.mp (h i)
  refine Dominated.of_le_mul (∑ i, C i) fun x => ?_
  obtain ⟨i, p, hp⟩ := exists_ofPayload (d x)
  rw [atBranch_eq d a hp.symm, atBranch_eq d b hp.symm]
  exact (hC i _).trans (Nat.mul_le_mul_right _ (Finset.single_le_sum
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)))

variable {β : α → Type*} [∀ x, UniqueEncoding Tree (β x)]

/-- Branch on the constructor of a computed value: the branch of each constructor receives the
input with the constructor's fields. One decision `D` on codes serves every input. -/
theorem Internal.HasProgram.cases (D : CaseTree k) (hD : ∀ x, dispatch (T x) = D)
    {d : (x : α) → T x} {f : (x : α) → β x} {qd : Value → Code Value} {td pd : α → ℕ}
    (hd : HasProgram d qd td pd) {q : Fin k → Value → Code Value}
    {t p : (i : Fin k) → Branch d i → ℕ}
    (hb : ∀ i, HasProgram (fun y : Branch d i => f y.1.1) (q i) (t i) (p i)) :
    HasProgram f
      (fun v => do let w ← qd v; D.run w fun i a => do let e ← Value.pair v a; q i e)
      (fun x => td x + atBranch d t x + 1)
      (fun x => max (pd x)
        (atBranch d (fun i y => max (1 + ⌜y.1.1⌝ₜ.size + ⌜y.1.2⌝ₜ.size) (p i y)) x)) := by
  obtain ⟨bd, hbd, hdt, hdp⟩ := hd.sound
  choose b hb hbt hbp using fun i => (hb i).sound
  have h := hbd.bind_input (r := fun w v => D.run w fun i a => do let e ← Value.pair v a; q i e)
    (g := f) (time := fun x => 1 + atBranch d (fun i => (b i).time) x + D.cost)
    (peak := fun x => max ⌜d x⌝ₜ.size
      (atBranch d (fun i y => max (1 + ⌜y.1.1⌝ₜ.size + ⌜y.1.2⌝ₜ.size) ((b i).peak y)) x))
    (fun u v n hu _ => D.run_fresh (fun i a m ha => by
      have := (hb i).1 (.var m) (m + 1) le_rfl
      simp only [Value.pair, Code.build_bind, Code.eval_build]
      exact ⟨(Nat.le_succ m).trans this.1, this.2⟩) hu) ?_
  · refine ⟨_, h, ?_, ?_⟩
    · exact ((hdt.add (Dominated.atBranch d hbt)).add
        (Dominated.const (1 + D.cost))).mono_left fun x => by dsimp only; omega
    · refine (hdp.max (Dominated.atBranch d fun i =>
        (Dominated.refl fun y : Branch d i => 1 + ⌜y.1.1⌝ₜ.size + ⌜y.1.2⌝ₜ.size).max
          (hbp i))).mono_left fun x => ?_
      obtain ⟨i, pl, hpl⟩ := exists_ofPayload (d x)
      have := hbd.size_le x
      dsimp only
      rw [atBranch_eq d _ hpl.symm]
      simp only [le_max_iff, max_le_iff] at *
      omega
  · intro u v n s x hu hv hux hvx
    obtain ⟨i, pl, hpl⟩ := exists_ofPayload (d x)
    have hsel : D.select (u.eval s) = (i, ⌜pl⌝ₜ) := by
      rw [hux, ← hD x, ← select_encode, hpl]
    rw [atBranch_eq d _ hpl.symm, atBranch_eq d _ hpl.symm]
    set y : Branch d i := ⟨⟨x, pl⟩, hpl.symm⟩
    have hy : ⌜y⌝ₜ.size = 1 + ⌜x⌝ₜ.size + ⌜pl⌝ₜ.size := rfl
    have hY := (hb i).size_le y
    rw [hy] at hY
    apply (D.run_bounded hu (time := 1 + (b i).time y)
      (by rw [hux]; exact le_max_left _ _) (hY.trans (le_max_right _ _)) ?_).mono
      (by omega) le_rfl (fun _ _ h => h)
    intro m t a hm ha ht hat
    rw [hsel] at hat ⊢
    have hvt : v.eval t = ⌜x⌝ₜ := (v.eval_eq_of_forall_lt hv ht).trans hvx
    have hcode : Tree.pair (v.eval t) (a.eval t) = ⌜y⌝ₜ := by
      simp [y, hvt, hat, Sigma.encode_mk]
    have hsteps : (v.expression.pair a.expression).assignSteps = 1 := by
      cases v <;> cases a <;> simp
    simp only [Value.pair, Code.bounded_eval_bind_iff, Expr.eval_pair, Value.eval_expression,
      Expr.maxSize, Value.maxSize_expression, hcode, hy]
    refine ⟨by omega, ?_, ?_⟩
    · simp only [hvt, hat, max_le_iff]
      refine ⟨?_, ?_, le_max_of_le_right (le_max_left _ _)⟩ <;> omega
    · apply ((hb i).2 (.var m) (m + 1) _ y le_rfl (by simp)).mono (by omega)
        ((le_max_right _ _).trans (le_max_right _ _))
      intro r w ⟨hr, hw⟩
      exact ⟨hr, fun j hj => (hw j (by omega)).trans (by simp [Nat.ne_of_lt hj])⟩

/-- A branch no input reaches, such as a constructor excluded by a subtype, has every program. -/
theorem Internal.HasProgram.of_false {f : (x : α) → β x} (h : α → False) :
    HasProgram f (fun _ => pure .nil) (fun _ => 0) (fun _ => 0) :=
  ⟨⟨fun _ => 0, fun _ => 0⟩, ⟨fun _ _ _ => ⟨le_rfl, Nat.zero_le _⟩,
    fun _ _ _ x => (h x).elim⟩, .refl _, .refl _⟩

end Complexity.TreeProgram.Source

end

public meta section

namespace Complexity.TreeProgram.Source

open Internal (HasProgram)

open Lean Meta in
/-- Unfold the `match` at the head of a source body and reduce: eliminations of constructors and
of structures disappear, and what remains is stuck on a value that is not a constructor. -/
private partial def unfoldCases (e : Lean.Expr) : MetaM Lean.Expr := do
  let e ← whnfCore e
  if let some app ← matchMatcherApp? e then
    let info ← getConstInfo app.matcherName
    unless info.value?.isSome do return e
    return ← unfoldCases
      ((← instantiateValueLevelParams info app.matcherLevels.toList).beta e.getAppArgs)
  -- A `casesOn` with a catch-all, as overlapping patterns compile to.
  let some name := e.getAppFn.constName? | return e
  unless isCasesOnLike (← getEnv) name do return e
  let some e ← unfoldDefinition? e | return e
  unfoldCases e

open Lean Meta in
/-- The structure projections leading from `x` to `e`, starting at `x`. -/
private partial def projectionPath? (x e : Lean.Expr) : MetaM (Option (List (Name × Nat))) := do
  if e == x then return some []
  match e with
  | .proj s i b => return (← projectionPath? x b).map (· ++ [(s, i)])
  | .mdata _ b => projectionPath? x b
  | .app .. =>
    let some name := e.getAppFn.constName? | return none
    let some info ← getProjectionFnInfo? name | return none
    unless !info.fromClass && e.getAppNumArgs == info.numParams + 1 do return none
    let s := (← getConstInfoCtor info.ctorName).induct
    return (← projectionPath? x e.appArg!).map (· ++ [(s, info.i)])
  | _ => return none

open Lean Meta in
/-- Reduce the projections of constructor applications in a branch body. -/
private def reduceProjections (e : Lean.Expr) : MetaM Lean.Expr :=
  Meta.transform e (post := fun e => do
    let (s, i) ← match e with
      | .proj _ i s => pure (s, i)
      | _ =>
        let some name := e.getAppFn.constName? | return .done e
        let some info ← getProjectionFnInfo? name | return .done e
        unless !info.fromClass && e.getAppNumArgs == info.numParams + 1 do return .done e
        pure (e.appArg!, info.i)
    let s := s.headBeta
    let some (.ctorInfo ctor) := s.getAppFn.constName?.map ((← getEnv).find? ·) |>.join
      | return .done e
    return .visit (s.getArg! (ctor.numParams + i)))

open Lean Meta in
/-- The function `fun c h => b'` where `b'` is `b` with its part at `path` replaced by `c`, and
`h : part = c` transports the proofs stored in `b` about the part. -/
private def rebuildFn (b part : Lean.Expr) (path : List (Name × Nat)) :
    MetaM (Option Lean.Expr) := do
  withLocalDeclD `c (← inferType part) fun c => do
  withLocalDeclD `h (← mkEq part c) fun h => do
    let rec go (b : Lean.Expr) : List (Name × Nat) → MetaM (Option Lean.Expr)
      | [] => return some c
      | (s, i) :: path => do
        let some inner ← go (.proj s i b) path | return none
        let type ← whnf (← inferType b)
        let ctor := getStructureCtor (← getEnv) s
        let .const _ levels := type.getAppFn | return none
        let params := type.getAppArgs.extract 0 ctor.numParams
        let mut ctorType ← instantiateForall (← inferType (mkConst ctor.name levels)) params
        let mut fields := #[]
        for j in [:ctor.numFields] do
          let .forallE _ fieldType _ _ ← whnf ctorType | return none
          -- A field type reading only the other parts does not depend on the replaced one.
          let fieldType ← reduceProjections fieldType.headBeta
          let value ← if j == i then pure inner
            else if !fieldType.containsFVar c.fvarId! then pure (.proj s j b)
            -- What depends on the replaced part is transported along the part's equation.
            else mkEqRec (← mkLambdaFVars #[c, h] fieldType) (.proj s j b) h
          fields := fields.push value
          ctorType := (← whnf ctorType).bindingBody!.instantiate1 value
        return some (mkAppN (mkConst ctor.name levels) (params ++ fields))
    let some e ← go b path | return none
    return some (← mkLambdaFVars #[c, h] e)

open Lean Meta in
/-- `fun i => Fin.cases v₀ (fun i => Fin.cases v₁ …) i` with the given motive on `Fin k`. -/
private partial def finCases (motive : Lean.Expr) (k : Nat) (values : List Lean.Expr) :
    MetaM Lean.Expr := do
  let fin := mkApp (mkConst ``Fin) (mkNatLit k)
  withLocalDeclD `i fin fun i => do
    match k, values with
    | k + 1, v :: values =>
      let tailMotive ← withLocalDeclD `j (mkApp (mkConst ``Fin) (mkNatLit k)) fun j => do
        mkLambdaFVars #[j] (motive.beta #[← mkAppM ``Fin.succ #[j]])
      let tail ← finCases tailMotive k values
      mkLambdaFVars #[i] (← mkAppOptM ``Fin.cases #[mkNatLit k, motive, v, tail, i])
    | _, _ => mkLambdaFVars #[i] (← mkAppOptM ``Fin.elim0 #[motive.beta #[i], i])

open Lean Meta in
/-- A growth stated by branches, written as a `match` on the value whose constructor selects the
branch: `atBranch` and the view's `elim` are unfolded, and each branch's growth is applied, with
the size of the branch's input stated by the input and the fields. -/
private def readableBranches (e : Lean.Expr) : MetaM Lean.Expr := do
  let literal? (i : Lean.Expr) : MetaM (Option Nat) := do
    if i.isAppOfArity ``Fin.mk 3 then return ← evalNat (i.getArg! 1) |>.run
    return (← getFinValue? i).map (·.2.val)
  let e ← Meta.transform e (post := fun e => do
    if e.isHeadBetaTarget then return .visit e.headBeta
    if e.isAppOfArity ``CaseView.atBranch 8 then
      let some u ← unfoldDefinition? e | return .done e
      return .visit (← withTransparency .instances <| whnf u)
    -- The growth of the branch at a constructor's literal index.
    if e.isAppOf ``Fin.cases && e.getAppNumArgs ≥ 5 then
      let args := e.getAppArgs
      if let some j ← literal? args[4]! then
        let rest := args.extract 5 args.size
        if j = 0 then return .visit (mkAppN args[2]! rest).headBeta
        let pred ← mkAppOptM ``Fin.mk #[args[0]!, mkNatLit (j - 1),
          ← mkDecideProof (← mkLt (mkNatLit (j - 1)) args[0]!)]
        return .visit (mkAppN args[3]! (#[pred] ++ rest)).headBeta
    -- The fields are stated at their own type, with its own encoding.
    if e.isAppOfArity ``CaseView.Payload 5 then
      let type ← whnfD e
      if type != e then return .visit type
    -- A view's own `match` on a constructor's index, as in the type of its fields.
    if let .reduced r ← reduceMatcher? e then return .visit r
    if e.isAppOfArity ``CaseView.encoding 5 then
      if let some inst ← synthInstance? (← whnfD (← inferType e)) then return .done inst
    -- Every code is stated with the instance its type has, as elsewhere in growths.
    if e.isAppOfArity ``UniqueEncoding.encode 4 && !e.hasLooseBVars then
      let args := e.getAppArgs
      if let some inst ← synthInstance? (← mkAppM ``UniqueEncoding #[args[0]!, args[1]!]) then
        if inst != args[2]! then return .done (mkAppN e.getAppFn (args.set! 2 inst))
    return .done e)
  -- The input of a branch at a constructor is the input with the fields: the size of its code is
  -- stated by theirs, and a unit has size one.
  Meta.transform (← reduceProjections e) (post := fun e => do
    unless e.isAppOfArity ``Tree.size 1 && e.appArg!.isAppOfArity ``UniqueEncoding.encode 4 do
      return .done e
    let v := e.appArg!.appArg!
    if v.isAppOf ``PUnit.unit then return .done (mkNatLit 1)
    unless v.isAppOfArity ``Subtype.mk 4 && (v.getArg! 2).isAppOfArity ``Sigma.mk 4 do
      return .done e
    let size (a : Lean.Expr) := do
      mkAppM ``Tree.size #[← mkAppOptM ``UniqueEncoding.encode #[mkConst ``Tree, none, none, a]]
    let some r ← observing? do
        mkAppM ``HAdd.hAdd #[← mkAppM ``HAdd.hAdd #[mkNatLit 1, ← size ((v.getArg! 2).getArg! 2)],
          ← size ((v.getArg! 2).getArg! 3)]
      | return .done e
    return .visit r)

/-- A `match` on a part of the input of a source function, with the type's `CaseView`. -/
private structure CaseSplit where
  /-- The part, as a function of the input, and its type with its encoding. -/
  part : Lean.Expr
  type : Lean.Expr
  encoding : Lean.Expr
  view : Lean.Expr
  dispatch : Lean.Expr
  constructors : Nat
  /-- The input rebuilt with the part replaced (`rebuildFn`), as a function of the input. -/
  rebuild : Lean.Expr

open Lean Meta in
/-- The part of the input that the `match` at the head of a source body eliminates, and its
view. A constructor at a fixed index is eliminated with the index it is paired with. -/
private def caseSplit? (f : Lean.Expr) : MetaM (Option CaseSplit) :=
  lambdaTelescope f fun xs body => do
    let #[x] := xs | return none
    let stuck ← unfoldCases body
    let .const name _ := stuck.getAppFn | return none
    let .recInfo info ← getConstInfo name | return none
    let some major := stuck.getAppArgs[info.getMajorIdx]? | return none
    let field (s : Name) (i : Nat) : Lean.Expr → Option Lean.Expr
      | .proj n j b => if n == s && j == i then some b else none
      | e => if e.isAppOfArity (s ++ if i == 0 then `fst else `snd) 3 then e.appArg! else none
    let candidates := match field ``Prod 0 major >>= field ``Sigma 1 with
      | some q => #[major, q]
      | none => #[major]
    for part in candidates do
      let some path ← projectionPath? x part | continue
      let T ← inferType part
      let .sort (.succ u) ← whnf (← inferType T) | continue
      let instT ← synthInstance (← mkAppM ``UniqueEncoding #[mkConst ``Tree, T])
      let k ← mkFreshExprMVar (mkConst ``Nat)
      let some view ← synthInstance? (mkApp3 (mkConst ``CaseView [u]) T instT k) | continue
      let some k ← (evalNat (← instantiateMVars k)).run | continue
      let D ← whnfD (mkApp4 (mkConst ``CaseView.dispatch [u]) T instT (mkNatLit k) view)
      if D.hasFVar then continue
      let some rebuild ← rebuildFn x part path | continue
      return some ⟨← mkLambdaFVars xs part, ← mkLambdaFVars xs T, ← mkLambdaFVars xs instT,
        ← mkLambdaFVars xs view, D, k, ← mkLambdaFVars xs rebuild⟩
    return none

open Lean Meta in
/-- The branch of constructor `i`: its inputs `{y : Σ x, P x // d x = C y.2}` at their concrete
types, and the source there as `f` at the rebuilt input, reduced, with `f y.1.1 = body`, or a
contradiction if the branch is unreachable. A result whose type depends on the replaced part is
transported back to the input. -/
private def caseBranch (f β : Lean.Expr) (c : CaseSplit) (i : Lean.Expr) :
    MetaM (Lean.Expr × (Lean.Expr × Lean.Expr ⊕ Lean.Expr)) := do
  let (payload, constructor) ← lambdaTelescope f fun xs _ => do
    let args := #[c.type.beta xs, c.encoding.beta xs, mkNatLit c.constructors, c.view.beta xs, i]
    let P ← withTransparency .instances <| whnf (← mkAppOptM ``CaseView.Payload (args.map some))
    let C ← withLocalDeclD `p P fun p => do
      mkLambdaFVars (xs.push p) (← withTransparency .instances <| whnf
        (← mkAppOptM ``CaseView.ofPayload ((args.push p).map some)))
    return (← mkLambdaFVars xs P, C)
  let B ← mkAppM ``Subtype #[← withLocalDeclD `y (← mkAppM ``Sigma #[payload]) fun y => do
    let x ← mkAppM ``Sigma.fst #[y]
    mkLambdaFVars #[y]
      (← mkEq (c.part.beta #[x]) (constructor.beta #[x, ← mkAppM ``Sigma.snd #[y]]))]
  withLocalDeclD `y B fun y => do
    let base ← mkAppM ``Sigma.fst #[← mkAppM ``Subtype.val #[y]]
    let part := c.part.beta #[base]
    let hy ← mkAppM ``Subtype.property #[y]
    let rebuild := c.rebuild.beta #[base]
    let rebuilt := rebuild.beta
      #[constructor.beta #[base, ← mkAppM ``Sigma.snd #[← mkAppM ``Subtype.val #[y]]], hy]
    let body ← reduceProjections (← unfoldCases (f.beta #[rebuilt]))
    match body.getAppFn.constName?, body.getAppArgs with
    | some ``absurd, #[_, _, h, h'] => return (B, .inr (← mkLambdaFVars #[y] (mkApp h' h)))
    | some ``False.elim, #[_, h] => return (B, .inr (← mkLambdaFVars #[y] h))
    | _, _ => pure ()
    let motive ← withLocalDeclD `c (← inferType part) fun c => do
      withLocalDeclD `h (← mkEq part c) fun h => do
        mkLambdaFVars #[c, h] (← mkEq base (rebuild.beta #[c, h]))
    let rebuiltEq ← mkEqRec motive (← mkEqRefl base) hy
    let congr ← mkAppM ``congr_arg_heq #[f, rebuiltEq]
    let (body, heq) ← if ← isDefEq (← inferType body) (← inferType (f.beta #[base])) then
        pure (body, congr)
      else
        let back ← mkEqSymm rebuiltEq
        let result ← withLocalDeclD `z (← inferType base) fun z => do
          withLocalDeclD `h (← mkEq rebuilt z) fun h => mkLambdaFVars #[z, h] (β.beta #[z])
        let transported ← mkEqRec result body back
        let heq ← mkExpectedTypeHint (← mkAppOptM ``eqRec_heq #[none, β, none, none, back, body])
          (← mkHEq transported body)
        pure (transported, ← mkAppM ``HEq.trans #[congr, ← mkHEqSymm heq])
    let equation ← mkExpectedTypeHint (← mkAppM ``eq_of_heq #[heq])
      (← mkEq (f.beta #[base]) body)
    return (B, .inl (← mkLambdaFVars #[y] body, ← mkLambdaFVars #[y] equation))

open Lean Meta Mathlib.Meta.FunProp in
/-- A `match` on a part of the input, by the elimination rule `HasProgram.cases` of the type's
`CaseView`. The branch of a constructor is the source at the input rebuilt with the constructor
at that part, which reduces the `match`; an unreachable branch is a contradiction. -/
def casesRule (search : Lean.Expr → FunPropM (Option Result)) (goal : Lean.Expr) :
    FunPropM (Option Result) := do
  let #[α, β, instα, instβ, f, _, _, _] := goal.getAppArgs | return none
  let some c ← caseSplit? f | return none
  let k := c.constructors
  let nat := mkConst ``Nat
  let programType ← mkArrow (mkConst ``Value) (mkApp (mkConst ``Code) (mkConst ``Value))
  let some hd ← search (← mkAppOptM ``HasProgram #[α, c.type, instα, c.encoding, c.part,
      ← mkFreshExprMVar programType, ← mkFreshExprMVar (← mkArrow α nat),
      ← mkFreshExprMVar (← mkArrow α nat)]) | return none
  -- The source at the input of a branch, its type and encoding.
  let atBase (B : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr × Lean.Expr) :=
      withLocalDeclD `y B fun y => do
    let base ← mkAppM ``Sigma.fst #[← mkAppM ``Subtype.val #[y]]
    return (← mkLambdaFVars #[y] (f.beta #[base]), ← mkLambdaFVars #[y] (β.beta #[base]),
      ← mkLambdaFVars #[y] (instβ.beta #[base]))
  let mut branches := #[]
  for j in [:k] do
    let i ← mkAppOptM ``Fin.mk #[mkNatLit k, mkNatLit j,
      ← mkDecideProof (← mkLt (mkNatLit j) (mkNatLit k))]
    let (B, branch) ← caseBranch f β c i
    let instB ← synthInstance (← mkAppM ``UniqueEncoding #[mkConst ``Tree, B])
    let (source, outType, outInst) ← atBase B
    let proof ← match branch with
      | .inr contradiction =>
        mkAppOptM ``HasProgram.of_false #[B, instB, outType, outInst, source, contradiction]
      | .inl (body, equation) =>
        let growth ← mkArrow B nat
        let some r ← search (← mkAppOptM ``HasProgram #[B, outType, instB, outInst, body,
            ← mkFreshExprMVar programType, ← mkFreshExprMVar growth,
            ← mkFreshExprMVar growth]) | return none
        let eq ← mkFunExt (← withLocalDeclD `y B fun y => do
          mkLambdaFVars #[y] (← mkEqSymm (equation.beta #[y])))
        mkAppM ``HasProgram.congr #[r.proof, eq]
    branches := branches.push (proof, (← instantiateMVars (← inferType proof)).getAppArgs)
  -- The branches' programs, growths and certificates as functions of the constructor.
  let fin := mkApp (mkConst ``Fin) (mkNatLit k)
  let branchType (i : Lean.Expr) :=
    mkAppOptM ``CaseView.Branch #[α, c.type, c.encoding, mkNatLit k, c.view, c.part, i]
  let byIndex (motive : Lean.Expr → MetaM Lean.Expr) (values : Array Lean.Expr) := do
    finCases (← withLocalDeclD `i fin fun i => do mkLambdaFVars #[i] (← motive i)) k values.toList
  let q ← byIndex (fun _ => pure programType) (branches.map (·.2[5]!))
  let t ← byIndex (fun i => do mkArrow (← branchType i) nat) (branches.map (·.2[6]!))
  let p ← byIndex (fun i => do mkArrow (← branchType i) nat) (branches.map (·.2[7]!))
  let hb ← byIndex (fun i => do
    let B ← branchType i
    let (source, outType, outInst) ← atBase B
    mkAppOptM ``HasProgram #[B, outType,
      ← synthInstance (← mkAppM ``UniqueEncoding #[mkConst ``Tree, B]), outInst, source,
      q.beta #[i], t.beta #[i], p.beta #[i]]) (branches.map (·.1))
  let hD ← lambdaTelescope c.view fun xs v => do
    let dispatch ← mkAppOptM ``CaseView.dispatch #[none, none, mkNatLit k, v]
    mkLambdaFVars xs (← mkExpectedTypeHint (← mkEqRefl c.dispatch) (← mkEq dispatch c.dispatch))
  let proof ← mkAppOptM ``HasProgram.cases #[α, c.type, instα, c.encoding, mkNatLit k, c.view,
    β, instβ, c.dispatch, hD, c.part, f, none, none, none, hd.proof, q, t, p, hb]
  let type ← instantiateMVars (← inferType proof)
  let type := type.setArg 6 (← readableBranches (type.getArg! 6)) |>.setArg 7
    (← readableBranches (type.getArg! 7))
  return some ⟨← mkExpectedTypeHint proof type⟩

end Complexity.TreeProgram.Source
