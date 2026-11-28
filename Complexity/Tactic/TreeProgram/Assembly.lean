/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Tactic.TreeProgram.Rules
public import Complexity.Models.TreeMachine.Language.CaseView
public meta import Complexity.Tactic.TreeProgram.Search

/-! # Values assembled from the input in one step

A field of a field of the input, a closed value, and a constructor of such values have codes
assembled from subtrees of the input's code and constant trees. An `Assembly` describes such a
code; one assignment builds it, so `HasProgramInO.assemble` is proved once and each use only proves
the equation of the trees. An assembled tree has at most `Assembly.weight` nodes per node of the
input, so `HasProgramInO.assemble` bounds the peak by the input's code size alone.
-/

@[expose] public section

open Complexity TreeProgram

namespace Complexity.TreeProgram

namespace Expr

theorem assignSteps_le_steps (e : Expr ℕ) : e.assignSteps ≤ e.steps + 2 := by
  cases e <;> simp

end Expr

/-- A tree assembled from subtrees of an input tree and constant trees. -/
inductive Assembly where
  | read (path : List Bool)
  | const (T : Tree)
  | pair (a b : Assembly)

namespace Assembly

/-- The tree assembled from the input tree `t`. -/
def eval (t : Tree) : Assembly → Tree
  | read path => t.subtree path
  | const T => T
  | pair a b => .pair (a.eval t) (b.eval t)

theorem eval_read (t : Tree) (path : List Bool) : (read path).eval t = t.subtree path := rfl

theorem eval_const (t T : Tree) : (const T).eval t = T := rfl

theorem eval_pair (t : Tree) (a b : Assembly) :
    (pair a b).eval t = .pair (a.eval t) (b.eval t) := rfl

/-- The expression assembling the tree from the input's expression. -/
def expr (i : Expr ℕ) : Assembly → Expr ℕ
  | read path => i.subtree path
  | const T => .ofTree T
  | pair a b => .pair (a.expr i) (b.expr i)

/-- The steps of assembling from a value. -/
def steps : Assembly → ℕ
  | read path => path.length
  | const T => (Expr.ofTree T : Expr ℕ).steps
  | pair a b => a.steps + (b.steps + 1)

@[simp] theorem eval_expr (A : Assembly) (i : Expr ℕ) (s : ℕ → Tree) :
    (A.expr i).eval s = A.eval (i.eval s) := by
  induction A with
  | read path => simp [expr, eval]
  | const T => simp [expr, eval]
  | pair a b iha ihb => simp [expr, eval, iha, ihb]

theorem steps_expr (A : Assembly) (v : Value) : (A.expr v.expression).steps = A.steps := by
  induction A with
  | read path => simp [expr, steps, Expr.steps_subtree]
  | const T => rfl
  | pair a b iha ihb => simp [expr, steps, iha, ihb]

/-- Assembling reads only the input and builds only parts of the result. -/
theorem maxSize_expr_le (A : Assembly) (v : Value) (s : ℕ → Tree) :
    (A.expr v.expression).maxSize s ≤ max (v.eval s).size (A.eval (v.eval s)).size := by
  induction A with
  | read path => simp [expr]
  | const T => simp [expr, eval]
  | pair a b iha ihb =>
    simp only [expr, Expr.maxSize, eval_expr, Value.eval_expression, eval, Tree.size_pair,
      max_le_iff] at iha ihb ⊢
    omega

/-- An upper bound on the nodes of an assembled tree per node of the input. -/
def weight : Assembly → ℕ
  | read _ => 1
  | const T => T.size
  | pair a b => 1 + a.weight + b.weight

/-- An assembled tree has at most `A.weight` nodes per node of the input. -/
theorem size_eval_le (A : Assembly) (t : Tree) : (A.eval t).size ≤ A.weight * t.size := by
  have ht := Tree.size_pos t
  induction A with
  | read path => simpa [eval, weight] using Tree.size_subtree_le t path
  | const T => simpa [eval, weight] using Nat.le_mul_of_pos_right T.size ht
  | pair a b iha ihb =>
    simp only [eval, Tree.size_pair, weight, Nat.add_mul, Nat.one_mul]
    omega

/-- The code of a list assembled from assemblies of its entries. -/
def list : List Assembly → Assembly
  | [] => const .nil
  | a :: as => pair a (list as)

/-- The assembly of a list builds the code of the list of the assembled entries. -/
theorem eval_list (t : Tree) (as : List Assembly) :
    (list as).eval t = ⌜as.map (·.eval t)⌝ₜ := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [list, eval, ih, encode_prod]

end Assembly

end Complexity.TreeProgram

namespace Complexity.TreeProgram.Source

open Internal (HasProgramInO)

variable {α : Type*} {β : α → Type*} [UniqueEncoding Tree α] [∀ x, UniqueEncoding Tree (β x)]

/-- A value whose code is assembled from subtrees of the input's code and constant trees, such as
a constructor of fields of the input, is built in one assignment. The assembled tree has at most
`A.weight` nodes per node of the input, so the peak is counted against the input. -/
theorem Internal.HasProgramInO.assemble {f : (x : α) → β x} (A : Assembly)
    (h : ∀ x, A.eval ⌜x⌝ₜ = ⌜f x⌝ₜ) :
    HasProgramInO f (fun v => Code.eval (A.expr v.expression)) (fun _ => 1)
      (fun x => ⌜x⌝ₜ.size) :=
  (HasProgramInO.of_implements ⟨fun _ => A.steps + 2, fun x => max ⌜x⌝ₜ.size ⌜f x⌝ₜ.size⟩
    ⟨fun v n hv => by change n ≤ n + 1 ∧ n + 1 ≤ n + 1; omega,
      fun v n s x hv hx => by
        have hs := A.maxSize_expr_le v s
        rw [hx, h] at hs
        simp only [Code.bounded_eval_iff]
        exact ⟨(Expr.assignSteps_le_steps _).trans (by rw [A.steps_expr]), hs,
          by simp [hx, h], fun j hj => by simp [Nat.ne_of_lt hj]⟩⟩).mono
    (Dominated.const _) (Dominated.of_le_mul (1 + A.weight) fun x => by
      have := A.size_eval_le ⌜x⌝ₜ
      rw [h] at this
      exact max_le (Nat.le_mul_of_pos_left _ (by omega))
        (this.trans (Nat.mul_le_mul_right _ (Nat.le_add_left _ _))))

/-- Read the subtree of the input's code at a path, such as a field of a field, whose code is a
subtree by the structures' `T.encode_field`: one step for every path. -/
theorem Internal.HasProgramInO.subtree {f : (x : α) → β x} (path : List Bool)
    (h : ∀ x, ⌜f x⌝ₜ = ⌜x⌝ₜ.subtree path) :
    HasProgramInO f (fun v => Code.eval (v.expression.subtree path)) (fun _ => 1)
      (fun x => ⌜x⌝ₜ.size) :=
  HasProgramInO.assemble (.read path) fun x => (h x).symm

/-- A closed value is written as its code in one step. -/
theorem Internal.HasProgramInO.const {γ : Type*} [UniqueEncoding Tree γ] (c : γ) :
    HasProgramInO (fun _ : α => c) (fun _ => Code.eval (.ofTree ⌜c⌝ₜ)) (fun _ => 1) (fun _ => 1) :=
  (HasProgramInO.of_implements
    ⟨fun _ => (Expr.ofTree ⌜c⌝ₜ : Expr ℕ).assignSteps, fun _ => ⌜c⌝ₜ.size⟩
    ⟨fun v n hv => by change n ≤ n + 1 ∧ n + 1 ≤ n + 1; omega,
      fun v n s x hv hx => by
        simp only [Code.bounded_eval_iff, Expr.maxSize_ofTree]
        exact ⟨le_rfl, le_rfl, by simp, fun j hj => by simp [Nat.ne_of_lt hj]⟩⟩).mono
    (Dominated.const _) (Dominated.const _)

end Complexity.TreeProgram.Source

end

public meta section

namespace Complexity.TreeProgram.Source

open Internal (HasProgramInO)

open Lean Meta in
/-- The first equation of `thms` rewriting `e` at the root only, to an encoding if `encoding` (and
to an application of `rhsHead?` if given), that `accept` takes, given the right side and the
equation. An equation whose left side applies a variable is skipped. -/
def rootEquation {α : Type} (thms : SimpTheorems) (e : Lean.Expr) (encoding : Bool)
    (accept : Lean.Expr → Lean.Expr → MetaM (Option α))
    (rhsHead? : Option Name := none) : MetaM (Option α) := do
  let candidates ← thms.post.getMatch e
  for thm in candidates.qsort (·.priority > ·.priority) do
    let value ← thm.getValue
    let (args, _, type) ← forallMetaTelescopeReducing (← inferType value)
    let some (_, l, r) := type.eq? | continue
    if encoding && !r.isAppOfArity ``UniqueEncoding.encode 4 then continue
    if let some head := rhsHead? then
      unless r.isAppOf head do continue
    let arg := if encoding || l.isAppOfArity ``UniqueEncoding.encode 4 then l.appArg! else l
    if arg.isApp && arg.getAppFn.isMVar then continue
    unless ← isDefEq l e do continue
    let r ← instantiateMVars r
    let proof ← instantiateMVars (mkAppN value args)
    if r.hasMVar || proof.hasMVar || r == e then continue
    if let some a ← accept r (← mkExpectedTypeHint proof (← mkEq e r)) then return some a
  return none

open Lean Meta in
/-- The components of a right-nested tuple. -/
partial def tupleComponents (e : Lean.Expr) : List Lean.Expr :=
  if e.isAppOfArity ``Prod.mk 4 then e.appFn!.appArg! :: tupleComponents e.appArg! else [e]

open Lean Meta in
/-- The structural encoding `⌜C a⌝ₜ = ⌜v⌝ₜ` of a constructor application, with the components of
`v` and their declared types. The equation is found for the constructor alone, its fields being
local variables, and the actual fields are substituted afterwards. -/
def constructorEncoding (body : Lean.Expr) :
    MetaM (Option (Lean.Expr × List (Lean.Expr × Lean.Expr))) := do
  let .const name _ := body.getAppFn | return none
  let some (.ctorInfo ctor) := (← getEnv).find? name | return none
  if name == ``Prod.mk then return none
  let args := body.getAppArgs
  unless args.size == ctor.numParams + ctor.numFields do return none
  let head := mkAppN body.getAppFn (args.extract 0 ctor.numParams)
  let fields := args.extract ctor.numParams args.size
  forallBoundedTelescope (← inferType head) ctor.numFields fun ys type => do
    let some inst ← synthInstance? (← mkAppM ``UniqueEncoding #[mkConst ``Tree, type]) |
      return none
    let some (r, proof) ← rootEquation (← getSimpTheorems)
        (← mkAppOptM ``encode #[mkConst ``Tree, type, inst, mkAppN head ys]) true
        fun r h => return some (r, h) |
      return none
    let substitute (e : Lean.Expr) := do return (← mkLambdaFVars ys e).beta fields
    return some (← substitute proof, ← (tupleComponents r.appArg!).mapM fun c => do
      return (← substitute c, ← substitute (← inferType c)))

open Lean Meta in
/-- The literal path a path term evaluates to. -/
private partial def literalPath? (e : Lean.Expr) : MetaM (Option (List Bool)) := do
  let e ← whnfD e
  if e.isAppOfArity ``List.nil 1 then return some []
  unless e.isAppOfArity ``List.cons 3 do return none
  let r ← whnfD e.appFn!.appArg!
  let some rest ← literalPath? e.appArg! | return none
  if r.isConstOf ``Bool.true then return some (true :: rest)
  if r.isConstOf ``Bool.false then return some (false :: rest)
  return none

open Lean Meta in
/-- The structure value `b` that `e` is a field of, with the structure's `T.encode_field` fact. -/
private def structureLink? (e : Lean.Expr) : MetaM (Option (Lean.Expr × Name)) := do
  let field (s : Name) (i : Nat) (b : Lean.Expr) := do
    let some field := (getStructureFields (← getEnv) s)[i]? | return none
    let fact := s ++ .mkSimple s!"encode_{field}"
    unless (← getEnv).contains fact do return none
    return some (b, fact)
  match e with
  | .proj s i b => field s i b
  | .app .. =>
    if let some name := e.getAppFn.constName? then
      if let some info ← getProjectionFnInfo? name then
        if !info.fromClass && e.getAppNumArgs == info.numParams + 1 then
          return ← field (← getConstInfoCtor info.ctorName).induct info.i e.appArg!
    return none
  | _ => return none

open Lean Meta in
/-- The path in the code of the input `x` to the code of `e`, a field of a field of `x`, with the
equation `⌜e⌝ₜ = code.subtree path`, where `code` is the code of `x`. Each link comes from a
structure's `T.encode_field` or a registered `source_view` subtree equation
`⌜e⌝ₜ = ⌜b⌝ₜ.subtree p` with a literal path (at most `viewFuel` steps), such as a read of a
`FinVector` at a closed index (`encode_finVector_get_apply`). -/
private partial def fieldPath? (x code e : Lean.Expr) (encoded? : Option Lean.Expr := none)
    (visited : Array Lean.Expr := #[]) (viewFuel : Nat := 8) :
    MetaM (Option (List Bool × Lean.Expr)) := do
  let e := e.consumeMData
  unless e.containsFVar x.fvarId! do return none
  if visited.contains e then return none
  let visited := visited.push e
  if e == x then
    let subtree := mkApp2 (mkConst ``Tree.subtree) code (toExpr ([] : List Bool))
    return some ([], ← mkExpectedTypeHint (← mkEqRefl code) (← mkEq code subtree))
  let extend (path : List Bool) (h hf outer lhs : Lean.Expr) (p : List Bool) :
      MetaM (Option (List Bool × Lean.Expr)) := do
    let pE := toExpr p
    let hf ← mkExpectedTypeHint hf (← mkEq lhs (mkApp2 (mkConst ``Tree.subtree) outer pE))
    if path.isEmpty then return some (p, hf)
    -- `⌜e⌝ₜ = (code.subtree path).subtree p = code.subtree (path ++ p)`
    let pathE := toExpr path
    let along ← mkCongrArg (← withLocalDeclD `t (mkConst ``Tree) fun t =>
      mkLambdaFVars #[t] (mkApp2 (mkConst ``Tree.subtree) t pE)) h
    let append ← mkEqSymm (mkApp3 (mkConst ``Tree.subtree_append) code pathE pE)
    let proof ← mkEqTrans hf (← mkEqTrans along append)
    let subtree := mkApp2 (mkConst ``Tree.subtree) code (toExpr (path ++ p))
    return some (path ++ p, ← mkExpectedTypeHint proof (← mkEq lhs subtree))
  let viaLink (b : Lean.Expr) (fact : Name) : MetaM (Option (List Bool × Lean.Expr)) := do
    let some (path, h) ← fieldPath? x code b (visited := visited) (viewFuel := viewFuel) |
      return none
    let some (_, outer, _) := (← inferType h).eq? | return none
    let factConst ← mkConstWithFreshMVarLevels fact
    let (args, _, type) ← forallMetaTelescopeReducing (← inferType factConst)
    let some (_, _, rhs) := type.eq? | return none
    let some value := args.back? | return none
    unless ← isDefEq value b <&&> isDefEq rhs.appFn!.appArg! outer do return none
    for arg in args do
      unless ← arg.mvarId!.isAssigned do
        arg.mvarId!.assign (← synthInstance (← inferType arg))
    let hf ← instantiateMVars (mkAppN factConst args)
    let some (_, lhs, rhs) := (← inferType hf).eq? | return none
    let some p ← literalPath? rhs.appArg! | return none
    extend path h hf outer lhs p
  if let some (b, fact) ← structureLink? e then
    if let some res ← viaLink b fact then return some res
  if viewFuel > 0 then
    if let some ext ← getSimpExtension? `source_view then
      let encoded? ← match encoded? with
        | some enc => pure (some enc)
        | none => observing? (mkAppM ``encode #[mkConst ``Tree, e])
      if let some encoded := encoded? then
        let res ← rootEquation (← ext.getTheorems) encoded false (rhsHead? := some ``Tree.subtree)
          fun r hf => do
            unless r.isAppOfArity ``Tree.subtree 2 do return none
            let outer := r.appFn!.appArg!
            unless outer.isAppOfArity ``UniqueEncoding.encode 4 do return none
            let b := outer.appArg!
            let some p ← literalPath? r.appArg! | return none
            let some (path, h) ← fieldPath? x code b (encoded? := some outer) (visited := visited)
                (viewFuel := viewFuel - 1) |
              return none
            let some (_, outerH, _) := (← inferType h).eq? | return none
            unless ← isDefEq outer outerH do return none
            extend path h hf outerH encoded p
        if res.isSome then return res
  return none

open Lean Meta in
/-- The value of a source function at its input, which may itself be a function. -/
private def atInput {γ : Type} (f : Lean.Expr) (k : Lean.Expr → Lean.Expr → MetaM γ) :
    MetaM γ := do
  if f.isLambda then lambdaBoundedTelescope f 1 fun xs body => k xs[0]! body
  else withLocalDeclD `x (← whnf (← inferType f)).bindingDomain! fun x => k x (mkApp f x)

open Lean Meta Mathlib.Meta.FunProp in
/-- A field of a field of the input is read as the subtree at its path (`HasProgramInO.subtree`). -/
def fieldRule (goal : Lean.Expr) : MetaM (Option Result) := do
  let #[α, β, instα, instβ, f, _, _, _] := goal.getAppArgs | return none
  atInput f fun x body => do
    let code ← mkAppOptM ``encode #[mkConst ``Tree, α, instα, x]
    let body := body.headBeta.consumeMData
    -- The code of a field, as a tree, has the field's code.
    let (body, encoded?) ←
      if body.isAppOfArity ``UniqueEncoding.encode 4 then
        pure (body.appArg!, some body)
      else
        let ty := β.beta #[x]
        let inst := instβ.beta #[x]
        if !ty.hasMVar && !inst.hasMVar then
          pure (body, some (← mkAppOptM ``encode #[mkConst ``Tree, ty, inst, body]))
        else
          pure (body, none)
    let some (path, h) ← fieldPath? x code body (encoded? := encoded?) | return none
    -- The input itself is not a read.
    if path.isEmpty then return none
    return some ⟨← mkAppOptM ``HasProgramInO.subtree
      #[α, β, instα, instβ, f, toExpr path, ← mkLambdaFVars #[x] h]⟩

open Lean Meta Mathlib.Meta.FunProp in
/-- A closed value is written as its code (`HasProgramInO.const`), without computing it. A
constructor whose code is the empty tree is computed by no step, like `()`, also when it mentions
types and instances, such as `([] : List α)`; only its code's root is reduced. -/
def closedRule (goal : Lean.Expr) : MetaM (Option Result) := do
  let #[α, β, instα, instβ, f, _, _, _] := goal.getAppArgs | return none
  atInput f fun x body => do
    let body := body.headBeta
    if body.hasMVar then return none
    -- Types and instances are not data. A code mentioning them is not written by a program,
    -- which is the same at every type.
    let data ← (Lean.collectFVars {} body).fvarIds.anyM fun v => do
      let type ← whnf (← v.getType)
      return !type.isSort && (← isClass? type).isNone
    if data then return none
    -- A speculative rule may leave the type and the encoder to be found.
    unless ← isDefEq (β.beta #[x]) (← inferType body) do return none
    let type ← instantiateMVars (β.beta #[x])
    let inst ← instantiateMVars (instβ.beta #[x])
    if type.containsFVar x.fvarId! || inst.containsFVar x.fvarId! then return none
    if inst.hasMVar then
      unless ← isDefEq inst (← synthInstance (← mkAppM ``UniqueEncoding #[mkConst ``Tree, type]))
        do return none
    let inst ← instantiateMVars inst
    let code ← mkAppOptM ``encode #[mkConst ``Tree, type, inst, body]
    if ← isConstructorApp (← whnfR body) then
      if (← whnfD code).isAppOf ``BinaryTree.nil then
        let unit ← mkAppOptM ``HasProgramInO.unit #[α, instα]
        let empty ← mkExpectedTypeHint (← mkEqRefl code)
          (← mkEq code (← mkAppM ``encode #[mkConst ``Tree, mkConst ``Unit.unit]))
        return some ⟨← mkAppM ``HasProgramInO.of_encode #[← mkLambdaFVars #[x] empty, unit]⟩
    if body.hasFVar then return none
    return some ⟨← mkAppOptM ``HasProgramInO.const #[α, instα, type, inst, body]⟩

open Lean Meta Mathlib.Meta.FunProp in
/-- Whether a function has a selected implementation: a registered one, or a local hypothesis. -/
private def hasSelectedImplementation (name : Name) : MetaM Bool := do
  unless (← getTheoremsForFunction name ``HasProgramInO).isEmpty do return true
  (← getLCtx).anyM fun decl => do
    if decl.isImplementationDetail then return false
    let type ← instantiateMVars decl.type
    unless type.isAppOfArity ``HasProgramInO 8 do return false
    lambdaTelescope (type.getArg! 4) fun _ body => return body.getAppFn.isConstOf name

open Lean Meta in
/-- An assembly of the code of `e` from the code `code` of the input `x`, with the equation
`A.eval code = ⌜e⌝ₜ`: a field of a field of the input is read, a closed value is a constant, a
constructor assembles its fields by its encoding equation, and a value with a registered
`source_view` code equation `⌜e⌝ₜ = ⌜w⌝ₜ` is assembled through `w`. A definition whose value is a
constructor is unfolded at the `root`, where its selected implementations have been tried, and
inside only if it has none; otherwise the search computes it by them. -/
private partial def assembly? (x code e : Lean.Expr) (root := false)
    (encoded? : Option Lean.Expr := none) (visited : Array Lean.Expr := #[])
    (viewFuel : Nat := 8) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
  let e := e.consumeMData
  if visited.contains e then return none
  let visited := visited.push e
  let encoded ← match encoded? with
    | some enc => pure enc
    | none => mkAppM ``encode #[mkConst ``Tree, e]
  let stated (A proof : Lean.Expr) := do
    return some (A, ← mkExpectedTypeHint proof
      (← mkEq (mkApp2 (mkConst ``Assembly.eval) code A) encoded))
  if !e.hasFVar && !e.hasMVar then
    let A := mkApp (mkConst ``Assembly.const) encoded
    return ← stated A (← mkEqRefl encoded)
  if let some (path, h) ← fieldPath? x code e (encoded? := some encoded) then
    return ← stated (mkApp (mkConst ``Assembly.read) (toExpr path)) (← mkEqSymm h)
  if e.isAppOfArity ``Prod.mk 4 then
    let some (A₁, h₁) ← assembly? x code e.appFn!.appArg! (visited := visited)
        (viewFuel := viewFuel) | return none
    let some (A₂, h₂) ← assembly? x code e.appArg! (visited := visited)
        (viewFuel := viewFuel) | return none
    return ← stated (mkApp2 (mkConst ``Assembly.pair) A₁ A₂)
      (← mkCongr (← mkCongrArg (mkConst ``Tree.pair) h₁) h₂)
  if let some (proof, _) ← constructorEncoding e then
    let some (_, _, tuple) := (← inferType proof).eq? | return none
    let some (A, h) ← assembly? x code tuple.appArg! (encoded? := some tuple)
        (visited := visited) (viewFuel := viewFuel) | return none
    return ← stated A (← mkEqTrans h (← mkEqSymm proof))
  if !root then
    let some name := e.getAppFn.constName? | return none
    if ← hasSelectedImplementation name then return none
  if viewFuel > 0 then
    if let some ext ← getSimpExtension? `source_view then
      let res ← rootEquation (← ext.getTheorems) encoded true fun r h => do
        let w := r.appArg!
        let isWrapper := (w.isApp && w.appArg! == e) ||
          match w with | .proj _ _ b => b == e | _ => false
        if isWrapper then return none
        let some (A, hw) ← assembly? x code w (encoded? := some r) (visited := visited)
            (viewFuel := viewFuel - 1) | return none
        stated A (← mkEqTrans hw (← mkEqSymm h))
      if res.isSome then return res
  -- A definition whose value is a constructor application is unfolded once, as by
  -- `constructorRule`.
  let some value ← withTransparency .default <| unfoldDefinition? e | return none
  let value := value.headBeta
  unless ← isConstructorApp value do return none
  let some (A, h) ← assembly? x code value (visited := visited) (viewFuel := viewFuel) | return none
  stated A h

open Lean Meta Mathlib.Meta.FunProp in
/-- A constructor of values at hand is built in one step by its assembly (`HasProgramInO.assemble`),
found on the source's form `source` and stated on the requested function. -/
def assembleRule (goal source : Lean.Expr) : MetaM (Option Result) := do
  let #[α, β, instα, instβ, f, _, _, _] := goal.getAppArgs | return none
  atInput source fun x body => do
    let code ← mkAppOptM ``encode #[mkConst ``Tree, α, instα, x]
    let some (A, h) ← assembly? x code body.headBeta (root := true) | return none
    return some ⟨← mkAppOptM ``HasProgramInO.assemble
      #[α, β, instα, instβ, f, A, ← mkLambdaFVars #[x] h]⟩

end Complexity.TreeProgram.Source
