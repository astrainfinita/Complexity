/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Asymptotics.Nat
public import Complexity.Tactic.Dominated.Pointwise

/-! # Closing growth comparisons

`dominated` proves `Dominated f g` when both sides are given, as left by `source_fun_prop` and
`model_fun_prop`, whose default discharger it is, and `IsPoly s f`, that `f` is polynomial in the
measure `s`. It never changes either side, and leaves the summands it cannot prove as goals. Every
comparison is settled once per call. Both goals go through the same steps (`Target`); they differ in
what splits without loss and in how parts combine: by degrees against a given right side, and by
the closure rules of `IsPoly`, with no degree.

## Splitting

The left side is normalized with `@[dominated_simp]`, and its sums and maxima are split; on an
`IsPoly` goal also its products, constant powers and constants, which `IsPoly` splits without loss
(but for a factor that can vanish). A difference is compared as stated when it is the target or a
fact, and through its minuend otherwise. Each summand is tried in turn through a `Dominated`
hypothesis, a genuine property of the source function matched reducibly, and on an `IsPoly` goal
also a polynomial growth `IsPoly r T` applied in it; entry by entry by a rule registered with
`@[dominated_traversal]`, such as for maxima over lists and sums over tables; by the pointwise
step, against `g` or `s + 1`; and, against a power of degree at least 2 on the right or on an
`IsPoly` goal, by cases on an `if`, and for its products and powers or, on an `IsPoly` goal,
through an upper bound polynomial in turn (`viaBound`).

## The pointwise step

The pointwise step destructures the input, splits the source cases, expands encoded sizes with
`@[dominated_expand]` and the definitions of the list, adds size facts and closes each case with
`omega`; the coefficient is the hidden witness `2 ^ 40`. The size facts are the statements
`a ≤ b`, `a < b` or `a = b` of the list and those registered with `@[dominated]`, instantiated at
the terms they are about (their left side, or their right side when the left side is a variable or
a literal), the terms of their other side being looked at in the next round, and the statements
registered with `@[dominated_forward]`, instantiated at matching hypotheses. Like `omega`, it reads
the other hypotheses without changing them. Products and powers are atoms there.

## Products and powers

A summand that the pointwise step cannot prove is proved by degree synthesis against a base `S`
taken from the powers of the right side: every subterm `t` of the left side gets a degree `d` with
`Dominated (fun x => t) (fun x => S x ^ d)`, sums and maxima taking the larger degree, products
adding and powers multiplying the degrees, and `Dominated (fun x => S x ^ e) g` closes it when
`d ≤ e`. The constants stay hidden in `Dominated`, so nested products and powers need no
coefficient, and `Dominated` hypotheses give degrees of any size. An atom has degree 1 when it is
linearly within a multiple of `S`, and otherwise the degree of an upper bound of it.

Splitting sums and maxima loses nothing, but splitting a product, a power or a difference loses what
is known about it as a whole, such as `x * y ≤ z` or `x ^ 2 ≤ y`. So when the rules alone fail, a
second pass also bounds products, powers and differences as atoms are, and keeps the lower degree.
An `if` whose condition depends only on the input is split losslessly by cases on the condition,
which each part has as the property of its subtype input. A `match` on a pattern binds variables
that degree synthesis cannot see: such a summand is still compared pointwise, with facts about the
products and powers it depends on (`addPowerFacts`), a provisional treatment (plan W2); on an
`IsPoly` goal it is compared pointwise only. See `degree`, `viaDegree` and `viaCases`.
-/

public meta section

open Lean Meta Elab Tactic

namespace Complexity.Tactic.Dominated

/-! ### The solver

`dominated` follows the structure of `positivity` and `fun_prop`: a recursive function builds
proof terms, with the facts of the call in a reader context and the settled comparisons in a
cache. The pointwise step `sizeOmega` plays the part of a discharger. -/

/-- A simp context built when first used, once per call: building one costs about as much as a
small comparison, and many calls need only some of them. A simp context holds no metavariables, so
one built on a branch that is later backtracked stays valid. -/
structure LazySimp where
  /-- The context, once built. -/
  ref : IO.Ref (Option Simp.Context)
  /-- How to build it. -/
  build : MetaM Simp.Context

/-- A simp context to build on first use. -/
def LazySimp.new (build : MetaM Simp.Context) : MetaM LazySimp :=
  return { ref := ← IO.mkRef none, build }

/-- The simp context, built on first use. -/
def LazySimp.get (l : LazySimp) : MetaM Simp.Context := do
  if let some c ← l.ref.get then return c
  let c ← l.build
  l.ref.set (some c)
  return c

/-- The facts and the list of one `dominated` call. -/
structure Context where
  /-- Statements `a ≤ b`, `a < b` or `a = b` to instantiate at matching terms in the pointwise
  step, by the term each is about: those given and those registered with `@[dominated]`. -/
  statements : DiscrTree Lean.Expr
  /-- Statements registered with `@[dominated_forward]`, by their premise. -/
  premises : DiscrTree Lean.Expr
  /-- `Dominated` facts with their types, compositions unfolded. -/
  facts : Array (Lean.Expr × Lean.Expr)
  /-- Expansion of encoded sizes on the left side. -/
  sizes : LazySimp
  /-- The same, also distributing the table length over an entry. -/
  sizesMul : LazySimp
  /-- Expansion of encoded sizes in the pointwise step, unfolding the definitions of the list. -/
  expand : LazySimp
  /-- The normalization of `sizes`, also unfolding the definitions of the list: degree synthesis
  reads atoms and the right side with it, without rewriting the goals left to the user. -/
  sizesUnfold : LazySimp
  /-- Numeral arithmetic used with `expand`, so that exponents such as `2 * 3` become literals. -/
  numerals : Simp.SimprocsArray
  /-- Polynomial growths `IsPoly r T` among the hypotheses, read on `IsPoly` goals only: their
  degree is unknown, so no given exponent can be compared with it. -/
  polyFacts : Array Lean.Expr := #[]
  /-- Statements concluding `IsPoly r T`, registered with `@[dominated]` or in the list, by the
  part `T a` each is about; read on `IsPoly` goals only. -/
  polyLemmas : DiscrTree Lean.Expr := {}
  /-- The rules registered with `@[dominated_traversal]`. -/
  traversalRules : TraversalRules

/-- Comparisons settled during one call, and the summands left to the user. -/
structure State where
  /-- Settled `Dominated` goals and positivity propositions: a proof, or `none` for a failure. -/
  cache : Std.HashMap Lean.Expr (Option Lean.Expr) := {}
  /-- Summands left as goals, by type. -/
  left : Array (Lean.Expr × MVarId) := #[]
  /-- Whether the pointwise step adds the facts about products and powers, as for a `match` on a
  pattern (`viaPowerFacts`). -/
  nonlinear : Bool := false

/-- The solver monad: one context and one cache per `dominated` call. -/
abbrev DominatedM := ReaderT Context (StateRefT State TacticM)

/-- Unfold the type abbreviations in `e`, such as `CNF ℕ` to `List (CNF.Clause ℕ)`. -/
partial def unfoldTypeAbbrevs (env : Environment) (e : Lean.Expr) : Lean.Expr :=
  e.replace fun t => do
    let .const c us := t.getAppFn | none
    let some (.defnInfo info) := env.find? c | none
    unless getReducibilityStatusCore env c matches .reducible do none
    unless info.type.getForallBody.isSort do none
    some (unfoldTypeAbbrevs env ((info.value.instantiateLevelParams info.levelParams us).beta
      t.getAppArgs))

/-- Settle `p` once per call, up to type abbreviations: a lemma about an underlying type, such as
one about `List α` used at `CNF ℕ`, reaches the same comparisons. A proof that still has
metavariables is not kept, since a later backtracking step could unassign them. -/
def memo (p : Lean.Expr) (k : DominatedM (Option Lean.Expr)) : DominatedM (Option Lean.Expr) := do
  let p ← instantiateMVars p
  let key := unfoldTypeAbbrevs (← getEnv) p
  -- The proof is stated at `p`, so assembling proofs never rechecks definitional equality.
  if let some r := (← get).cache[key]? then
    -- A failure settled without the facts about products and powers is tried again with them.
    if r.isSome || !(← get).nonlinear then return ← r.mapM (mkExpectedTypeHint · p)
  let r ← match ← k with
    | some proof => pure (some (← mkExpectedTypeHint (← instantiateMVars proof) p))
    | none => pure none
  unless r.any (·.hasMVar) do modify fun s => { s with cache := s.cache.insert key r }
  return r

/-- Run a rule; an exception counts as a failure and leaves no trace. -/
def attempt (k : DominatedM (Option Lean.Expr)) : DominatedM (Option Lean.Expr) := do
  let saved ← show TacticM _ from saveState
  try k catch _ =>
    saved.restore
    return none

/-- Run `tac` on `goal`; keep its assignments only if it closes the goal. -/
def closes (goal : MVarId) (tac : TacticM Unit) : TacticM Bool := do
  let saved ← saveState
  let goals ← getGoals
  try
    setGoals [goal]
    tac
    if (← getGoals).isEmpty then
      setGoals goals
      return true
  catch _ => pure ()
  saved.restore
  return false

/-- Prove `type` by applying `rule` reducibly and settling each new goal with `prove`. -/
def viaRule (rule : Name) (type : Lean.Expr)
    (prove : Lean.Expr → DominatedM (Option Lean.Expr)) : DominatedM (Option Lean.Expr) :=
  attempt do
    let goal ← mkFreshExprSyntheticOpaqueMVar type
    for sub in ← withReducible (goal.mvarId!.apply (← mkConstWithFreshMVarLevels rule)) do
      let some proof ← prove (← instantiateMVars (← sub.getType)) | throwError "no proof"
      sub.assign proof
    return some (← instantiateMVars goal)

/-- The domain of a function. -/
def domainOf (f : Lean.Expr) : MetaM Lean.Expr := do
  return (← whnf (← inferType f)).bindingDomain!

/-- `e` without metadata. -/
partial def eraseMData (e : Lean.Expr) : Lean.Expr :=
  e.replace fun | .mdata _ b => some (eraseMData b) | _ => none

/-- Close one case of the pointwise step by `omega` with the size facts, and the facts about
products and powers when `nonlinear`, expanding the encoded sizes that splitting has exposed. -/
def closeCase (outer : FVarIdSet) (goal : MVarId) : DominatedM Bool := do
  let nonlinear := (← get).nonlinear
  let ctx ← read
  -- `omega` takes a term under metadata, as the alternatives of a `match` carry, for an atom.
  let goal ← goal.replaceTargetDefEq (eraseMData (← instantiateMVars (← goal.getType)))
  closes goal do
    let some g ← simpOwn outer (← ctx.expand.get)
        (← addSizeFacts outer ctx.statements ctx.premises goal) ctx.numerals
      | setGoals []
    setGoals [← if nonlinear then addPowerFacts g else pure g]
    Omega.omegaDefault

/-- The pointwise step: prove `goal : ∀ x, p x` by destructuring `x`, splitting its cases,
expanding encoded sizes and closing each case with `closeCase`. -/
def sizeOmega (goal : MVarId) : DominatedM Bool := do
  let ctx ← read
  let outer ← goal.withContext do return (← getLCtx).foldl (·.insert ·.fvarId) {}
  let plain ← simpContext #[]
  let ids ← simpContext #[] #[``id]
  let (_, goal) ← goal.intro1
  let mut goals := #[]
  for g in ← destructure outer goal do
    if let some g ← dsimpOwn plain g then goals := goals ++ (← splitAll g)
  for g in goals do
    let some g ← encodeFields outer g | continue
    for g in ← casesEquations outer g do
      let some g ← dsimpOwn ids g outer | continue
      let some g ← simpOwn outer (← ctx.expand.get) (← normalizeEncodings outer g) ctx.numerals
        | continue
      let some g ← encodeFields outer g | continue
      for g in ← splitAll (← normalizeEncodings outer g) do
        unless ← closeCase outer g do return false
  return true

/-- Prove `∀ x, p x` with `sizeOmega`, where `p x` relates `f x` and `g x`. -/
def bySizeOmega (f : Lean.Expr) (p : Lean.Expr → MetaM Lean.Expr) :
    DominatedM (Option Lean.Expr) := do
  let type ← withLocalDeclD `x (← domainOf f) fun x => do mkForallFVars #[x] (← p x)
  let h ← mkFreshExprSyntheticOpaqueMVar type
  let saved ← show TacticM _ from saveState
  try
    if ← sizeOmega h.mvarId! then return some h
  catch _ => pure ()
  saved.restore
  return none

/-- `Dominated f g` pointwise, with the hidden coefficient `2 ^ 40`. -/
def pointwise (f g : Lean.Expr) : DominatedM (Option Lean.Expr) := do
  let C := mkNatLit 1099511627776
  let some h ← bySizeOmega f fun x => do
      mkAppM ``LE.le #[(mkApp f x).headBeta, ← mkAppM ``HMul.hMul #[C, (mkApp g x).headBeta]]
    | return none
  return some (← mkAppM ``Dominated.of_le_mul #[C, h])

/-- `0 < e` read off its form: a code size, a positive literal, or a sum with a positive part. -/
private partial def positiveByForm? (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  if e.isAppOfArity ``Tree.size 1 then return some (← mkAppM ``Tree.size_pos #[e.appArg!])
  if let some n := e.nat? then
    if n > 0 then return some (← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit 0, e]))
  if e.isAppOfArity ``HAdd.hAdd 6 then
    let a := e.getAppArgs[4]!
    let b := e.appArg!
    if let some h ← positiveByForm? b then
      return some (← mkAppM ``Nat.lt_of_lt_of_le #[h, ← mkAppM ``Nat.le_add_left #[b, a]])
    if let some h ← positiveByForm? a then
      return some (← mkAppM ``Nat.lt_of_lt_of_le #[h, ← mkAppM ``Nat.le_add_right #[a, b]])
  return none

/-- `∀ x, 0 < g x`, from a hypothesis, read off its form, or pointwise. -/
def positive (g : Lean.Expr) : DominatedM (Option Lean.Expr) := do
  let p ← withLocalDeclD `x (← domainOf g) fun x => do
    mkForallFVars #[x] (← mkAppM ``LT.lt #[mkNatLit 0, (mkApp g x).headBeta])
  memo p do
    for decl in ← getLCtx do
      if !decl.isImplementationDetail && (← withReducible (isDefEq decl.type p)) then
        return some decl.toExpr
    let direct ← withLocalDeclD `x (← domainOf g) fun x => do
      let some h ← positiveByForm? (mkApp g x).headBeta | return none
      return some (← mkLambdaFVars #[x] h)
    if direct.isSome then return direct
    bySizeOmega g fun x => mkAppM ``LT.lt #[mkNatLit 0, (mkApp g x).headBeta]

/-- `Dominated f g` without facts: the target itself, a constant, or a pointwise bound. A
constant is recognized syntactically, after the left side is normalized: recognizing one by
unfolding definitions would leave a costly definitional equality in the proof. -/
def proveBase (f g : Lean.Expr) : DominatedM (Option Lean.Expr) := do
  if ← withReducible (isDefEq f g) then return some (← mkAppM ``Dominated.refl #[g])
  if let .lam _ _ body _ := f then
    if !body.hasLooseBVars then
      if let some h ← positive g then
        return some (← mkAppM ``Dominated.const_of_pos #[body, h])
  pointwise f g

/-- The structures whose projections occur in `es`. Degree synthesis reads the size of such a
structure as the size of its fields, and of no other structure. -/
def projectedIn (es : Array Lean.Expr) : MetaM (Std.HashSet Lean.Expr) := do
  let env ← getEnv
  let (_, s) ← (es.forM fun e => e.forEach' fun t => do
      if let .proj _ _ b := t then modify (·.insert b)
      if let some n := t.getAppFn.constName? then
        if let some info := env.getProjectionFnInfo? n then
          if t.getAppNumArgs == info.numParams + 1 then modify (·.insert t.appArg!)
      return true : StateT (Std.HashSet Lean.Expr) MetaM Unit).run {}
  return s

/-- `⌜y⌝ₜ.size` with `y` replaced by its constructor applied to its projections, when `y`
has a structure type and is not a constructor application. Equal by structure eta. -/
def etaSize? (t : Lean.Expr) : MetaM (Option Lean.Expr) := do
  unless t.isAppOfArity ``Tree.size 1 do return none
  let e := t.appArg!
  unless e.isAppOfArity ``UniqueEncoding.encode 4 do return none
  let y := e.appArg!
  let ty ← whnfR (← inferType y)
  let .const name us := ty.getAppFn | return none
  let env ← getEnv
  let some info := getStructureInfo? env name | return none
  let ctor := getStructureCtor env name
  if (← whnfR y).getAppFn.isConstOf ctor.name then return none
  let projs ← info.fieldNames.mapM fun f => mkProjection y f
  let y' := mkAppN (mkConst ctor.name us) (ty.getAppArgs ++ projs)
  return some (mkApp t.appFn! (mkApp e.appFn! y'))

/-- `t ≤ u` with its proof, from a comparison `h` whose left side has `t` in its linear form, unless
`u` contains `t`. -/
def upperBound (t h : Lean.Expr) : TacticM (Option (Lean.Expr × Lean.Expr)) := do
  let ty ← whnfR (← instantiateMVars (← inferType h))
  unless ty.getAppNumArgs > 0 && ty.getAppArgs[0]!.isConstOf ``Nat do return none
  let le ← if ty.isAppOfArity ``LE.le 4 then pure h
    else if ty.isAppOfArity ``LT.lt 4 then mkAppM ``Nat.le_of_lt #[h]
    else if ty.isAppOfArity ``Eq 3 then mkAppM ``Nat.le_of_eq #[h]
    else return none
  let leTy ← whnfR (← inferType le)
  let (l, u) := (leTy.appFn!.appArg!, leTy.appArg!)
  if (u.find? (· == t)).isSome then return none
  if ← withReducible (isDefEq l t) then return some (u, le)
  unless (linearForm l).2.any (·.1 == t) do return none
  let some h' ← omegaAbstracted (← mkAppM ``LE.le #[t, u]) #[(leTy, le)] | return none
  return some (u, h')

/-- On the inputs where the condition `p` holds (or fails, when not `holds`), the left side `f`
with the `if`s on `p` settled: `fun y => f y.1` and an equation to it. -/
def settleCases (f p : Lean.Expr) (holds : Bool) : MetaM (Lean.Expr × Lean.Expr) := do
  let α ← domainOf f
  let pred ← if holds then pure p else withLocalDeclD `x α fun x => do
    mkLambdaFVars #[x] (mkNot (mkApp p x).headBeta)
  withLocalDeclD `y (← mkAppM ``Subtype #[pred]) fun y => do
    let val ← mkAppM ``Subtype.val #[y]
    let hy ← mkAppM ``Subtype.property #[y]
    let c := (mkApp p val).headBeta
    let body := (mkApp f val).headBeta
    let mut cur := body
    let mut eq ← mkEqRefl body
    -- Settle the `if`s on the condition, one at a time.
    repeat
      let some t := cur.find? fun t => (t.isAppOfArity ``ite 5 || t.isAppOfArity ``dite 5) &&
          t.getAppArgs[1]! == c | break
      let args := t.getAppArgs
      let rule := if t.isAppOfArity ``ite 5 then
          (if holds then ``ite_eq_left else ``ite_eq_right)
        else (if holds then ``dite_eq_left else ``dite_eq_right)
      let h ← mkAppOptM rule #[c, args[2]!, hy, args[0]!, args[3]!, args[4]!]
      let abst ← kabstract cur t
      let motive := Lean.mkLambda `z .default args[0]! abst
      eq ← mkEqTrans eq (← mkCongrArg motive h)
      cur := abst.instantiate1 (← inferType h).appArg!
    return (← mkLambdaFVars #[y] cur, ← mkFunExt (← mkLambdaFVars #[y] eq))

/-- The comparisons about the term `t`, with `x` standing for the input: the conjuncts of the
property of a subtype input, and the given and registered statements instantiated at `t`. -/
partial def comparisonsAbout (x t : Lean.Expr) : DominatedM (Array Lean.Expr) := do
  let mut out := #[]
  let ty ← whnfR (← inferType x)
  if ty.isAppOfArity ``Subtype 2 then
    let rec conjuncts (h : Lean.Expr) (p : Lean.Expr) (fuel : Nat) : MetaM (Array Lean.Expr) := do
      if fuel == 0 then return #[]
      let p ← whnfR p
      if p.isAppOfArity ``And 2 then
        return (← conjuncts (← mkAppM ``And.left #[h]) p.appFn!.appArg! (fuel - 1)) ++
          (← conjuncts (← mkAppM ``And.right #[h]) p.appArg! (fuel - 1))
      return #[h]
    let hx ← mkAppM ``Subtype.property #[x]
    out := out ++ (← conjuncts hx (← inferType hx) 4)
  for l in ← (← read).statements.getMatch t do
    let some (h, _) ← instanceAt l t | continue
    out := out.push h
  return out

/-- The size `t` of a structure in `projected`, one whose projections occur, read through the sizes
of its fields: the sizes and the equation to them. -/
def fieldSizes? (projected : Std.HashSet Lean.Expr) (t : Lean.Expr) :
    DominatedM (Option (Lean.Expr × Lean.Expr)) := do
  let some t' ← etaSize? t | return none
  unless projected.contains t.appArg!.appArg! do return none
  let (r, _) ← simp t' (← (← read).expand.get)
  if r.expr == t' then return none
  return some (r.expr,
    ← mkEqTrans (← mkExpectedTypeHint (← mkEqRefl t) (← mkEq t t')) (← r.getProof))

/-- `Dominated (fun x => t) (fun x => S x ^ d)` for a degree `d` read off the structure of `t`, with
`x` standing for the input and `hS` the positivity of `S`. Literals have degree 0; sums and maxima
take the larger degree of their parts, products add and powers multiply them (the exponent is
evaluated), and a difference takes the degree of its minuend. Any other term is an atom, bounded as
a whole by `bound`:
* with degree 1 when it is within a multiple of `S`: read off when it is an atom of the linear form
  of `S`, and otherwise by the pointwise step, run in `outer`, the context without `x`, so that its
  auxiliary proofs do not capture `x`;
* otherwise with the degree of an upper bound: a `Dominated` hypothesis about it, or `t ≤ u` from
  a comparison whose left side has `t` in its linear form, `u` not containing `t`, among the
  conjuncts of the property of a subtype input and the statements instantiated at `t`;
* an atom also through the definitions of the list, and the size of a structure in `projected`
  through the sizes of its fields.

Splitting a product, a power or a difference loses what is known about it as a whole, such as
`x * y ≤ z` or `x ^ 2 ≤ y`. In the `thorough` pass these are also bounded as atoms are, first, and
the lower degree is kept; degree 1 is the least for a term with an atom, so the parts are then not
read. That pass also tries every upper bound instead of the first one. The degree found is not
always the least: degrees are integers, and one base is used throughout. -/
partial def degree (outer : LocalContext × LocalInstances) (projected : Std.HashSet Lean.Expr)
    (thorough : Bool) (x S hS t : Lean.Expr) :
    DominatedM (Option (Nat × Lean.Expr)) := do
  -- Pointwise comparisons run without `x` in scope, so their auxiliary proofs do not capture it.
  let outside {β : Type} (k : DominatedM β) : DominatedM β := withLCtx outer.1 outer.2 k
  let Sx := (mkApp S x).headBeta
  let fn (e : Lean.Expr) : MetaM Lean.Expr := mkLambdaFVars #[x] e
  let powFn (d : Nat) : MetaM Lean.Expr := do fn (← mkAppM ``HPow.hPow #[Sx, mkNatLit d])
  let lift (p : Lean.Expr) (d e : Nat) : MetaM Lean.Expr := do
    if d == e then return p
    mkAppM ``Dominated.mono_pow
      #[p, ← mkDecideProof (← mkAppM ``LE.le #[mkNatLit d, mkNatLit e]), hS]
  let hinted (p : Lean.Expr) (t : Lean.Expr) (d : Nat) : MetaM Lean.Expr := do
    mkExpectedTypeHint p (← mkAppM ``Dominated #[← fn t, ← powFn d])
  let lower (a b : Option (Nat × Lean.Expr)) : Option (Nat × Lean.Expr) :=
    match a, b with
    | some (d, p), some (e, q) => if e < d then some (e, q) else some (d, p)
    | some r, none => some r
    | none, r => r
  let sub := degree outer projected thorough x S hS
  if t.nat?.isSome then
    let hpos ← fn (← mkAppOptM ``Nat.pow_pos #[none, mkNatLit 0, mkApp hS x])
    return some (0, ← mkAppM ``Dominated.const_of_pos #[t, hpos])
  let two (a b : Lean.Expr) := do
    let some (da, pa) ← sub a | return none
    let some (db, pb) ← sub b | return none
    return some (da, pa, db, pb)
  if t.isAppOfArity ``HAdd.hAdd 6 || t.isAppOfArity ``Max.max 4 then
    let (a, b) := if t.isAppOfArity ``HAdd.hAdd 6 then (t.getAppArgs[4]!, t.appArg!)
      else (t.appFn!.appArg!, t.appArg!)
    let some (da, pa, db, pb) ← two a b | return none
    let d := max da db
    let rule := if t.isAppOfArity ``HAdd.hAdd 6 then ``Dominated.add_same else ``Dominated.max_same
    return some (d, ← hinted (← mkAppM rule #[← lift pa da d, ← lift pb db d]) t d)
  -- `t` bounded as a whole: degree 1 by a linear comparison, or the degree of an upper bound.
  let bound (atomic : Bool) : DominatedM (Option (Nat × Lean.Expr)) := do
    let atom ← fn t
    -- An atom of the base's linear form has degree 1, read off without the pointwise step.
    if let some k := termwiseCoefficient t Sx then
      if let some h ← omegaAbstracted
          (← mkAppM ``LE.le #[t, ← mkAppM ``HMul.hMul #[mkNatLit k, Sx]])
          #[(← mkAppM ``LT.lt #[mkNatLit 0, Sx], mkApp hS x)] then
        let p ← mkAppM ``Dominated.of_le_mul #[mkNatLit k, ← fn h]
        return some (1, ← hinted (← mkAppM ``Dominated.le_pow #[p, ← mkDecideProof
          (← mkAppM ``LT.lt #[mkNatLit 0, mkNatLit 1])]) t 1)
    -- Otherwise degree 1 by a pointwise linear comparison.
    if let some p ← outside (memo (← mkAppM ``Dominated #[atom, S]) (attempt (proveBase atom S)))
    then
      return some (1, ← hinted (← mkAppM ``Dominated.le_pow #[p, ← mkDecideProof
        (← mkAppM ``LT.lt #[mkNatLit 0, mkNatLit 1])]) t 1)
    let mut best : Option (Nat × Lean.Expr) := none
    -- A `Dominated` hypothesis about the term, of some degree.
    for (h, type) in (← read).facts do
      unless ← withReducible (isDefEq type.appFn!.appArg! atom) do continue
      let some (d, po) ← sub (mkApp type.appArg! x).headBeta | continue
      best := lower best (some (d, ← hinted (← mkAppM ``Dominated.trans #[h, po]) t d))
      unless thorough do return best
    -- An upper bound from a comparison, of some degree.
    for h in ← comparisonsAbout x t do
      let some (u, le) ← upperBound t h | continue
      let some (d, po) ← sub u | continue
      let p ← mkAppM ``Dominated.trans #[← mkAppM ``Dominated.of_le #[← fn le], po]
      best := lower best (some (d, ← hinted p t d))
      unless thorough do return best
    -- An atom read through the definitions of the list.
    if atomic then
      let (r, _) ← simp t (← (← read).sizesUnfold.get)
      if r.expr != t then
        let eq ← r.getProof
        if let some (d, po) ← sub r.expr then
          let p ← mkAppM ``Dominated.trans
            #[← mkAppM ``Dominated.of_le #[← fn (← mkAppM ``Nat.le_of_eq #[eq])], po]
          best := lower best (some (d, ← hinted p t d))
    return best
  -- Products, powers and differences: by their rule, and in the thorough pass also as a whole.
  let composed? : Option (DominatedM (Option (Nat × Lean.Expr))) ←
    if t.isAppOfArity ``HMul.hMul 6 then
      pure (some do
        let some (da, pa, db, pb) ← two t.getAppArgs[4]! t.appArg! | pure none
        let p ← mkAppM ``Dominated.mul #[pa, pb]
        let h ← fn (← mkAppM ``Eq.ge #[← mkAppM ``Nat.pow_add #[Sx, mkNatLit da, mkNatLit db]])
        pure (some (da + db, ← hinted (← mkAppM ``Dominated.mono #[p, h]) t (da + db))))
    else if t.isAppOfArity ``HPow.hPow 6 then do
      match ← (evalNat t.appArg!).run with
      | some n => pure (some do
          let some (da, pa) ← sub t.getAppArgs[4]! | pure none
          let p ← mkAppM ``Dominated.pow #[pa, mkNatLit n]
          let h ← fn (← mkAppM ``Eq.ge #[← mkAppM ``Nat.pow_mul #[Sx, mkNatLit da, mkNatLit n]])
          pure (some (da * n, ← hinted (← mkAppM ``Dominated.mono #[p, h]) t (da * n))))
      | none => pure none
    else if t.isAppOfArity ``HSub.hSub 6 then
      pure (some do
        let some (da, pa) ← sub t.getAppArgs[4]! | pure none
        pure (some (da, ← hinted (← mkAppM ``Dominated.sub_left #[pa, ← fn t.appArg!]) t da)))
    else pure none
  if let some composed := composed? then
    unless thorough do return ← composed
    -- A whole bound of degree 1 is the least possible, so the parts need not be read.
    let whole ← bound false
    if whole.any (·.1 ≤ 1) then return whole
    return lower (← composed) whole
  -- The size of a structure whose projections occur: read through its projections.
  if let some (u, eq) ← fieldSizes? projected t then
    if let some (d, po) ← sub u then
      let p ← mkAppM ``Dominated.trans
        #[← mkAppM ``Dominated.of_le #[← fn (← mkAppM ``Nat.le_of_eq #[eq])], po]
      return some (d, ← hinted p t d)
  bound true

/-- Whether the body of `f` matches on a pattern (a `match`, `casesOn` or recursor), whose variables
degree synthesis cannot see. -/
def matchesPattern (f : Lean.Expr) : MetaM Bool := do
  withLocalDeclD `x (← domainOf f) fun x => do
    let body := (mkApp f x).headBeta
    let env ← getEnv
    return (body.find? fun e =>
      (e.getAppFn.constName?.any fun n => n.isStr && (n.getString! == "casesOn" ||
        n.getString! == "rec" || (Lean.Meta.Match.Extension.getMatcherInfo? env n).isSome))).isSome

/-- The condition of an `if` in the body of `f` that depends only on the input, not on variables
bound in the body, as a predicate on the input. -/
def conditionOf? (f : Lean.Expr) : MetaM (Option Lean.Expr) := do
  withLocalDeclD `x (← domainOf f) fun x => do
    let some t := (mkApp f x).headBeta.find? fun t =>
        (t.isAppOfArity ``ite 5 || t.isAppOfArity ``dite 5) && !t.getAppArgs[1]!.hasLooseBVars
      | return none
    return some (← mkLambdaFVars #[x] t.getAppArgs[1]!)

/-- Whether the right side has a power of degree at least 2, also once the definitions of the list
are unfolded. Products and powers are compared only then: a product or power of non-constant terms
has degree at least 2. -/
def hasHighPower (g : Lean.Expr) : DominatedM Bool := do
  withLocalDeclD `x (← domainOf g) fun x => do
    let r := (mkApp g x).headBeta
    let high (r : Lean.Expr) := (r.find? fun t => t.isAppOfArity ``HPow.hPow 6 &&
      (t.appArg!.nat?.any (2 ≤ ·) || !t.appArg!.isLit && t.appArg!.nat?.isNone)).isSome
    if high r then return true
    -- The right side read through the definitions of the list.
    let (r', _) ← simp r (← (← read).sizesUnfold.get)
    return high r'.expr

/-- `Dominated f g` by degree synthesis. The candidate bases `S`, with exponents `e`, are the powers
of `g`, first those of its linear form and then those within its terms, also once the definitions
of the list are unfolded (read only here: the goals left to the user keep `g`), and lastly `g`
itself with exponent 1. For a positive `S`, the degree `d` of the left side comes from `degree`,
and when `d ≤ e`, `Dominated (fun x => S x ^ e) g` from the pointwise step. All candidates are
tried by the rules alone before any is tried thoroughly. On the element domain of a traversal, the
`Dominated` hypotheses about the outer input are composed with the projection to it. -/
def viaDegree (f g : Lean.Expr) : DominatedM (Option Lean.Expr) := do
  let outer := (← getLCtx, ← getLocalInstances)
  withLocalDeclD `x (← domainOf f) fun x => do
    let body := (mkApp f x).headBeta
    let r := (mkApp g x).headBeta
    -- The powers of the right side: those of its linear form first, then those within its terms.
    let powers (e : Lean.Expr) : MetaM (Array (Lean.Expr × Nat)) := do
      let (_, nested) ← (e.forEach' fun t => do
          if t.isAppOfArity ``HPow.hPow 6 && !t.hasLooseBVars then modify (·.push t)
          return true : StateT (Array Lean.Expr) MetaM Unit).run #[]
      let mut out := #[]
      for t in (linearForm e).2.map (·.1) ++ nested do
        unless t.isAppOfArity ``HPow.hPow 6 do continue
        let some n ← (evalNat t.appArg!).run | continue
        let b := t.getAppArgs[4]!
        unless 0 < n && (← isDefEq (← inferType b) (mkConst ``Nat)) do continue
        unless out.contains (b, n) do out := out.push (b, n)
      return out
    let mut candidates : Array (Lean.Expr × Nat) := ← powers r
    -- Facts about the outer input, along the projection to it on an element domain.
    let domain ← whnfR (← domainOf f)
    let mut composedFacts : Array (Lean.Expr × Lean.Expr) := #[]
    if domain.isAppOf ``Sigma then
      let projection ← withLocalDeclD `z domain fun z => do
        mkLambdaFVars #[z] (← mkAppM ``Sigma.fst #[z])
      for (h, type) in (← read).facts do
        if let some h' ← (observing? (mkAppM ``Dominated.comp #[h, projection]) : MetaM _) then
          let lam (k : Lean.Expr) := withLocalDeclD `z domain fun z => do
            mkLambdaFVars #[z] (mkApp k (mkApp projection z)).headBeta
          let composed ← mkAppM ``Dominated #[← lam type.appFn!.appArg!, ← lam type.appArg!]
          composedFacts := composedFacts.push (← mkExpectedTypeHint h' composed, composed)
    let (r', _) ← simp r (← (← read).sizesUnfold.get)
    let projected ← projectedIn #[body, r, r'.expr]
    if r'.expr != r then
      for c in ← powers r'.expr do
        unless candidates.contains c do candidates := candidates.push c
    -- The right side itself, unless it is already a power among the candidates.
    unless r.isAppOfArity ``HPow.hPow 6 && candidates.any (·.1 == r.getAppArgs[4]!) do
      candidates := candidates.push (r, 1)
    -- First by the rules alone, then also bounding products, powers and differences as wholes.
    for thorough in [false, true] do
      for (base, e) in candidates do
        let S ← mkLambdaFVars #[x] base
        let some hS ← withLCtx outer.1 outer.2 (positive S) | continue
        let saved ← show TacticM _ from saveState
        let run : DominatedM (Option (Nat × Lean.Expr)) :=
          withReader (fun c => { c with facts := c.facts ++ composedFacts })
            (degree outer projected thorough x S hS body)
        let res ← try run catch _ => do
          saved.restore
          pure none
        let some (d, p) := res | continue
        if d > e then continue
        let p ← (do
          if d == e then return p
          mkAppM ``Dominated.mono_pow
            #[p, ← mkDecideProof (← mkAppM ``LE.le #[mkNatLit d, mkNatLit e]), hS] :
            MetaM Lean.Expr)
        let Se ← mkLambdaFVars #[x] (← mkAppM ``HPow.hPow #[base, mkNatLit e])
        let mut q? : Option Lean.Expr := none
        if base == r && e == 1 then
          q? := some (← mkAppM ``Dominated.of_le #[← mkLambdaFVars #[x] (← mkAppM ``Nat.le_of_eq
            #[← mkAppM ``Nat.pow_one #[base]])])
        else
          q? ← withLCtx outer.1 outer.2 (attempt (proveBase Se g))
        let some q := q? | continue
        let h ← instantiateMVars (← mkAppM ``Dominated.trans #[p, q])
        if h.containsFVar x.fvarId! || h.hasMVar then continue
        return some h
    return none

/-- Unfold compositions, so that matching a fact is reducible and cheap to fail. -/
def unfoldComp (e : Lean.Expr) : MetaM Lean.Expr := Meta.transform e (post := fun t => do
  if t.isAppOfArity ``Function.comp 5 then
    let args := t.getAppArgs
    return .done (← withLocalDeclD `x args[0]! fun x => do
      mkLambdaFVars #[x] (mkApp args[3]! (mkApp args[4]! x).headBeta).headBeta)
  return .continue)

/-- Whether `f` is the encoded size of a projection, possibly nested, of the value whose encoded
size is `f'`: a fact about `f'` then bounds `f` through the pointwise step. -/
def sizeOfProjection (f f' : Lean.Expr) : MetaM Bool := do
  withLocalDeclD `z (← domainOf f) fun z => do
    let a := (mkApp f z).headBeta
    let b := (mkApp f' z).headBeta
    let value? (e : Lean.Expr) : Option Lean.Expr :=
      if e.isAppOfArity ``Tree.size 1 && e.appArg!.isAppOfArity ``UniqueEncoding.encode 4 then
        some e.appArg!.appArg! else none
    let some va := value? a | return false
    let some vb := value? b | return false
    return va != vb && (va.find? (· == vb)).isSome

/-! ### The two targets

A summand is compared with a given right side, `Dominated f g`, or shown polynomial in a measure,
`IsPoly s f`. Both go through the same steps; `IsPoly` splits products and constant powers without
loss, so its parts combine by its closure rules, with no degree. -/

/-- What is proved about a left side `f`: `Dominated f g`, or `IsPoly s f`. -/
inductive Target where
  /-- `Dominated f g`, for a given right side `g`. -/
  | dominated (g : Lean.Expr)
  /-- `IsPoly s f`, that `f` is polynomial in the measure `s`. -/
  | poly (s : Lean.Expr)

namespace Target

/-- The goal about the left side `f`. -/
def goal (target : Target) (f : Lean.Expr) : MetaM Lean.Expr :=
  match target with
  | dominated g => mkAppM ``Dominated #[f, g]
  | poly s => mkAppM ``IsPoly #[s, f]

/-- The left side and the target of a goal `Dominated f g` or `IsPoly s f`. -/
def of? (type : Lean.Expr) : Option (Lean.Expr × Target) :=
  if type.isAppOf ``Dominated then some (type.appFn!.appArg!, dominated type.appArg!)
  else if type.isAppOfArity ``IsPoly 3 then some (type.appArg!, poly type.appFn!.appArg!)
  else none

/-- The target on a domain mapped to the input by `π`: the right side or the measure composed
with `π`. -/
def along (target : Target) (domain π : Lean.Expr) : MetaM Target := do
  let comp (k : Lean.Expr) : MetaM Lean.Expr := withLocalDeclD `y domain fun y => do
    mkLambdaFVars #[y] (mkApp k (mkApp π y).headBeta).headBeta
  match target with
  | dominated g => return dominated (← comp g)
  | poly s => return poly (← comp s)

/-- The traversal rules of the target's kind whose growth matches the left side `f`, in the order
of registration, each with the normalization of its elements: the expansion of encoded sizes, also
distributing the table length over an entry for a rule registered with `mul`. -/
def traversals (target : Target) (f : Lean.Expr) (ctx : Context) :
    MetaM (Array (Name × LazySimp)) := do
  let poly := target matches poly _
  let found ← withLocalDeclD `x (← domainOf f) fun x =>
    ctx.traversalRules.index.getMatch (f.beta #[x])
  return (found.qsort (· < ·)).filterMap fun i =>
    let r := ctx.traversalRules.rules[i]!
    if r.poly == poly then some (r.name, if r.mul then ctx.sizesMul else ctx.sizes) else none

end Target

/-- `IsPoly s f` without facts: `f` within a multiple of `s + 1` pointwise, a linear comparison;
higher degrees come from the closure rules and from upper bounds. Comparing linearly only is the
current choice, to be revisited if it meets a problem. That `f` is `s` itself is seen when
splitting. -/
def proveBasePoly (f s : Lean.Expr) : DominatedM (Option Lean.Expr) := do
  let succ ← withLocalDeclD `x (← domainOf f) fun x => do
    mkLambdaFVars #[x] (← mkAppM ``HAdd.hAdd #[(mkApp s x).headBeta, mkNatLit 1])
  let some h ← pointwise f succ | return none
  let hsucc ← mkExpectedTypeHint (← mkAppM ``IsPoly.add
    #[← mkAppOptM ``IsPoly.refl #[none, s], ← mkAppOptM ``IsPoly.const #[none, s, mkNatLit 1]])
    (← mkAppM ``IsPoly #[s, succ])
  return some (← mkAppM ``IsPoly.of_dominated #[hsucc, h])

/-- The polynomial growths `IsPoly r T` whose `T a` is the body of `f`, each with `fun x => a`: the
hypotheses, and the statements registered with `@[dominated]` or in the list, their premises
determined by the match. -/
def growthsAt (f : Lean.Expr) : DominatedM (Array (Lean.Expr × Lean.Expr)) := do
  let ctx ← read
  withLocalDeclD `x (← domainOf f) fun x => do
    let t := (mkApp f x).headBeta
    let mut growths := ctx.polyFacts
    for e in ← ctx.polyLemmas.getMatch t do
      let saved ← show TacticM _ from saveState
      let (xs, _, type) ← forallMetaTelescopeReducing (← inferType e)
      let a ← mkFreshExprMVar (← domainOf type.appArg!)
      if ← withReducible (isDefEq (mkApp type.appArg! a).headBeta t) then
        let fact ← instantiateMVars (mkAppN e xs)
        unless fact.hasExprMVar || fact.containsFVar x.fvarId! do growths := growths.push fact
      saved.restore
    let mut out := #[]
    for hT in growths do
      let T := (← instantiateMVars (← inferType hT)).appArg!
      let a ← mkFreshExprMVar (← domainOf T)
      unless ← withReducible (isDefEq (mkApp T a).headBeta t) do continue
      let a ← instantiateMVars a
      if a.hasExprMVar then continue
      out := out.push (hT, ← mkLambdaFVars #[x] a)
    return out

mutual

/-- `Dominated f g` or `IsPoly s f` through a fact `Dominated f' g'`. Against `g`: directly when
`g'` is `g`, otherwise with `Dominated g' g` from `proveBase`, or by degree synthesis when `g` has a
power of degree at least 2, so facts are never chained. On an `IsPoly` goal: with `g'` polynomial in
`s` in turn; and as `T a`, given a polynomial growth `IsPoly r T` (`growthsAt`), by composition with
`r a` polynomial in `s` in turn. `f'` is `f`, or a value of which `f` is the size of a projection,
with `Dominated f f'` from `proveBase`. On the element domain of a traversal, a fact about the outer
input is used along the projection to that input. -/
partial def viaFacts (f : Lean.Expr) (target : Target) : DominatedM (Option Lean.Expr) := do
  let domain ← whnfR (← domainOf f)
  let projection? : Option Lean.Expr ←
    if domain.isAppOf ``Sigma then
      some <$> withLocalDeclD `z domain fun z => do
        mkLambdaFVars #[z] (← mkAppM ``Sigma.fst #[z])
    else if domain.isAppOf ``Subtype then
      (observing? (withLocalDeclD `z domain fun z => do
        mkLambdaFVars #[z] (← mkAppM ``Prod.fst #[← mkAppM ``Subtype.val #[z]])) : MetaM _)
    else pure none
  for (h, type) in (← read).facts do
    let mut candidates := #[(h, type)]
    if let some projection := projection? then
      if let some h' ← (observing? (mkAppM ``Dominated.comp #[h, projection]) : MetaM _) then
        let lam (k : Lean.Expr) := withLocalDeclD `z domain fun z => do
          mkLambdaFVars #[z] (mkApp k (mkApp projection z)).headBeta
        let composed ← mkAppM ``Dominated #[← lam type.appFn!.appArg!, ← lam type.appArg!]
        candidates := candidates.push (← mkExpectedTypeHint h' composed, composed)
    for (h, type) in candidates do
      let f' := type.appFn!.appArg!
      let mut h := h
      unless ← withReducible (isDefEq f' f) do
        -- A fact about a value also bounds the size of its projections.
        unless ← sizeOfProjection f f' do continue
        let some hf ← memo (← mkAppM ``Dominated #[f, f']) (attempt (proveBase f f')) | continue
        h ← mkAppM ``Dominated.trans #[hf, h]
      let g' := type.appArg!
      match target with
      | .dominated g =>
        if ← withReducible (isDefEq g' g) then return some h
        if let some rest ← memo (← mkAppM ``Dominated #[g', g]) (do
            if let some h ← attempt (proveBase g' g) then return some h
            unless ← hasHighPower g do return none
            attempt (viaDegree g' g)) then
          return some (← mkAppM ``Dominated.trans #[h, rest])
      | .poly _ =>
        if let some p ← split g' target (← read).sizes prove then
          return some (← mkAppM ``IsPoly.of_dominated #[p, h])
  let .poly s := target | return none
  -- A polynomial growth applied in `f`, by composition.
  for (hT, a) in ← growthsAt f do
    let r := (← instantiateMVars (← inferType hT)).appFn!.appArg!
    let ra ← withLocalDeclD `x (← domainOf f) fun x => do
      mkLambdaFVars #[x] (mkApp r (mkApp a x).headBeta).headBeta
    let some p ← split ra target (← read).sizes prove | continue
    let h ← mkAppOptM ``IsPoly.comp #[none, s, none, none, none, a, hT, p]
    return some (← mkExpectedTypeHint h (← mkAppM ``IsPoly #[s, f]))
  return none

/-- Expand encoded sizes in `f` with `ctx` and split it without loss: its sums, maxima and zeros,
and on an `IsPoly` goal also its products, powers with an exponent independent of the input, and
constants. A difference is proved as stated when it is the target or a fact, and through its
minuend otherwise, on an `IsPoly` goal as a whole when its minuend is not polynomial. `leaf` proves
the remaining summands. The target is not rewritten.

On an `IsPoly` goal the arithmetic is split before the encoded sizes are expanded, and each part
that is the measure itself, possibly up to structure eta, is closed at once: expanding it would
leave its fields to be compared one by one. -/
partial def split (f : Lean.Expr) (target : Target) (ctx : LazySimp)
    (leaf : Lean.Expr → Target → DominatedM (Option Lean.Expr)) :
    DominatedM (Option Lean.Expr) := do
  -- The goal about `f` from the goal about its normal form.
  let normalize (f : Lean.Expr) (k : Lean.Expr → DominatedM (Option Lean.Expr)) :
      DominatedM (Option Lean.Expr) := do
    let (r, _) ← simp f (← ctx.get)
    let some proof ← k r.expr | return none
    let some eq := r.proof? | return some proof
    let motive ← withLocalDeclD `F (← inferType f) fun F => do
      mkLambdaFVars #[F] (← target.goal F)
    let proof ← mkExpectedTypeHint proof (← target.goal r.expr)
    return some (← mkEqMPR (← mkCongrArg motive eq) proof)
  let rec go (normalized : Bool) (f : Lean.Expr) : DominatedM (Option Lean.Expr) := do
    let two (rule : Name) (a b : Lean.Expr) : DominatedM (Option Lean.Expr) := do
      let some pa ← go normalized a | return none
      let some pb ← go normalized b | return none
      return some (← mkAppM rule #[pa, pb])
    if let .poly s := target then
      if ← withReducible (isDefEq f s) then return some (← mkAppOptM ``IsPoly.refl #[none, s])
      if let .lam n α body bi := f then
        let part (e : Lean.Expr) := Lean.Expr.lam n α e bi
        let args := body.getAppArgs
        if body.isAppOfArity ``HAdd.hAdd 6 then
          return ← two ``IsPoly.add (part args[4]!) (part args[5]!)
        if body.isAppOfArity ``Max.max 4 then
          return ← two ``IsPoly.max (part args[2]!) (part args[3]!)
        if body.isAppOfArity ``HMul.hMul 6 then
          return ← two ``IsPoly.mul (part args[4]!) (part args[5]!)
        if body.isAppOfArity ``HPow.hPow 6 && !args[5]!.hasLooseBVars then
          let some pa ← go normalized (part args[4]!) | return none
          return some (← mkAppM ``IsPoly.pow #[pa, args[5]!])
        if !body.hasLooseBVars then return some (← mkAppOptM ``IsPoly.const #[none, s, body])
    unless normalized do return ← normalize f (go true)
    let .lam n α body bi := f | leaf f target
    let part (e : Lean.Expr) := Lean.Expr.lam n α e bi
    let args := body.getAppArgs
    match target with
    | .dominated g =>
      if body.isAppOfArity ``HAdd.hAdd 6 then
        return ← two ``Dominated.add_same (part args[4]!) (part args[5]!)
      if body.isAppOfArity ``Max.max 4 then
        return ← two ``Dominated.max_same (part args[2]!) (part args[3]!)
      if body.isAppOfArity ``HSub.hSub 6 then
        -- The difference itself when it is the target or a fact; its minuend otherwise.
        if ← withReducible (isDefEq f g) then return some (← mkAppM ``Dominated.refl #[g])
        if let some h ← attempt (viaFacts f target) then return some h
        let some h ← go true (part args[4]!) | return none
        return some (← mkAppM ``Dominated.sub_left #[h, part args[5]!])
      if body.nat? == some 0 then
        let zero ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``Dominated #[f, g])
        let _ ← zero.mvarId!.apply (← mkConstWithFreshMVarLevels ``Dominated.zero)
        return some (← instantiateMVars zero)
    | .poly _ =>
      if body.isAppOfArity ``HSub.hSub 6 then
        -- The difference itself when it is a fact; its minuend when that is polynomial, proved
        -- completely, and otherwise the difference as a whole.
        if let some h ← attempt (viaFacts f target) then return some h
        if let some h ← split (part args[4]!) target ctx prove then
          return some (← mkAppM ``IsPoly.sub #[h, part args[5]!])
    leaf f target
  match target with
  | .dominated _ => normalize f (go true)
  | .poly _ => go false f

/-- `Dominated f g` pointwise with the facts about the products and powers that `f` depends on
(`addPowerFacts`), for a `match` on a pattern, whose variables degree synthesis cannot see. This
keeps the earlier treatment of products and powers for these summands, provisionally (plan W2). -/
partial def viaPowerFacts (f g : Lean.Expr) : DominatedM (Option Lean.Expr) := do
  modify fun s => { s with nonlinear := true }
  let r ← attempt (do
    if let some h ← viaFacts f (.dominated g) then return some h
    proveBase f g)
  modify fun s => { s with nonlinear := false }
  return r

/-- `Dominated f g` or `IsPoly s f` for a left side with an `if` whose condition depends only on the
input, by `Dominated.of_cases` or `IsPoly.of_cases` on the condition. On each part the condition is
the property of the subtype, which settles the `if`s on it, and the part is split and proved
again. -/
partial def viaCases (f : Lean.Expr) (target : Target) : DominatedM (Option Lean.Expr) := do
  let α ← domainOf f
  let some p ← conditionOf? f | return none
  let part (holds : Bool) : DominatedM (Option Lean.Expr) := do
    let (f', funEq) ← settleCases f p holds
    let domain ← domainOf f'
    let target' ← target.along domain
      (← withLocalDeclD `y domain fun y => do mkLambdaFVars #[y] (← mkAppM ``Subtype.val #[y]))
    let some proof ← split f' target' (← read).sizes prove | return none
    let motive ← withLocalDeclD `F (← inferType f') fun F => do
      mkLambdaFVars #[F] (← target'.goal F)
    return some (← mkEqMPR (← mkCongrArg motive funEq) proof)
  let some yes ← part true | return none
  let some no ← part false | return none
  match target with
  | .dominated g => return some (← mkAppOptM ``Dominated.of_cases #[α, f, g, p, yes, no])
  | .poly s => return some (← mkAppOptM ``IsPoly.of_cases #[α, s, f, p, yes, no])

/-- `IsPoly s f` through an upper bound of the body `t` of `f`, polynomial in `s` in turn, as an
atom is bounded in degree synthesis: the size of a structure whose projections occur, in `t` or in
`s`, through the sizes of its fields; `t ≤ u` from a comparison about `t` (`comparisonsAbout`); and
`t` read through the definitions of the list. With no degree to compare, the first bound polynomial
in `s` is used. -/
partial def viaBound (f s : Lean.Expr) : DominatedM (Option Lean.Expr) := do
  let ctx ← read
  let α ← domainOf f
  -- Bounds `t ≤ u` are found with `x` in scope, and proved polynomial outside it, so that no
  -- auxiliary proof captures `x`.
  let via (bounds : Lean.Expr → Lean.Expr → DominatedM (Array (Lean.Expr × Lean.Expr))) :
      DominatedM (Option Lean.Expr) := do
    let found ← withLocalDeclD `x α fun x => do
      (← bounds x (mkApp f x).headBeta).mapM fun (u, le) => do
        return (← mkLambdaFVars #[x] u, ← mkLambdaFVars #[x] le)
    for (u, le) in found do
      let some p ← split u (.poly s) ctx.sizes prove | continue
      return some (← mkAppM ``IsPoly.of_dominated #[p, ← mkAppM ``Dominated.of_le #[le]])
    return none
  let ofEq (u eq : Lean.Expr) : MetaM (Array (Lean.Expr × Lean.Expr)) := do
    return #[(u, ← mkAppM ``Nat.le_of_eq #[eq])]
  if let some p ← via fun x t => do
      let sx := (mkApp s x).headBeta
      let (sx', _) ← simp sx (← ctx.sizesUnfold.get)
      let some (u, eq) ← fieldSizes? (← projectedIn #[t, sx, sx'.expr]) t | return #[]
      ofEq u eq then
    return some p
  if let some p ← via fun x t => do
      (← comparisonsAbout x t).filterMapM (upperBound t ·) then
    return some p
  via fun _ t => do
    let (r, _) ← simp t (← ctx.sizesUnfold.get)
    if r.expr == t then return #[]
    ofEq r.expr (← r.getProof)

/-- One summand against the target: a fact; a registered traversal rule, comparing for example a
maximum over a list element by element or a table sum entry by entry; the linear
pointwise step, against `g` or `s + 1`; and then, on an `IsPoly` goal or against a power of degree
at least 2 on the right, the facts about products and powers for a `match` on a pattern (against
`g` only), cases on the condition of an `if`, and degree synthesis against `g` or an upper bound
polynomial in `s`. Traversal rules read the target on the element domain and split the element,
which must be proved completely. -/
partial def prove (f : Lean.Expr) (target : Target) : DominatedM (Option Lean.Expr) := do
  let type ← target.goal f
  memo type do
    if let some h ← attempt (viaFacts f target) then return some h
    let element (ctx : LazySimp) (type : Lean.Expr) : DominatedM (Option Lean.Expr) := do
      let some (a, target) := Target.of? type.consumeMData | return none
      split a target ctx prove
    for (rule, ctx) in ← target.traversals f (← read) do
      if let some h ← viaRule rule type (element ctx) then return some h
    match target with
    | .dominated g =>
      if let some h ← attempt (proveBase f g) then return some h
      unless ← hasHighPower g do return none
      if ← matchesPattern f then return ← viaPowerFacts f g
    | .poly s =>
      if let some h ← attempt (proveBasePoly f s) then return some h
      -- The variables of a pattern are not seen by the bounds: such a summand is compared
      -- pointwise only, provisionally (plan W2).
      if ← matchesPattern f then return none
    if (← conditionOf? f).isSome then return ← attempt (viaCases f target)
    match target with
    | .dominated g => attempt (viaDegree f g)
    | .poly s => attempt (viaBound f s)

end

/-- Prove a summand, or leave it as a goal; equal summands share one goal. -/
def proveOrLeave (f : Lean.Expr) (target : Target) : DominatedM (Option Lean.Expr) := do
  if let some h ← prove f target then return some h
  let type ← instantiateMVars (← target.goal f)
  if let some (_, goal) := (← get).left.find? (·.1 == type) then return some (mkMVar goal)
  let goal ← mkFreshExprSyntheticOpaqueMVar type
  modify fun s => { s with left := s.left.push (type, goal.mvarId!) }
  return some goal

/-- The definitions, the statements `a ≤ b`, `a < b` or `a = b`, and the statements `IsPoly r T`
of a list given to `tactic`. -/
def listItems (tactic : String) (args : Array Term) :
    TacticM (Array Name × Array Lean.Expr × Array Lean.Expr) := do
  let mut unfolds := #[]
  let mut lemmas := #[]
  let mut growths := #[]
  for arg in args do
    let e ← Term.withoutErrToSorry <| elabTermForApply arg
    let type ← inferType e
    if let some name := e.constName? then
      unless ← isProp type do
        unfolds := unfolds.push name
        continue
    let (_, _, body) ← forallMetaTelescopeReducing type
    if body.consumeMData.isAppOfArity ``IsPoly 3 then
      growths := growths.push e
      continue
    if (key? body).isNone then
      throwErrorAt arg
        "{tactic}: expected a definition, a statement `a ≤ b`, `a < b` or `a = b`, \
          or `IsPoly r T`"
    lemmas := lemmas.push e
  return (unfolds, lemmas, growths)

/-- Close a growth comparison `Dominated f g` whose two sides are given, or a polynomial growth
`IsPoly s f`, splitting the left side without loss: sums and maxima, and for `IsPoly` also
products and constant powers; equal summands are proved once. Local `Dominated` hypotheses are
used as facts, and for `IsPoly` also local `IsPoly` hypotheses. The list gives definitions to
unfold when comparing pointwise, statements `a ≤ b`, `a < b` or `a = b` to instantiate at matching
terms there, as for those registered with `@[dominated]`, and statements `IsPoly r T` to use at
matching parts on `IsPoly` goals. Products and powers are compared by their degrees against the
powers of the right side, read through the definitions of the list: an equation about the right
side given in the list is not used for this. Summands that cannot be proved are left as goals. -/
syntax (name := dominated) "dominated" (" [" term,* "]")? : tactic

/-- The statements concluding `IsPoly r T` among `extra` and those registered with
`@[dominated]`, by the part `T a` each is about. -/
def polyTree (extra : Array Lean.Expr) : MetaM (DiscrTree Lean.Expr) := do
  let mut tree : DiscrTree Lean.Expr := {}
  for e in extra ++ (← (dominatedAttr.getState (← getEnv)).mapM (mkConstWithFreshMVarLevels ·)) do
    let (_, _, type) ← forallMetaTelescopeReducing (← inferType e)
    unless type.isAppOfArity ``IsPoly 3 do continue
    let a ← mkFreshExprMVar (← domainOf type.appArg!)
    tree ← tree.insert (mkApp type.appArg! a).headBeta e
  return tree

/-- The context of one call: the `Dominated` hypotheses, the simp sets, and the definitions and
statements of the list; for an `IsPoly` goal also the polynomial growths among the hypotheses and
the statements `IsPoly r T` registered or in `growths`. -/
def mkContext (target : Target) (unfolds : Array Name) (lemmas growths : Array Lean.Expr) :
    TacticM Context := do
  let mut facts := #[]
  let mut polyFacts := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let type := (← instantiateMVars decl.type).consumeMData
    if type.isAppOf ``Dominated then facts := facts.push (decl.toExpr, ← unfoldComp type)
    if type.isAppOfArity ``IsPoly 3 then polyFacts := polyFacts.push decl.toExpr
  let sizes ← LazySimp.new <| simpContext #[``Function.comp_apply, ``Nat.mul_one, ``Tree.size_pair]
    (attrs := #[`dominated_simp])
  let sizesUnfold ← LazySimp.new <| simpContext
    #[``Function.comp_apply, ``Nat.mul_one, ``Tree.size_pair] unfolds (attrs := #[`dominated_simp])
  let sizesMul ← LazySimp.new <| simpContext
    #[``Function.comp_apply, ``Nat.mul_add, ``Nat.mul_one, ``Nat.mul_zero]
    (attrs := #[`dominated_simp])
  let expand ← LazySimp.new <| simpContext (simpOnlyBuiltins.toArray ++ #[``Function.comp_apply,
    ``max_le_iff, ``Tree.size_pair, ``not_true_eq_false,
    ``List.map_const', ``List.sum_replicate, ``smul_eq_mul, ``pow_zero]) unfolds
    (attrs := #[`dominated_simp, `dominated_expand])
  let numerals := #[← (← (← ({} : Simp.Simprocs).add ``Nat.reduceMul true).add ``Nat.reduceAdd
    true).add ``encodeParts true]
  let ctx : Context := {
    statements := ← factTree lemmas, premises := ← premiseTree, facts, sizes, sizesMul, expand,
    numerals, sizesUnfold, traversalRules := dominatedTraversalExt.getState (← getEnv) }
  let .poly _ := target | return ctx
  return { ctx with polyFacts, polyLemmas := ← polyTree growths }

elab_rules : tactic
  | `(tactic| dominated $[[$args,*]]?) => withMainContext do
    let goal ← getMainGoal
    -- A property `IsO(T)` applied to a budget, left by unfolding `HasProgramIn`, is a beta redex.
    let type := (← instantiateMVars (← goal.getType)).consumeMData.headBeta
    let some (f, target) := Target.of? type
      | throwError "dominated: expected a `Dominated` or `IsPoly` goal"
    -- Metadata on the left side would hide its sums and its degree.
    let f := eraseMData f
    let (unfolds, lemmas, growths) ← listItems "dominated" (args.map (·.getElems) |>.getD #[])
    let ctx ← mkContext target unfolds lemmas growths
    let (proof, state) ← (split f target ctx.sizes proveOrLeave |>.run ctx).run {}
    let some proof := proof | throwError "dominated: no proof"
    goal.assign (← mkExpectedTypeHint proof type)
    replaceMainGoal (state.left.map (·.2)).toList

end Complexity.Tactic.Dominated
