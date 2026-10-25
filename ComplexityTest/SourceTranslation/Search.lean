/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Complexity.Tactic.TreeProgram.Library

noncomputable section

open Complexity TreeProgram Complexity.TreeProgram.Source
namespace ComplexityTest.SourceTranslation.Search

section Composition

-- Selected callbacks compose their growths without choosing new programs.
example (f g : Bool → Bool) {t p u q : Bool → ℕ} (_hf : Implementation f t p)
    (_hg : Implementation g u q) :
    Implementation (fun x => g (f x)) (fun x => t x + u (f x)) (fun x => max (p x) (q (f x))) := by
  source_fun_prop

-- Let sharing keeps the input and pays for the callback once.
example (f : Bool → Bool) (g : Bool × Bool → Bool) {t p : Bool → ℕ} {u q : Bool × Bool → ℕ}
    (_hf : Implementation f t p) (_hg : Implementation g u q) :
    Implementation (fun x => let y := f x; g (x, y)) (fun x => 0 + (t x + 1) + u (x, f x))
      (fun x => max (max 0 (max (p x) ⌜(x, f x)⌝ₜ.size)) (q (x, f x))) := by
  source_fun_prop

end Composition

section CandidateFailure

private def unsupported : List Bool → List Bool
  | [] => []
  | x :: xs => unsupported xs ++ [x]

private def chosen (xs : List Bool) := xs.reverse

private def availableImplementation :
    Implementation chosen (fun xs => ⌜xs⌝ₜ.size) (fun xs => ⌜xs⌝ₜ.size) :=
  Implementation.reverse

private def needsRecursive (_h : Implementation unsupported (fun _ => 1) (fun _ => 1)) :
    Implementation chosen (fun xs => ⌜xs⌝ₜ.size) (fun xs => ⌜xs⌝ₜ.size) :=
  availableImplementation

-- A failed implementation premise is rolled back before another implementation rule is tried.
attribute [local fun_prop] availableImplementation needsRecursive

example : (by source_fun_prop : Implementation chosen _ _).program =
    availableImplementation.program := rfl

end CandidateFailure

private def uncertified : List Bool → List Bool
  | [] => []
  | b :: bs => b :: b :: uncertified bs

-- Encoded results report the unsupported source operation, not its encoder.
/--
error: source translation: `ComplexityTest.SourceTranslation.Search.uncertified` needs a registered implementation (choose replacement source with `via`, or register a function equality with `[source]`)
source path: fun xs => encode Complexity.Tree (uncertified xs) → uncertified
-/
#guard_msgs in
example : Implementation (fun xs => ⌜uncertified xs⌝ₜ) (fun _ => 1) (fun _ => 1) := by
  source_fun_prop

section LocalPriority

-- A uniform chosen implementation is reusable at each runtime iteration.
example (f : Bool → Bool) {t p : Bool → ℕ} (_callback : Implementation f t p) :
    Implementation (fun x : ℕ × Bool => f^[x.1] x.2) (fun x => iterateTime f t x.1 x.2 + 1)
      (fun x => iteratePeak f p x.1 x.2) := by source_fun_prop

-- Local selection takes precedence over a registered default.
example {t p : List Bool → ℕ} (h : Implementation (List.reverse : List Bool → List Bool) t p) :
    (by source_fun_prop : Implementation (List.reverse : List Bool → List Bool) t p) = h := rfl

private def alternative (xs : List Bool) := xs.reverse

@[local fun_prop] private def defaultImplementation :
    Implementation alternative (fun xs => ⌜xs⌝ₜ.size) (fun xs => ⌜xs⌝ₜ.size) :=
  Implementation.reverse.congr rfl

example {t p : List Bool → ℕ} (selected : Implementation alternative t p) :
    (by source_fun_prop : Implementation alternative t p) = selected := rfl

example {t p : Bool → ℕ} (selected : Implementation (id : Bool → Bool) t p) :
    (by source_fun_prop : Implementation (id : Bool → Bool) t p) = selected := rfl

example {t p : Bool → ℕ} (selected : Implementation (fun _ : Bool => ()) t p) :
    (by source_fun_prop : Implementation (fun _ : Bool => ()) t p) = selected := rfl

private def doubleReverse (xs : List Bool) := xs.reverse.reverse

@[local fun_prop] private def doubleReverseDefault : Implementation doubleReverse
    (fun xs => ⌜xs⌝ₜ.size + ⌜xs.reverse⌝ₜ.size) (fun xs => max ⌜xs⌝ₜ.size ⌜xs.reverse⌝ₜ.size) :=
  Implementation.reverse.comp Implementation.reverse

-- A semantic equality can expressly select a faster program; growth search never does so.
example : (by
    let selected : Implementation doubleReverse (fun _ => 0) (fun _ => 0) :=
      Implementation.identity.congr (by
        funext xs
        exact (List.reverse_reverse xs).symm)
    source_fun_prop : Implementation doubleReverse _ _).program =
      (Implementation.identity (α := List Bool)).program := rfl

example : (by source_fun_prop : Implementation doubleReverse _ _).program =
    doubleReverseDefault.program := rfl

end LocalPriority

section RuleStages

private def stored (x : Bool × Bool) : Bool := x.1

private def rebuilt : Implementation stored (fun _ => 1 + (1 + 1) + 1)
    (fun x => max (max ⌜x⌝ₜ.size (max ⌜x⌝ₜ.size ⌜(x.1, x.2)⌝ₜ.size)) ⌜(x.1, x.2)⌝ₜ.size) :=
  (Implementation.fst.pair Implementation.snd).comp Implementation.fst

private def preferred := rebuilt
private def secondary : Implementation stored (fun _ => 1) (fun x => ⌜x⌝ₜ.size) :=
  Implementation.fst
private def fallback : Implementation stored (fun _ => 1) (fun x => ⌜x⌝ₜ.size) :=
  Implementation.fst

attribute [local source_fallback] fallback

open Lean Meta Mathlib.Meta.FunProp in
run_elab do
  addTheorem ``preferred .local 20
  addTheorem ``secondary .local 10
  addTheorem ``fallback .local 2000

-- Ordinary registered rules precede structural projection, independent of their numeric cost.
example : (by source_fun_prop : Implementation stored _ _).program = preferred.program := rfl

example : (preferred.program Value.input).build 1 |>.2.1 ≠
    ((secondary.program Value.input).build 1).2.1 := by decide

section
attribute [local source_fallback] preferred secondary

-- Fallback rules do not displace a structural projection.
example : (by source_fun_prop : Implementation stored _ _).program =
    (Implementation.fst (α := Bool) (β := Bool)).program := rfl
end

end RuleStages

section SharedSession

private def branches (x : Bool × List Bool) : List Bool :=
  if x.1 then x.2.reverse else x.2

-- Branch callbacks share the outer translation's search budget.
/-- error: source translation: maximum number (5) of search steps exceeded -/
#guard_msgs in
set_option source.maxSteps 5 in
example : Implementation branches (fun _ => 1) (fun _ => 1) := by source_calls

example := (by source_calls : Implementation branches _ _)

private opaque unavailable : Bool → Bool
private def twice (x : Bool) := unavailable (unavailable x)

@[local fun_prop] private def localScope
    (_h : ∀ _ : Implementation unavailable (fun _ => 1) (fun _ => 1),
      Implementation (fun x => unavailable (unavailable x)) (fun _ => 1) (fun _ => 1))
    (g : Implementation (fun x => unavailable (unavailable x)) (fun _ => 1) (fun _ => 1)) :
    Implementation twice (fun _ => 1) (fun _ => 1) := g

-- A temporary local callback cannot populate a sibling premise's cache.
example : True := by
  fail_if_success have := (by source_fun_prop : Implementation twice _ _)
  trivial

open Lean Meta Elab Tactic in
example : True := by
  run_tac
    let session ← Source.Search.Session.create
    let rejected ← try
      let _ ← session.discharge #[] (throwError "fatal marker") (mkConst ``True)
      pure false
    catch ex => pure ((← ex.toMessageData.toString) == "fatal marker")
    unless rejected do throwError "an unexpected elaboration error was swallowed"
    evalTactic (← `(tactic| trivial))

end SharedSession

end ComplexityTest.SourceTranslation.Search
