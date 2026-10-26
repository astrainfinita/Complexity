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
example (f g : Bool → Bool) {pf pg : Value → Code Value} {t p u q : Bool → ℕ}
    (_hf : HasProgram f pf t p) (_hg : HasProgram g pg u q) :
    HasProgram (fun x => g (f x)) (fun v => pf v >>= pg) (fun x => t x + u (f x))
      (fun x => max (p x) (q (f x))) := by
  source_fun_prop

-- Let sharing keeps the input and pays for the callback once.
example (f : Bool → Bool) (g : Bool × Bool → Bool) {pf pg : Value → Code Value}
    {t p : Bool → ℕ} {u q : Bool × Bool → ℕ} (_hf : HasProgram f pf t p)
    (_hg : HasProgram g pg u q) :
    HasProgram (fun x => let y := f x; g (x, y)) hole(pf, pg ⊢ program)
      (fun x => 0 + (t x + 1) + u (x, f x))
      (fun x => max (max 0 (max (p x) ⌜(x, f x)⌝ₜ.size)) (q (x, f x))) := by
  fill_hole program in source_fun_prop

end Composition

section CandidateFailure

private def unsupported : List Bool → List Bool
  | [] => []
  | x :: xs => unsupported xs ++ [x]

private def chosen (xs : List Bool) := xs.reverse

private theorem hasProgram_available :
    HasProgram chosen hole(⊢ program) (fun xs => ⌜xs⌝ₜ.size) (fun xs => ⌜xs⌝ₜ.size) := by
  abstract_hole program using programAvailable
  fill_hole program in
    exact List.hasProgram_reverse

private theorem needsRecursive {program : Value → Code Value}
    (_h : HasProgram unsupported program (fun _ => 1) (fun _ => 1)) :
    HasProgram chosen programAvailable (fun xs => ⌜xs⌝ₜ.size) (fun xs => ⌜xs⌝ₜ.size) :=
  hasProgram_available

-- A failed implementation premise is rolled back before another implementation rule is tried.
attribute [local fun_prop] hasProgram_available needsRecursive

example := (by source_fun_prop : HasProgram chosen programAvailable _ _)

end CandidateFailure

private def uncertified : List Bool → List Bool
  | [] => []
  | b :: bs => b :: b :: uncertified bs

-- Encoded results report the unsupported source operation, not its encoder.
/--
error: source translation: `ComplexityTest.SourceTranslation.Search.uncertified` needs a registered implementation (choose replacement source with `via`, or register a function equality with `[source]`)
source path: fun xs => encode Complexity.Tree (uncertified xs) → fun xs => uncertified xs
-/
#guard_msgs in
example : HasProgram (fun xs => ⌜uncertified xs⌝ₜ) hole(⊢ program) (fun _ => 1) (fun _ => 1) := by
  fill_hole program in source_fun_prop

section LocalPriority

-- A uniform chosen implementation is reusable at each runtime iteration.
example (f : Bool → Bool) {pf : Value → Code Value} {t p : Bool → ℕ}
    (_callback : HasProgram f pf t p) :
    HasProgram (fun x : ℕ × Bool => f^[x.1] x.2) hole(pf ⊢ program)
      (fun x => iterateTime f t x.1 x.2 + 1) (fun x => iteratePeak f p x.1 x.2) := by
  fill_hole program in source_fun_prop

-- Local selection takes precedence over a registered default.
example {program : Value → Code Value} {t p : List Bool → ℕ}
    (_h : HasProgram (List.reverse : List Bool → List Bool) program t p) :
    HasProgram (List.reverse : List Bool → List Bool) program t p := by
  source_fun_prop

private def alternative (xs : List Bool) := xs.reverse

@[local fun_prop] private theorem hasProgram_default :
    HasProgram alternative hole(⊢ program) (fun xs => ⌜xs⌝ₜ.size) (fun xs => ⌜xs⌝ₜ.size) := by
  abstract_hole program using programDefault
  fill_hole program in
    exact List.hasProgram_reverse.congr rfl

example {program : Value → Code Value} {t p : List Bool → ℕ}
    (_selected : HasProgram alternative program t p) : HasProgram alternative program t p := by
  source_fun_prop

example {program : Value → Code Value} {t p : Bool → ℕ}
    (_selected : HasProgram (id : Bool → Bool) program t p) :
    HasProgram (id : Bool → Bool) program t p := by
  source_fun_prop

example {program : Value → Code Value} {t p : Bool → ℕ}
    (_selected : HasProgram (fun _ : Bool => ()) program t p) :
    HasProgram (fun _ : Bool => ()) program t p := by
  source_fun_prop

private def doubleReverse (xs : List Bool) := xs.reverse.reverse

@[local fun_prop] private theorem hasProgram_doubleReverseDefault :
    HasProgram doubleReverse hole(⊢ program)
    (fun xs => ⌜xs⌝ₜ.size + ⌜xs.reverse⌝ₜ.size) (fun xs => max ⌜xs⌝ₜ.size ⌜xs.reverse⌝ₜ.size) := by
  abstract_hole program using programDoubleReverseDefault
  fill_hole program in
    exact List.hasProgram_reverse.comp List.hasProgram_reverse

-- A semantic equality can expressly select a faster program; growth search never does so.
example := (by
    have _selected : HasProgram doubleReverse (fun v => pure v) (fun _ => 0) (fun _ => 0) :=
      HasProgram.identity.congr (by
        funext xs
        exact (List.reverse_reverse xs).symm)
    source_fun_prop : HasProgram doubleReverse (fun v => pure v) _ _)

example := (by source_fun_prop : HasProgram doubleReverse programDoubleReverseDefault _ _)

end LocalPriority

section RuleStages

private def stored (x : Bool × Bool) : Bool := x.1

private theorem hasProgram_rebuilt : HasProgram stored hole(⊢ program) (fun _ => 1 + (1 + 1) + 1)
    (fun x => max (max ⌜x⌝ₜ.size (max ⌜x⌝ₜ.size ⌜(x.1, x.2)⌝ₜ.size)) ⌜(x.1, x.2)⌝ₜ.size) := by
  abstract_hole program using programRebuilt
  fill_hole program in
    exact (Prod.hasProgram_fst.pair Prod.hasProgram_snd).comp Prod.hasProgram_fst

private alias hasProgram_preferred := hasProgram_rebuilt
private theorem hasProgram_secondary :
    HasProgram stored hole(⊢ program) (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programSecondary
  fill_hole program in
    exact Prod.hasProgram_fst
private theorem hasProgram_fallback :
    HasProgram stored hole(⊢ program) (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programFallback
  fill_hole program in
    exact Prod.hasProgram_fst

attribute [local source_fallback] hasProgram_fallback

open Lean Meta Mathlib.Meta.FunProp in
run_elab do
  addTheorem ``hasProgram_preferred .local 20
  addTheorem ``hasProgram_secondary .local 10
  addTheorem ``hasProgram_fallback .local 2000

-- Ordinary registered rules precede structural projection, independent of their numeric cost.
example := (by source_fun_prop : HasProgram stored programRebuilt _ _)

example : (programRebuilt Value.input).build 1 |>.2.1 ≠
    ((programSecondary Value.input).build 1).2.1 := by decide

section
attribute [local source_fallback] hasProgram_preferred hasProgram_secondary

-- Fallback rules do not displace a structural projection.
example := (by source_fun_prop : HasProgram stored Value.left _ _)
end

end RuleStages

section SharedSession

private def branches (x : Bool × List Bool) : List Bool :=
  if x.1 then x.2.reverse else x.2

-- Branch callbacks share the outer translation's search budget.
/-- error: source translation: maximum number (5) of search steps exceeded -/
#guard_msgs in
set_option source.maxSteps 5 in
example : HasProgram branches hole(⊢ program) (fun _ => 1) (fun _ => 1) := by
  fill_hole program in source_calls

example := (by source_calls : HasProgram branches _ _ _)

private opaque unavailable : Bool → Bool
private def twice (x : Bool) := unavailable (unavailable x)

@[local fun_prop] private theorem localScope {pu pt : Value → Code Value}
    (_h : ∀ _ : HasProgram unavailable pu (fun _ => 1) (fun _ => 1),
      HasProgram (fun x => unavailable (unavailable x)) pt (fun _ => 1) (fun _ => 1))
    (g : HasProgram (fun x => unavailable (unavailable x)) pt (fun _ => 1) (fun _ => 1)) :
    HasProgram twice pt (fun _ => 1) (fun _ => 1) := g

-- A temporary local callback cannot populate a sibling premise's cache.
example : True := by
  fail_if_success have := (by source_fun_prop : HasProgram twice _ _ _)
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
