/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Complexity.Tactic.TreeProgram.Library

noncomputable section

open Complexity TreeProgram Complexity.TreeProgram.Source
open Complexity.TreeProgram.Source.Internal (HasProgramInO)
namespace ComplexityTest.SourceTranslation.Search

section Composition

-- Selected callbacks compose their growths without choosing new programs.
example (f g : Bool → Bool) {pf pg : Value → Code Value} {t p u q : Bool → ℕ}
    (_hf : HasProgramInO f pf t p) (_hg : HasProgramInO g pg u q) :
    HasProgramInO (fun x => g (f x)) (fun v => pf v >>= pg) (fun x => t x + u (f x))
      (fun x => max (p x) (q (f x))) := by
  source_fun_prop

-- Let sharing keeps the input and pays for the callback once.
example (f : Bool → Bool) (g : Bool × Bool → Bool) {pf pg : Value → Code Value}
    {t p : Bool → ℕ} {u q : Bool × Bool → ℕ} (_hf : HasProgramInO f pf t p)
    (_hg : HasProgramInO g pg u q) :
    HasProgramInO (fun x => let y := f x; g (x, y)) hole(pf, pg ⊢ program)
      (fun x => 0 + (t x + 1) + u (x, f x))
      (fun x => max (max 0 (max (p x) ⌜(x, f x)⌝ₜ.size)) (q (x, f x))) := by
  fill_hole program in source_fun_prop

end Composition

section CandidateFailure

private def unsupported : List Bool → List Bool
  | [] => []
  | x :: xs => unsupported xs ++ [x]

private def chosen (xs : List Bool) := xs.reverse

private theorem hasProgramInO_available :
    HasProgramInO chosen hole(⊢ program) (fun xs => ⌜xs⌝ₜ.size) (fun xs => ⌜xs⌝ₜ.size) := by
  abstract_hole program using programAvailable
  fill_hole program in
    exact List.hasProgramIn_reverse.toHasProgramInO

private theorem needsRecursive {program : Value → Code Value}
    (_h : HasProgramInO unsupported program (fun _ => 1) (fun _ => 1)) :
    HasProgramInO chosen programAvailable (fun xs => ⌜xs⌝ₜ.size) (fun xs => ⌜xs⌝ₜ.size) :=
  hasProgramInO_available

-- A failed implementation premise is rolled back before another implementation rule is tried.
attribute [local fun_prop] hasProgramInO_available needsRecursive

example := (by source_fun_prop : HasProgramInO chosen programAvailable _ _)

end CandidateFailure

private def uncertified : List Bool → List Bool
  | [] => []
  | b :: bs => b :: b :: uncertified bs

-- Encoded results report the unsupported source operation, not its encoder.
/--
error: source translation: `ComplexityTest.SourceTranslation.Search.uncertified` needs a registered implementation (choose replacement source with `via`, or register a function equality with `[program]`)
source path: fun xs => ⌜uncertified xs⌝ₜ → fun xs => uncertified xs
-/
#guard_msgs in
example : HasProgramInO (fun xs => ⌜uncertified xs⌝ₜ) hole(⊢ program) (fun _ => 1)
    (fun _ => 1) := by
  fill_hole program in source_fun_prop

section LocalPriority

-- A uniform chosen implementation is reusable at each runtime iteration.
example (f : Bool → Bool) {pf : Value → Code Value} {t p : Bool → ℕ}
    (_callback : HasProgramInO f pf t p) :
    HasProgramInO (fun x : ℕ × Bool => f^[x.1] x.2) hole(pf ⊢ program)
      (fun x => iterateTime f t x.1 x.2 + 1) (fun x => iteratePeak f p x.1 x.2) := by
  fill_hole program in source_fun_prop

-- Local selection takes precedence over a registered default.
example {program : Value → Code Value} {t p : List Bool → ℕ}
    (_h : HasProgramInO (List.reverse : List Bool → List Bool) program t p) :
    HasProgramInO (List.reverse : List Bool → List Bool) program t p := by
  source_fun_prop

private def alternative (xs : List Bool) := xs.reverse

@[local fun_prop] private theorem hasProgramInO_default :
    HasProgramInO alternative hole(⊢ program) (fun xs => ⌜xs⌝ₜ.size) (fun xs => ⌜xs⌝ₜ.size) := by
  abstract_hole program using programDefault
  fill_hole program in
    exact List.hasProgramIn_reverse.toHasProgramInO.congr rfl

example {program : Value → Code Value} {t p : List Bool → ℕ}
    (_selected : HasProgramInO alternative program t p) :
    HasProgramInO alternative program t p := by
  source_fun_prop

example {program : Value → Code Value} {t p : Bool → ℕ}
    (_selected : HasProgramInO (id : Bool → Bool) program t p) :
    HasProgramInO (id : Bool → Bool) program t p := by
  source_fun_prop

example {program : Value → Code Value} {t p : Bool → ℕ}
    (_selected : HasProgramInO (fun _ : Bool => ()) program t p) :
    HasProgramInO (fun _ : Bool => ()) program t p := by
  source_fun_prop

private def doubleReverse (xs : List Bool) := xs.reverse.reverse

@[local fun_prop] private theorem hasProgramInO_doubleReverseDefault :
    HasProgramInO doubleReverse hole(⊢ program)
    (fun xs => ⌜xs⌝ₜ.size + ⌜xs.reverse⌝ₜ.size) (fun xs => max ⌜xs⌝ₜ.size ⌜xs.reverse⌝ₜ.size) := by
  abstract_hole program using programDoubleReverseDefault
  fill_hole program in
    exact List.hasProgramIn_reverse.toHasProgramInO.comp List.hasProgramIn_reverse.toHasProgramInO

-- A semantic equality can expressly select a faster program; growth search never does so.
example := (by
    have _selected : HasProgramInO doubleReverse (fun v => pure v) (fun _ => 0) (fun _ => 0) :=
      HasProgramInO.identity.congr (by
        funext xs
        exact (List.reverse_reverse xs).symm)
    source_fun_prop : HasProgramInO doubleReverse (fun v => pure v) _ _)

example := (by source_fun_prop : HasProgramInO doubleReverse programDoubleReverseDefault _ _)

private def duplicate (x : Bool) : Bool × Bool := (x, x)

-- A definition whose value is a constructor is assembled only without a selected implementation:
-- inside a tuple, a constructor or a branch, the selected one is used.
example {program : Value → Code Value} {t p : Bool → ℕ}
    (_selected : HasProgramInO duplicate program t p) :=
  (by source_fun_prop : HasProgramInO (fun x => (duplicate x, x))
    (fun v => do let w ← program v; let z ← pure v; w.pair z) _ _)

example {program : Value → Code Value} {t p : Bool → ℕ}
    (_selected : HasProgramInO duplicate program t p) :=
  (by source_fun_prop : HasProgramInO (fun x => some (duplicate x))
    (fun v => do let w ← program v; Code.eval ((Expr.ofTree ⌜()⌝ₜ).pair w.expression)) _ _)

private def duplicateBranch (x : Bool × Bool) :=
  match x.1 with | true => (duplicate x.2, x.1) | false => ((x.2, x.2), x.1)

-- Assembled in one step, the branch takes constant time; with the selected implementation, its
-- time `t` is charged and no constant bounds it.
example : ∃ q u, HasProgramInO duplicateBranch q (fun _ => 1) u := by
  refine ⟨?q, ?u, ?h⟩
  case h =>
    source_fun_prop

example {program : Value → Code Value} {t p : Bool → ℕ}
    (_selected : HasProgramInO duplicate program t p) : True := by
  fail_if_success
    have : ∃ q u, HasProgramInO duplicateBranch q (fun _ => 1) u := by
      refine ⟨?q, ?u, ?h⟩
      case h =>
        source_fun_prop
        done
  trivial

end LocalPriority

section RuleStages

private def stored (x : Bool × Bool) : Bool := x.1

private theorem hasProgramInO_rebuilt : HasProgramInO stored hole(⊢ program)
    (fun _ => 1 + (1 + 1) + 1)
    (fun x => max (max ⌜x⌝ₜ.size (max ⌜x⌝ₜ.size ⌜(x.1, x.2)⌝ₜ.size)) ⌜(x.1, x.2)⌝ₜ.size) := by
  abstract_hole program using programRebuilt
  fill_hole program in
    exact (Prod.hasProgramIn_fst.toHasProgramInO.pair Prod.hasProgramIn_snd.toHasProgramInO).comp
      Prod.hasProgramIn_fst.toHasProgramInO

private alias hasProgramInO_preferred := hasProgramInO_rebuilt
private theorem hasProgramInO_secondary :
    HasProgramInO stored hole(⊢ program) (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programSecondary
  fill_hole program in
    exact Prod.hasProgramIn_fst.toHasProgramInO
private theorem hasProgramInO_fallback :
    HasProgramInO stored hole(⊢ program) (fun _ => 1) (fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programFallback
  fill_hole program in
    exact Prod.hasProgramIn_fst.toHasProgramInO

attribute [local source_fallback] hasProgramInO_fallback

open Lean Meta Mathlib.Meta.FunProp in
run_elab do
  addTheorem ``hasProgramInO_preferred .local 20
  addTheorem ``hasProgramInO_secondary .local 10
  addTheorem ``hasProgramInO_fallback .local 2000

-- Ordinary registered rules precede structural projection, independent of their numeric cost.
example := (by source_fun_prop : HasProgramInO stored programRebuilt _ _)

example : (programRebuilt Value.input).build 1 |>.2.1 ≠
    ((programSecondary Value.input).build 1).2.1 := by decide

section
attribute [local source_fallback] hasProgramInO_preferred hasProgramInO_secondary

-- Fallback rules do not displace a structural projection.
example := (by source_fun_prop : HasProgramInO stored Value.left _ _)
end

end RuleStages

section SharedSession

private def branches (x : Bool × List Bool) : List Bool :=
  if x.1 then x.2.reverse else x.2

-- Branch callbacks share the outer translation's search budget.
/-- error: source translation: maximum number (5) of search steps exceeded -/
#guard_msgs in
set_option source.maxSteps 5 in
example : HasProgramInO branches hole(⊢ program) (fun _ => 1) (fun _ => 1) := by
  fill_hole program in source_fun_prop

example := (by source_fun_prop : HasProgramInO branches _ _ _)

private opaque unavailable : Bool → Bool
private def twice (x : Bool) := unavailable (unavailable x)

@[local fun_prop] private theorem localScope {pu pt : Value → Code Value}
    (_h : ∀ _ : HasProgramInO unavailable pu (fun _ => 1) (fun _ => 1),
      HasProgramInO (fun x => unavailable (unavailable x)) pt (fun _ => 1) (fun _ => 1))
    (g : HasProgramInO (fun x => unavailable (unavailable x)) pt (fun _ => 1) (fun _ => 1)) :
    HasProgramInO twice pt (fun _ => 1) (fun _ => 1) := g

-- A temporary local callback cannot populate a sibling premise's cache.
example : True := by
  fail_if_success have := (by source_fun_prop : HasProgramInO twice _ _ _)
  trivial

end SharedSession

end ComplexityTest.SourceTranslation.Search
