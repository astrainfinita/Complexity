/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Problems.KSAT.Verifier
public import Complexity.Data.CNF.TreeEncoding
public import Complexity.Encoding.Nat
public import Complexity.Tactic.TreeProgram.Library
public import Complexity.Classes.Functions.Encoding
public import Complexity.Classes.TreeFunctions.UnitTime
public import Complexity.Classes.TreeFunctions.Composition

/-! # A polynomial-time tree program for the sparse `k`-SAT verifier

The program checks every clause for a satisfied literal, looking each variable up by scanning the
witness list and comparing binary numbers. Its time is polynomial in the code of the formula and
the witness, and its peak linear. The formula is evaluated under the assignment as a callback, by
the rule `HasProgramInO.cnfEval`.
-/

@[expose] public section

open Complexity TreeProgram

namespace Complexity.TreeProgram.Source

open Internal (HasProgramInO)

/-- Evaluate a formula under an assignment computed by a callback, which may capture the
environment, as for `HasProgramInO.map_with`: an assignment is a function, which has no code. Every
clause is checked for a satisfied literal, calling the callback at the variable of each literal;
time sums the callback over the literals, and the peak is the largest callback peak. -/
theorem Internal.HasProgramInO.cnfEval {ρ α : Type*} [UniqueEncoding Tree ρ]
    [UniqueEncoding Tree α] {f : ρ → CNF α} {x : ρ → α → Bool} {qi qx : Value → Code Value}
    {ti pi : ρ → ℕ} {tx px : ρ × α → ℕ} (hi : HasProgramInO (fun e => (e, f e)) qi ti pi)
    (hx : HasProgramInO (fun z : ρ × α => x z.1 z.2) qx tx px) :
    HasProgramInO (fun e => (f e).eval (x e)) hole(qi, qx ⊢ program)
      (fun e => ti e + ((f e).map fun c => (c.map fun l => tx (e, l.atom)).sum).sum + ⌜f e⌝ₜ.size)
      (fun e => max (pi e) (max ⌜(e, f e)⌝ₜ.size
        ((f e).foldr (fun c s => max (c.foldr (fun l s => max (px (e, l.atom)) s) 0) s) 0))) := by
  -- The bodies of `CNF.eval` and `CNF.Literal.eval`, unfolded only in this proof.
  have h := (by source_fun_prop : HasProgramInO
    (fun z : ρ × CNF α => z.2.all fun c => c.any fun l => x z.1 l.atom == l.polarity) _ _ _)
  fill_hole program in refine (hi.comp h).mono ?_ ?_
  -- Sums and maxima over the clauses and literals are split into their parts; the part with the
  -- callback is then the one stated, and the rest is bounded by the code of the formula.
  · simp only [List.sum_map_add]
    dominated
  · simp only [foldr_max_max]
    dominated

attribute [fun_prop] HasProgramInO.cnfEval

end Complexity.TreeProgram.Source

namespace Complexity.KSAT

open TreeProgram.Source

/-- The verifier checks clauses and literals, scanning the witness at every literal: time
polynomial in the code of the formula and the witness, and a linear peak. -/
@[program] theorem hasProgramIn_verify (k : ℕ) : HasProgramIn (verify k) hole(⊢ program)
    (IsPoly fun x => ⌜x⌝ₜ.size) IsO(fun x => ⌜x⌝ₜ.size) := by
  abstract_hole program using programVerify
  fill_hole program in source_fun_prop

/-- The verifier is polynomial-time in the size-charged tree model. -/
theorem verify_fp (k : ℕ) : verify k ∈ FP .sizeCostTree := by
  model_fun_prop

end Complexity.KSAT
