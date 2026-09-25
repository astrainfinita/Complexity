/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Classes.Time

/-!
# Polynomial-time decision problems

`P` is the decision class induced by `FP` with Boolean output. The output encoding
is fixed: exactly one bit, for either acceptance or rejection.

With partial input encodings this is a promise interpretation: every valid code
is covered and invalid codes impose no obligations. For ordinary bit-string
languages, the global identity encoding on `List Bool` is used by default.
No `DecidablePred` instance is required in the statement of membership.
-/

@[expose] public section

namespace Complexity

variable {α : Type*} [Encoding (List Bool) α]

/-- Predicates decidable in polynomial time on a finite-control deterministic
Turing machine, with a fixed singleton-bit Boolean output convention. -/
def P : Set (α → Prop) :=
  DecisionClass FP

namespace P

theorem of_decides {f : α → Bool} {p : α → Prop}
    (hf : f ∈ FP) (hp : Decides f p) : p ∈ P :=
  DecisionClass.of_decides hf hp

theorem congr {p q : α → Prop} (hp : p ∈ P) (h : ∀ a, p a ↔ q a) : q ∈ P :=
  DecisionClass.congr hp h

/-- The polynomial decision class is induced by the union of power-time function classes. -/
theorem eq_iUnion_dtime : P (α := α) = ⋃ d : ℕ, DTIME (fun n => n ^ d) :=
  DecisionClass.iUnion (fun d => FTIME (fun n => n ^ d))

/-- Polynomial time is the union of the parameterized power-time classes. -/
theorem mem_iff_exists_dtime {p : α → Prop} :
    p ∈ P ↔ ∃ d : ℕ, p ∈ DTIME (fun n => n ^ d) := by
  rw [eq_iUnion_dtime, Set.mem_iUnion]

end P

end Complexity
