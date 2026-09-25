/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Control.Program.Syntax
public import Complexity.Data.FinEnum

/-! # Optional numbering at an external call boundary

Ordinary compilation keeps native state and exit labels. Import this module when another
program calls the compiled controller. Dependent sums use arithmetic branch offsets rather
than lists of every label, but computing their sizes still traverses their finite branches.

For proofs using only finiteness, `Syntax` already supplies `Finite p.State` and
`Finite p.Exit`. A proof needing a cardinality may locally install
`letI : Fintype p.State := Fintype.ofFinite p.State` (likewise for `p.Exit`).
This classical enumeration is separate from the computable `FinEnum` instances below.
-/

@[expose] public section

namespace Complexity.Program.Syntax

variable {O A Op α : Type} {Ret : Op → Type}

/-- Number internal labels when importing a compiled program. -/
@[instance_reducible] def enumState [∀ o, FinEnum (Ret o)] : {u : Kind} →
    (p : Syntax O A Op Ret α u) → FinEnum p.State
  | _, .ret _ => inferInstanceAs (FinEnum PEmpty)
  | _, .step o k =>
    letI := fun x ↦ enumState (k x)
    inferInstanceAs (FinEnum (PUnit ⊕ ((x : Ret o) × State (k x))))
  | _, .loop (n := n) (r := r) _ _ body k =>
    letI := fun i ↦ enumState (body i)
    letI := fun j ↦ enumState (k j)
    inferInstanceAs (FinEnum (Fin n ⊕ (((i : Fin n) × State (body i)) ⊕
      ((j : Fin r) × State (k j)))))
  | _, .call (c := c) (d := d) _ k =>
    letI := fun j ↦ enumState (k j)
    inferInstanceAs (FinEnum (Fin c ⊕ ((j : Fin d) × State (k j))))

/-- Number exit labels when importing a compiled program. -/
@[instance_reducible] def enumExit [∀ o, FinEnum (Ret o)] : {u : Kind} →
    (p : Syntax O A Op Ret α u) → FinEnum p.Exit
  | _, .ret _ => inferInstanceAs (FinEnum PUnit)
  | _, .step o k =>
    letI := fun x ↦ enumExit (k x)
    inferInstanceAs (FinEnum ((x : Ret o) × Exit (k x)))
  | _, .loop (r := r) _ _ _ k =>
    letI := fun j ↦ enumExit (k j)
    inferInstanceAs (FinEnum ((j : Fin r) × Exit (k j)))
  | _, .call (d := d) _ k =>
    letI := fun j ↦ enumExit (k j)
    inferInstanceAs (FinEnum ((j : Fin d) × Exit (k j)))

attribute [instance] enumState enumExit

end Complexity.Program.Syntax
