/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Tactic.TreeProgram.Match
public import Complexity.Tactic.TreeProgram.Rules
public import Complexity.Models.Circuit.TreeEncoding

/-! # Translation rules for circuit constructors and matchers

Programs build circuits as `Circuit.outputs v.get` and `Circuit.gate op v.get next` for a
`FinVector` `v`, and match on circuits with `Circuit.casesFinVector`, `casesFinVectorOutputs` and
`casesFinVectorGate`. The rules here translate exactly these forms: their subgoals compute
`FinVector`s, arities, operation symbols and circuits, never a function `Fin k → Fin n`. A circuit
built from another function, and a `match` on a circuit, have no rule.
-/

@[expose] public section

open Complexity TreeProgram FirstOrder

namespace Complexity.TreeProgram.Source

open Internal (HasProgramInO)

variable {α : Type*} [UniqueEncoding Tree α] {L : Language}
  [∀ k, UniqueEncoding Tree (L.Functions k)] {n m : α → ℕ}

/-- A circuit of outputs read through a computed `FinVector`: its code is the `FinVector`'s code
after a tag. -/
theorem Internal.HasProgramInO.circuitOutputs {v : (x : α) → FinVector (Fin (n x)) (m x)}
    {q : Value → Code Value} {t p : α → ℕ} (h : HasProgramInO v q t p) :
    HasProgramInO (fun x => (Circuit.outputs (v x).get : Circuit L (n x) (m x))) hole(q ⊢ program)
      (fun x => t x + 1) (fun x => max (p x)
        ⌜(Circuit.outputs (v x).get : Circuit L (n x) (m x))⌝ₜ.size) := by
  fill_hole program in exact HasProgramInO.of_tagged_fields .nil (fun _ => rfl) h.with_size

attribute [fun_prop] HasProgramInO.circuitOutputs

/-- A gate on a computed `FinVector` of input wires: its code is the tuple of its arity, symbol,
wires and continuation after a tag. -/
theorem Internal.HasProgramInO.circuitGate {k : α → ℕ} {op : (x : α) → L.Functions (k x)}
    {v : (x : α) → FinVector (Fin (n x)) (k x)} {next : (x : α) → Circuit L (n x + 1) (m x)}
    {qk qs qv qn : Value → Code Value} {tk pk ts ps tv pv tn pn : α → ℕ}
    (hk : HasProgramInO k qk tk pk) (hs : HasProgramInO op qs ts ps)
    (hv : HasProgramInO v qv tv pv) (hn : HasProgramInO next qn tn pn) :
    HasProgramInO (fun x => Circuit.gate (op x) (v x).get (next x)) hole(qk, qs, qv, qn ⊢ program)
      (fun x => tk x + ts x + tv x + tn x + 4)
      (fun x => max (max (pk x) (max (ps x) (max (pv x) (pn x))))
        ⌜Circuit.gate (op x) (v x).get (next x)⌝ₜ.size) := by
  fill_hole program in
    refine (HasProgramInO.of_tagged_fields (.pair .nil .nil) (fun _ => rfl)
      (hk.field_cons (hs.field_cons (hv.field_cons hn.with_size)))).mono
      (Dominated.of_le fun x => le_of_eq ?_) (.refl _)
  omega

attribute [fun_prop] HasProgramInO.circuitGate

variable {β : α → Type*} [∀ x, UniqueEncoding Tree (β x)] {d : (x : α) → Circuit L (n x) (m x)}
  {qd : Value → Code Value} {td pd : α → ℕ}

/-- A match on a computed circuit by `casesFinVector`: each branch receives the input with the
fields of its constructor, the wire table as a `FinVector`. -/
theorem Internal.HasProgramInO.circuitCasesFinVector
    {fo : (x : α) → (v : FinVector (Fin (n x)) (m x)) → d x = .outputs v.get → β x}
    {fg : (x : α) → {k : ℕ} → (op : L.Functions k) → (v : FinVector (Fin (n x)) k) →
      (next : Circuit L (n x + 1) (m x)) → d x = .gate op v.get next → β x}
    {qo qg : Value → Code Value}
    {tOut pOut : {y : Σ x, FinVector (Fin (n x)) (m x) // d y.1 = .outputs y.2.get} → ℕ}
    {tGate pGate : {y : Σ x, Σ k, L.Functions k × FinVector (Fin (n x)) k ×
      Circuit L (n x + 1) (m x) // d y.1 = .gate y.2.2.1 y.2.2.2.1.get y.2.2.2.2} → ℕ}
    (hd : HasProgramInO d qd td pd)
    (ho : HasProgramInO (fun y : {y : Σ x, FinVector (Fin (n x)) (m x) //
      d y.1 = .outputs y.2.get} => fo y.1.1 y.1.2 y.2) qo tOut pOut)
    (hg : HasProgramInO (fun y : {y : Σ x, Σ k, L.Functions k × FinVector (Fin (n x)) k ×
      Circuit L (n x + 1) (m x) // d y.1 = .gate y.2.2.1 y.2.2.2.1.get y.2.2.2.2} =>
      fg y.1.1 y.1.2.2.1 y.1.2.2.2.1 y.1.2.2.2.2 y.2) qg tGate pGate) :
    HasProgramInO (fun x => (d x).casesFinVector (fo x) (fg x)) hole(qd, qo, qg ⊢ program)
      (fun x => td x + (d x).casesFinVector (fun v h => tOut ⟨⟨x, v⟩, h⟩)
        (fun op v next h => tGate ⟨⟨x, _, op, v, next⟩, h⟩) + 1)
      (fun x => max (pd x) ((d x).casesFinVector
        (fun v h => max (1 + ⌜x⌝ₜ.size + ⌜v⌝ₜ.size) (pOut ⟨⟨x, v⟩, h⟩))
        (fun op v next h => max (1 + ⌜x⌝ₜ.size + ⌜(⟨_, op, v, next⟩ : Σ k, L.Functions k ×
          FinVector (Fin (n x)) k × Circuit L (n x + 1) (m x))⌝ₜ.size)
          (pGate ⟨⟨x, _, op, v, next⟩, h⟩)))) := by
  let _ : ∀ x, CaseView (Circuit L (n x) (m x)) 2 := fun _ => Circuit.caseView
  have h0 : HasProgramInO (fun y : CaseView.Branch d 0 => (d y.1.1).casesFinVector (fo y.1.1)
      (fg y.1.1)) qo (fun y => tOut ⟨⟨y.1.1, ULift.down y.1.2⟩, y.2⟩)
      (fun y => pOut ⟨⟨y.1.1, ULift.down y.1.2⟩, y.2⟩) :=
    (ho.map_input (fun y : CaseView.Branch d 0 => ⟨⟨y.1.1, ULift.down y.1.2⟩, y.2⟩)
      fun _ => rfl).congr <| funext fun y => (Circuit.casesFinVector_of_eq_outputs _ _ y.2).symm
  have h1 : HasProgramInO (fun y : CaseView.Branch d 1 => (d y.1.1).casesFinVector (fo y.1.1)
      (fg y.1.1)) qg (fun y => tGate ⟨y.1, y.2⟩) (fun y => pGate ⟨y.1, y.2⟩) :=
    (hg.map_input (fun y : CaseView.Branch d 1 => ⟨y.1, y.2⟩) fun _ => rfl).congr <|
      funext fun y => (Circuit.casesFinVector_of_eq_gate _ _ y.2).symm
  fill_hole program in
    refine HasProgramInO.cases (T := fun x => Circuit L (n x) (m x)) (k := 2) (d := d)
      (f := fun x => (d x).casesFinVector (fo x) (fg x))
      (q := fun i => Fin.cases qo (fun _ => qg) i)
      (t := fun i => Fin.cases (motive := fun i => CaseView.Branch d i → ℕ)
        (fun y => tOut ⟨⟨y.1.1, ULift.down y.1.2⟩, y.2⟩)
        (fun j => Fin.cases (fun y => tGate ⟨y.1, y.2⟩) (fun j => j.elim0) j) i)
      (p := fun i => Fin.cases (motive := fun i => CaseView.Branch d i → ℕ)
        (fun y => pOut ⟨⟨y.1.1, ULift.down y.1.2⟩, y.2⟩)
        (fun j => Fin.cases (fun y => pGate ⟨y.1, y.2⟩) (fun j => j.elim0) j) i)
      _ (fun _ => rfl) hd ?_
  intro i
  match i with
  | 0 => exact h0
  | 1 => exact h1

attribute [fun_prop] HasProgramInO.circuitCasesFinVector

/-- A match by `casesFinVectorOutputs` on a computed circuit that is not a gate. -/
theorem Internal.HasProgramInO.circuitCasesFinVectorOutputs
    {fo : (x : α) → (v : FinVector (Fin (n x)) (m x)) → d x = .outputs v.get → β x}
    {notGate : ∀ x {k : ℕ} (op : L.Functions k) (v : FinVector (Fin (n x)) k)
      (next : Circuit L (n x + 1) (m x)), d x = .gate op v.get next → False}
    {qo : Value → Code Value}
    {tOut pOut : {y : Σ x, FinVector (Fin (n x)) (m x) // d y.1 = .outputs y.2.get} → ℕ}
    (hd : HasProgramInO d qd td pd)
    (ho : HasProgramInO (fun y : {y : Σ x, FinVector (Fin (n x)) (m x) //
      d y.1 = .outputs y.2.get} => fo y.1.1 y.1.2 y.2) qo tOut pOut) :
    HasProgramInO (fun x => (d x).casesFinVectorOutputs (fo x) (notGate x))
      hole(qd, qo ⊢ program)
      (fun x => td x + (d x).casesFinVector (fun v h => tOut ⟨⟨x, v⟩, h⟩) (fun _ _ _ _ => 0) + 1)
      (fun x => max (pd x) ((d x).casesFinVector
        (fun v h => max (1 + ⌜x⌝ₜ.size + ⌜v⌝ₜ.size) (pOut ⟨⟨x, v⟩, h⟩)) (fun _ _ _ _ => 0))) := by
  fill_hole program in
    refine (circuitCasesFinVector hd ho (HasProgramInO.of_false fun y =>
      notGate _ _ _ _ y.2)).mono (.refl _) (Dominated.of_le fun x => ?_)
  obtain ⟨i, p, hp⟩ := CaseView.exists_ofPayload (self := Circuit.caseView) (d x)
  match i, p, hp with
  | 0, ⟨_⟩, hp =>
    rw [Circuit.casesFinVector_of_eq_outputs _ _ hp.symm,
      Circuit.casesFinVector_of_eq_outputs _ _ hp.symm]
  | 1, ⟨_, _, _, _⟩, hp => exact (notGate x _ _ _ hp.symm).elim

attribute [fun_prop] HasProgramInO.circuitCasesFinVectorOutputs

/-- A match by `casesFinVectorGate` on a computed circuit that is a gate. -/
theorem Internal.HasProgramInO.circuitCasesFinVectorGate
    {notOutputs : ∀ x (v : FinVector (Fin (n x)) (m x)), d x = .outputs v.get → False}
    {fg : (x : α) → {k : ℕ} → (op : L.Functions k) → (v : FinVector (Fin (n x)) k) →
      (next : Circuit L (n x + 1) (m x)) → d x = .gate op v.get next → β x}
    {qg : Value → Code Value}
    {tGate pGate : {y : Σ x, Σ k, L.Functions k × FinVector (Fin (n x)) k ×
      Circuit L (n x + 1) (m x) // d y.1 = .gate y.2.2.1 y.2.2.2.1.get y.2.2.2.2} → ℕ}
    (hd : HasProgramInO d qd td pd)
    (hg : HasProgramInO (fun y : {y : Σ x, Σ k, L.Functions k × FinVector (Fin (n x)) k ×
      Circuit L (n x + 1) (m x) // d y.1 = .gate y.2.2.1 y.2.2.2.1.get y.2.2.2.2} =>
      fg y.1.1 y.1.2.2.1 y.1.2.2.2.1 y.1.2.2.2.2 y.2) qg tGate pGate) :
    HasProgramInO (fun x => (d x).casesFinVectorGate (notOutputs x) (fg x))
      hole(qd, qg ⊢ program)
      (fun x => td x + (d x).casesFinVector (fun _ _ => 0)
        (fun op v next h => tGate ⟨⟨x, _, op, v, next⟩, h⟩) + 1)
      (fun x => max (pd x) ((d x).casesFinVector (fun _ _ => 0)
        (fun op v next h => max (1 + ⌜x⌝ₜ.size + ⌜(⟨_, op, v, next⟩ : Σ k, L.Functions k ×
          FinVector (Fin (n x)) k × Circuit L (n x + 1) (m x))⌝ₜ.size)
          (pGate ⟨⟨x, _, op, v, next⟩, h⟩)))) := by
  fill_hole program in
    refine (circuitCasesFinVector hd (HasProgramInO.of_false fun y =>
      notOutputs _ _ y.2) hg).mono (.refl _) (Dominated.of_le fun x => ?_)
  obtain ⟨i, p, hp⟩ := CaseView.exists_ofPayload (self := Circuit.caseView) (d x)
  match i, p, hp with
  | 0, ⟨_⟩, hp => exact (notOutputs x _ hp.symm).elim
  | 1, ⟨_, _, _, _⟩, hp =>
    rw [Circuit.casesFinVector_of_eq_gate _ _ hp.symm,
      Circuit.casesFinVector_of_eq_gate _ _ hp.symm]

attribute [fun_prop] HasProgramInO.circuitCasesFinVectorGate

end Complexity.TreeProgram.Source
