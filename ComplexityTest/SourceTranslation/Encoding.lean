/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Complexity.Tactic.TreeProgram.Implementation
import Complexity.Encoding.Bool
import Complexity.Encoding.Sigma
import Complexity.Classes.Functions.Encoding

open Complexity TreeProgram TreeProgram.Source

namespace ComplexityTest.SourceTranslation.Encoding

-- The input map need not cover all inputs of the original implementation.
def trueOnly : Implementation (fun b : {b : Bool // b = true} => b.val) :=
  Implementation.identity.mapInput Subtype.val (fun _ => rfl)

example : ¬Function.Surjective (Subtype.val : {b : Bool // b = true} → Bool) := by
  rintro h
  obtain ⟨b, hb⟩ := h false
  exact Bool.noConfusion (b.property.symm.trans hb)

example : trueOnly.program = (Implementation.identity (α := Bool)).program := rfl

example : (trueOnly.evaluate ⟨true, rfl⟩).value = true := rfl

example : trueOnly.bounds = ⟨fun _ => 0, fun _ => 0⟩ := rfl

def sigmaIdentity : Implementation (fun p : Bool × Unit => (⟨p.1, p.2⟩ : Σ _ : Bool, Unit)) :=
  (Implementation.identity (α := Bool × Unit)).mapOutput
    (fun p => (⟨p.1, p.2⟩ : Σ _ : Bool, Unit))
    (fun p => @Sigma.encode_mk Bool (fun _ => Unit) _ _ p.1 p.2)

example : sigmaIdentity.program = (Implementation.identity (α := Bool × Unit)).program := rfl

example : sigmaIdentity.bounds = ⟨fun _ => 0, fun _ => 0⟩ := by
  simp only [sigmaIdentity, Implementation.bounds_mapOutput, Implementation.bounds_identity]

-- Independent universes and arbitrary encoding instances remain supported.
universe u v w

example {α : Type u} {β : Type v} {γ : Type w}
    [UniqueEncoding Tree α] [UniqueEncoding Tree β] [UniqueEncoding Tree γ]
    {f : α → β} (hf : Implementation f) (o : β → γ)
    (ho : ∀ y, ⌜o y⌝ₜ = ⌜y⌝ₜ) (x : α) :
    (hf.mapOutput o ho).evaluate x = Costed.bind (hf.evaluate x) (fun y => pure (o y)) := rfl

-- Adding a logical output certificate preserves the behavior and both exact budgets.
example {Data α β : Type*} [Encoding Data α] [UniqueEncoding Data β]
    {model : TimeSpaceModel Id Data} {f : α → β} {t s : ℕ → ℕ}
    (hf : model.ComputableInTimeAndSpace f t s) (P : β → Prop) (hP : ∀ x, P (f x)) :
    model.ComputableInTimeAndSpace (fun x => (⟨f x, hP x⟩ : {y // P y})) t s :=
  hf.of_encode (fun _ => rfl)

example {Data α β : Type*} [Encoding Data α] [UniqueEncoding Data β]
    {model : TimeSpaceModel Id Data} {f : α → β} {T S : ℕ → ℕ}
    (hf : f ∈ FTISP model T S) (P : β → Prop) (hP : ∀ x, P (f x)) :
    (fun x => (⟨f x, hP x⟩ : {y // P y})) ∈ FTISP model T S :=
  FTISP.of_encode hf (fun _ => rfl)

end ComplexityTest.SourceTranslation.Encoding
