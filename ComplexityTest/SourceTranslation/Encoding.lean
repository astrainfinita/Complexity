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
theorem hasProgram_trueOnly : HasProgram (fun b : {b : Bool // b = true} => b.val)
    (fun v => pure v) (fun _ => 0) (fun _ => 0) :=
  HasProgram.identity.map_input Subtype.val (fun _ => rfl)

example : ¬Function.Surjective (Subtype.val : {b : Bool // b = true} → Bool) := by
  rintro h
  obtain ⟨b, hb⟩ := h false
  exact Bool.noConfusion (b.property.symm.trans hb)

theorem hasProgram_sigmaIdentity :
    HasProgram (fun p : Bool × Unit => (⟨p.1, p.2⟩ : Σ _ : Bool, Unit)) (fun v => pure v)
      (fun _ => 0) (fun _ => 0) :=
  (HasProgram.identity (α := Bool × Unit)).of_encode
    (fun p => @Sigma.encode_mk Bool (fun _ => Unit) _ _ p.1 p.2)

-- Independent universes and arbitrary encoding instances remain supported.
universe u v w

example {α : Type u} {β : Type v} {γ : Type w}
    [UniqueEncoding Tree α] [UniqueEncoding Tree β] [UniqueEncoding Tree γ]
    {f : α → β} {pf : Value → Code Value} {t p : α → ℕ} (hf : HasProgram f pf t p) (o : β → γ)
    (ho : ∀ y, ⌜o y⌝ₜ = ⌜y⌝ₜ) : HasProgram (o ∘ f) pf t p :=
  hf.of_encode (g := f) (fun x => ho (f x))

-- Adding a logical output certificate preserves the behavior and both exact budgets.
example {Data α β : Type*} [Encoding Data α] [UniqueEncoding Data β]
    {model : TimeSpaceModel Id Data} {f : α → β} {t s : α → ℕ}
    (hf : model.ComputableWithin f t s) (P : β → Prop) (hP : ∀ x, P (f x)) :
    model.ComputableWithin (fun x => (⟨f x, hP x⟩ : {y // P y})) t s :=
  hf.of_encode (fun _ => rfl)

example {Data α β : Type*} [Encoding Data α] [UniqueEncoding Data β]
    {model : TimeSpaceModel Id Data} {f : α → β} {T S : ℕ → ℕ}
    (hf : f ∈ FTISP model T S) (P : β → Prop) (hP : ∀ x, P (f x)) :
    (fun x => (⟨f x, hP x⟩ : {y // P y})) ∈ FTISP model T S :=
  FTISP.of_encode hf (fun _ => rfl)

end ComplexityTest.SourceTranslation.Encoding
