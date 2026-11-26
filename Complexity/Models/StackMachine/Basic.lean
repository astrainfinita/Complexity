/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.StackMachine.Configuration
public import Complexity.Control.Controller.Computation

/-!
# Multiple-stack machines with finite local observations

Also provides `StackMachine.OptionBool`, a two-bit encoding of `Option Bool` (presence bit and value
bit) shared by Boolean-stack tape simulation and run circuits.
-/

@[expose] public section

universe uκ u v

namespace Complexity

/-- A controller observing the input symbol and the top of each work stack. -/
abbrev StackMachine (F : Type (max uκ u v) → Type*)
    (κ : Type uκ) (Γ : Type u) (Q : Type v) :=
  Controller F (Option Γ × (κ → Option Γ)) (StackMachine.Action κ Γ) Q

namespace StackMachine

variable {κ : Type uκ} {Γ : Type u}

variable (κ) in
/-- The standard initial configuration on a list input: the input head on the first symbol,
empty work stacks, and no output. -/
@[simps -fullyApplied inputPos «stacks» output]
def Cfg.init (xs : List Γ) : Cfg κ Γ xs.toArray := ⟨1, fun _ ↦ [], #[]⟩

instance : Controller.HasConfig (Action κ Γ) (List Γ) (fun xs ↦ Cfg κ Γ xs.toArray) where
  init xs := Cfg.init κ xs

@[simp] theorem hasConfig_init (xs : List Γ) :
    Controller.HasConfig.init (Action κ Γ) xs = Cfg.init κ xs := rfl

/-- Input and output are ordinary symbol lists. -/
@[simps (attr := simp↓)]
instance hasOutput {xs : Array Γ} : Controller.HasOutput (Cfg κ Γ xs) (List Γ) where
  IsOutput c ys := c.output = ys.toArray

namespace OptionBool

/-- Represent `a : Option Bool` as two bits indexed by `isValue : Bool`: `false` records whether
`a` is present (`a.isSome`), and `true` records its value (`a.getD false`, defaulting to `false` on
`none`). -/
def toBits (a : Option Bool) (isValue : Bool) : Bool :=
  if isValue then a.getD false else a.isSome

/-- Recover `Option Bool` from its presence bit (`b false`) and value bit (`b true`); when
`b false = false`, the value bit is ignored and `none` is returned. -/
def ofBits (b : Bool → Bool) : Option Bool :=
  if b false then some (b true) else none

@[simp] theorem toBits_false (a : Option Bool) : toBits a false = a.isSome := rfl

@[simp] theorem toBits_true (a : Option Bool) : toBits a true = a.getD false := rfl

@[simp] theorem toBits_none (isValue : Bool) : toBits none isValue = false := by
  cases isValue <;> rfl

@[simp] theorem ofBits_toBits (a : Option Bool) : ofBits (toBits a) = a := by
  cases a <;> rfl

theorem toBits_injective : Function.Injective toBits :=
  Function.LeftInverse.injective ofBits_toBits

@[simp] theorem toBits_inj {a b : Option Bool} : toBits a = toBits b ↔ a = b :=
  toBits_injective.eq_iff

end OptionBool

end StackMachine

end Complexity
