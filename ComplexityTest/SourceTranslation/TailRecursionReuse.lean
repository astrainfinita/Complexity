/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import ComplexityTest.SourceTranslation.TailRecursion

@[expose] public section

open Complexity
open ComplexityTest.SourceTranslation.TailRecursion

-- Importing the saved model restores its selected program and public allowance.
example : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace keep
    (fun _ => 11) (fun n => k * (n + 2)) := by model_fun_prop

example : True := by
  fail_if_success
    have : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace keep
        (fun _ => 4) (fun n => k * (n + 2)) := by model_fun_prop
  trivial

def optionalGather : Option (Bool × List (List Bool) × List Bool) → List Bool
  | none => []
  | some x => gather x

example : ∃ k, TimeSpaceModel.tree.ComputableInTimeAndSpace optionalGather
    (fun n => 400 * n + 400) (fun n => k * (30 * n + 30)) := by
  model_fun_prop
