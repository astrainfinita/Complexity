/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import ComplexityTest.SourceTranslation.Asymptotics

@[expose] public section

open Complexity TreeProgram.Source

namespace ComplexityTest.SourceTranslation.GrowthConflictRight

@[source_growth] theorem specification : Asymptotics.importConflictImplementation.HasGrowth
    (fun _ => 1) (fun _ => 1) := by
  source_fun_prop
  all_goals exact Dominated.zero

end ComplexityTest.SourceTranslation.GrowthConflictRight
