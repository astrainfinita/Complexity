/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Data.CNF.Basic
public import Complexity.Models.TreeMachine.Language.Derive

/-! # Tree representations and source operations for CNF literals

A literal is encoded as the pair of its variable code and its polarity code.
The existing list encoding then represents clauses and CNFs.
-/

@[expose] public section

namespace Complexity.CNF

attribute [tree_encoding] Literal

end Complexity.CNF
