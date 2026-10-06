/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.Circuit.Basic
public import Complexity.Models.TreeMachine.Language.Derive
public import Complexity.Encoding.Nat
public import Complexity.Encoding.Fin

/-! # Tree encodings and source operations for circuits

Input and output counts are supplied by the circuit type. A gate stores its arity,
operation symbol, input wires, and continuation, in that order.
-/

@[expose] public section

namespace Complexity

attribute [tree_encoding] Circuit

end Complexity
