/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.ModelTheory.Algebra.BooleanAlgebra.Basic
public import Complexity.Encoding.Sigma
public import Complexity.Encoding.Nat

/-! # Structural encodings and source operations for Boolean gates

Constructor tags are shared across arities. The decoder rejects a gate of the wrong arity.
-/

public section

namespace FirstOrder.BooleanAlgebra

tree_encoding Language.booleanAlgebra.Functions

end FirstOrder.BooleanAlgebra
