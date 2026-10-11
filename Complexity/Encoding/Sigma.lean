/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Language.Derive

/-! # Structural encodings and source operations for dependent pairs

A dependent pair stores both fields. Decoding the first field determines the type of the second.
-/

public section

attribute [tree_encoding] Sigma
