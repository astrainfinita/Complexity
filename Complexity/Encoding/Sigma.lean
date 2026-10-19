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

open Complexity in
theorem Sigma.size_encode_eq {α : Type*} {β : α → Type*} [UniqueEncoding Tree α]
    [∀ a, UniqueEncoding Tree (β a)] (x : Σ a, β a) :
    ⌜x⌝ₜ.size = 1 + ⌜x.1⌝ₜ.size + ⌜x.2⌝ₜ.size := rfl
