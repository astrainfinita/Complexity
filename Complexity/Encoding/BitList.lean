/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Encoding.Basic

/-! # Bit strings as their own codes -/

@[expose] public section

namespace Complexity

/-- Raw bit strings use the identity encoding. -/
instance bitListSelfEncoding : UniqueEncoding (List Bool) (List Bool) :=
  UniqueEncoding.refl (List Bool)

@[simp] theorem BitList.encode_self (xs : List Bool) : encode (List Bool) xs = xs := rfl

@[simp] theorem BitList.decode_self (xs : List Bool) : decode (List Bool) xs = Part.some xs := rfl

end Complexity
