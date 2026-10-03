/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Encoding.Composition
public import Complexity.Encoding.Tree
public import Complexity.Classes.TreeFunctions.Composition
public import Complexity.Classes.Functions.Encoding

/-!
# Polynomial compatibility of bit-string and tree encodings

The direct tree encoding and the bit-string encoding represented by `Tree.encodeBitList`
must admit polynomial-time conversions in both directions. Each conversion is
an identity computation on represented values, with different input and output
encodings. It must work on every valid input code and may return any valid code
of the same value. No canonical code or decidable decoder is required.

The witnesses are actual finite tree machines. In particular, this class makes
no assumption about equivalence between tree-machine and Turing-machine classes.
-/

@[expose] public section

namespace Complexity.Encoding

/-- The chosen bit-string and direct tree encodings admit polynomial-time
conversions on tree machines, using `Tree.encodeBitList` to store the bit strings. -/
class PolytimeCompatible (α : Type*) [e : Encoding (List Bool) α] [d : Encoding Tree α] :
    Prop where
  /-- Convert a bit-list tree into a direct tree code for the same value. -/
  fromBits : id ∈ @FP Tree α α (bitListEncoding.toEncoding.comp e) d .sizeCostTree
  /-- Convert any direct tree code into a bit-list tree for the same value. -/
  toBits : id ∈ @FP Tree α α d (bitListEncoding.toEncoding.comp e) .sizeCostTree

/-- Construct compatibility using polynomial-time functions on raw trees and
two equations on encodings. No change of encoding instances is needed at the call site. -/
theorem PolytimeCompatible.ofEncode {α : Type*}
    [e : UniqueEncoding (List Bool) α] [d : UniqueEncoding Tree α]
    {f g : Tree → Tree} (hf : f ∈ FP .sizeCostTree)
    (hg : g ∈ FP .sizeCostTree)
    (h : ∀ a : α, f (encode Tree (encode (List Bool) a)) = encode Tree a)
    (h' : ∀ a : α, g (encode Tree a) =
      encode Tree (encode (List Bool) a)) : PolytimeCompatible α where
  fromBits := @FP.of_encode Tree α α (bitListEncoding.comp e) d .sizeCostTree f id hf h
  toBits := @FP.of_encode Tree α α d (bitListEncoding.comp e) .sizeCostTree g id hg h'

/-- Using the list-tree representation directly requires no conversion.
This is an explicit witness for the specified encoding, not a global instance. -/
theorem PolytimeCompatible.ofComp {α : Type*} (e : Encoding (List Bool) α) :
    @PolytimeCompatible α e (bitListEncoding.toEncoding.comp e) :=
  @PolytimeCompatible.mk α e (bitListEncoding.toEncoding.comp e)
    (@TreeMachine.fp_id α (bitListEncoding.toEncoding.comp e))
    (@TreeMachine.fp_id α (bitListEncoding.toEncoding.comp e))

end Complexity.Encoding
