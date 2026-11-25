/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Problems.CircuitSAT.KSAT
public import Complexity.Problems.KSAT.Membership

/-! # Boolean circuit satisfiability is in NP

A witness for a circuit is a witness of the `3`-SAT verifier for its Tseitin formula; the verifier
on circuits is the reduction followed by the `3`-SAT verifier.
-/

@[expose] public section

namespace Complexity.CircuitSAT

/-- Boolean circuit satisfiability is in nondeterministic polynomial time. -/
theorem mem_np : CircuitSAT ∈ NP .ntm :=
  NP.of_verifier (TreeMachine.dom_decode_list_mem_p TreeMachine.dom_decode_nat_mem_p)
    (P.of_decides (f := fun x => KSAT.verify 3 (toKSAT x.1, x.2)) (by model_fun_prop)
      fun _ => Iff.rfl)
    (fun c => ⌜toKSAT c⌝ₜ.size) (by dominated)
    (fun c _ h => (toKSAT_correct c).2 (KSAT.verify_sound h)) fun c hc => by
      obtain ⟨w, hw, hv⟩ := (KSAT.exists_verify_iff _).1 ((toKSAT_correct c).1 hc)
      exact ⟨w, hw.size_encode_le.trans (toKSAT c).val.size_encode_atoms_le, hv⟩

end Complexity.CircuitSAT
