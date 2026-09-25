/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Complexity.Models.TreeMachine.Program.Scan
public import Complexity.Models.TuringMachine.Program.Specification.Trace

/-! # A configuration-only contract for the prefix scanner -/

@[expose] public section

namespace Complexity.TreeMachine.Program

open TM TM.Program Std.WP

variable {κ : Type} [DecidableEq κ] {zs : Array (Option Bool)}

private theorem balance_bounds (bs : List Bool) :
    -(bs.length : ℤ) ≤ BitList.balance bs ∧ BitList.balance bs ≤ bs.length := by
  induction bs with
  | nil => simp
  | cons b bs ih => cases b <;> simp only [List.length_cons, Nat.cast_add, Nat.cast_one,
      BitList.balance_cons_false, BitList.balance_cons_true] <;> omega

/-- Scan one tree prefix, retaining the complete final tapes and unused time credits.

The detailed scanner uses bounds containing all prefix configurations.
Callers need no resource-history assertions.
-/
@[spec]
theorem spec_scan_cfg (u : Cfg κ (Option Bool) Unit zs) (s d c : κ) (copy : Bool)
    (a : Tree) (xs ys ws : List (Option Bool)) (q : ℕ)
    (hs : s ≠ d) (hc : c ≠ s) (hd : c ≠ d)
    (hx : u.workTapes s = IntMemory.ofList (xs ++ code a ++ ws))
    (hy : u.workTapes d = IntMemory.ofList ys)
    (hz : u.workTapes c = IntMemory.ofList [some true])
    (hp : u.workPos s = xs.length) (hi : u.workPos d = ys.length) (hj : u.workPos c = 1) :
    Triple ((scan s d c copy).verify (cfgSemantics zs))
      (fun v b ↦ v = u ∧ b = 4 * a.size + q)
      (fun _ v b ↦ v = scanCfg u s d c copy a xs.length ys a.size ∧ b = q) () := by
  let L : κ → ℤ := fun i ↦ min (u.workPos i) (-(a.size : ℤ))
  let R : κ → ℤ := fun i ↦ max (u.workPos i) (xs.length + ys.length + a.size + 1)
  have hF : ScanFootprint u s d c copy a xs.length ys L R := by
    intro n hn i
    have hb := balance_bounds ((BitList.encodeTree a).take n)
    simp only [List.length_take, BitList.length_encodeTree] at hb
    simp only [scanCfg_workPos, scanWord, L, R, Set.mem_Icc]
    split_ifs <;> (try simp only [List.length_append, List.length_take, length_code]) <;>
      constructor <;> omega
  apply cfg_of_trace (spec_scan u s d c copy a xs ys ws L R q hs hc hd hx hy hz hp hi hj hF)
  · rintro v b ⟨hv, hb⟩
    subst v
    refine ⟨rfl, ?_, hb⟩
    intro i
    simpa only [Cfg.track_visited, NonemptyInterval.pure, Set.mem_Icc,
      scanCfg_zero u s d c copy a xs.length ys hy hp hi hj] using hF 0 (by omega) i
  · intro r v b h
    exact ⟨h.1, h.2.2⟩

end Complexity.TreeMachine.Program
