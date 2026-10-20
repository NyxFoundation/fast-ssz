import NyxSszVerification.Gindex.Arithmetic

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace NyxSszVerification

@[step] theorem gindex_rebase_refines (index : U128) (depth : U32) :
    NyxSszRust.gindex.rebase index depth ⦃ actual =>
      gindexResultAgrees UScalar.val U128.max actual (.ok (Ssz.gindexRebase index.val depth.val)) ⦄ := by
  unfold NyxSszRust.gindex.rebase
  by_cases wide : depth >= 128#u32
  · have power : 2 ^ 128 ≤ 2 ^ depth.val := Nat.pow_le_pow_right Nat.zero_lt_two (by scalar_tac)
    simp only [if_pos wide, spec_ok, gindexResultAgrees, Ssz.gindexRebase]
    scalar_tac
  · have small : depth.val < 128 := by scalar_tac
    have bounded := gindex_power_small depth small
    have doubleBound : 2 ^ (depth.val + 1) ≤ 2 ^ 128 :=
      Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
    have remainderBound : index.val % 2 ^ depth.val < 2 ^ depth.val := Nat.mod_lt _ (by positivity)
    rw [Nat.pow_succ, Nat.mul_two] at doubleBound
    simp only [if_neg wide]
    step*
    all_goals simp_all [Ssz.gindexRebase, Ssz.gindexBelow, gindexResultAgrees,
      Nat.shiftLeft_eq, Nat.mod_eq_of_lt bounded]
    all_goals scalar_tac

end NyxSszVerification
