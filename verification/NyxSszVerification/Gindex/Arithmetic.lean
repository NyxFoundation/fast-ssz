import NyxSszVerification.Gindex.Depth

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace NyxSszVerification

theorem gindex_word_eq {ty : UScalarTy} (left right : UScalar ty) :
    left = right ↔ left.val = right.val :=
  ⟨fun same => congrArg UScalar.val same, UScalar.eq_of_val_eq⟩

theorem gindex_power_covers (index : U128) (depth : Nat) (wide : 128 ≤ depth) :
    index.val < 2 ^ depth := by
  have wordBound : index.val < 2 ^ 128 := by scalar_tac
  exact lt_of_lt_of_le wordBound (Nat.pow_le_pow_right Nat.zero_lt_two wide)

theorem gindex_power_small (depth : U32) (small : depth.val < 128) :
    2 ^ depth.val < U128.size := by
  simpa [U128.size, U128.numBits] using Nat.pow_lt_pow_right Nat.one_lt_two small

@[step] theorem gindex_parent_refines (index : U128) :
    NyxSszRust.gindex.parent index ⦃ actual => actual.val = Ssz.gindexParent index.val ⦄ := by
  unfold NyxSszRust.gindex.parent
  step*
  simp_all [Ssz.gindexParent]

@[step] theorem gindex_sibling_refines (index : U128) :
    NyxSszRust.gindex.sibling index ⦃ actual => actual.val = Ssz.gindexSibling index.val ⦄ := by
  simp [NyxSszRust.gindex.sibling, Ssz.gindexSibling]

@[step] theorem gindex_bit_refines (index : U128) (position : U32) :
    NyxSszRust.gindex.bit index position ⦃ actual => actual = Ssz.gindexBit index.val position.val ⦄ := by
  unfold NyxSszRust.gindex.bit
  by_cases wide : position >= 128#u32
  · have covered := gindex_power_covers index position.val (by scalar_tac)
    simp [wide, Ssz.gindexBit, Nat.testBit_lt_two_pow covered]
  · simp only [wide, if_false]
    step*
    simp_all [Ssz.gindexBit, Nat.testBit_eq_decide_div_mod_eq,
      gindex_word_eq, Nat.shiftRight_eq_div_pow]

@[step] theorem gindex_below_refines (index : U128) (depth : U32) :
    NyxSszRust.gindex.below index depth ⦃ actual => actual.val = Ssz.gindexBelow index.val depth.val ⦄ := by
  unfold NyxSszRust.gindex.below
  by_cases wide : depth >= 128#u32
  · have covered := gindex_power_covers index depth.val (by scalar_tac)
    simp [wide, Ssz.gindexBelow, Nat.mod_eq_of_lt covered]
  · have small : depth.val < 128 := by scalar_tac
    have bounded := gindex_power_small depth small
    simp only [wide, if_false]
    step*
    all_goals simp_all [Ssz.gindexBelow, Nat.shiftLeft_eq, Nat.mod_eq_of_lt bounded]

end NyxSszVerification
