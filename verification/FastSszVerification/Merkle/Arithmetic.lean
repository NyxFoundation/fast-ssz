import Aeneas
import Ssz.Merkle.Verify

open Aeneas Aeneas.Std

namespace FastSszVerification

theorem shift_one_iff_log2 (value depth : Nat) (nonzero : value ≠ 0) :
    value >>> depth = 1 ↔ depth = value.log2 := by
  rw [eq_comm (a := depth) (b := value.log2)]
  have positive : 0 < 2 ^ depth := Nat.pow_pos Nat.zero_lt_two
  rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_iff positive, Nat.log2_eq_iff nonzero]
  simp only [Nat.one_mul, Nat.pow_succ, Nat.mul_two]
  omega

theorem index_depth_bound (index : U128) (nonzero : index.val ≠ 0) :
    index.val.log2 < 128 := by
  apply (Nat.log2_lt nonzero).mpr
  scalar_tac

theorem index_depth_positive (value : Nat) (lower : 2 ≤ value) :
    0 < value.log2 := by
  have enough : 2 ^ 1 ≤ value := by simpa using lower
  have positive := (Nat.le_log2 (by omega : value ≠ 0)).mpr enough
  omega

theorem gindex_length_positive (value : Nat) (lower : 2 ≤ value) :
    Ssz.gindexLength value = .ok value.log2 := by
  have nonzero : value.log2 ≠ 0 := Nat.ne_of_gt (index_depth_positive value lower)
  have above : ¬ value < 1 := by omega
  simp [Ssz.gindexLength, Ssz.gindexDepth, above, Bind.bind, Except.bind, nonzero]

theorem calculate_root_form (leaf : Ssz.Bytes) (proof : List Ssz.Bytes)
    (index : Nat) (lower : 2 ≤ index) :
    Ssz.calculateMerkleRoot leaf proof index =
      if proof.length = index.log2 then .ok (Ssz.climbBranch index 0 leaf proof)
      else .error (.branchLength index.log2 proof.length) := by
  rw [Ssz.calculateMerkleRoot, gindex_length_positive index lower]
  by_cases same : proof.length = index.log2 <;>
    simp [Bind.bind, Except.bind, same] <;> rfl

theorem climbBranch_shift (index shift level : Nat) (leaf : Ssz.Bytes) (proof : List Ssz.Bytes) :
    Ssz.climbBranch (index >>> shift) level leaf proof =
      Ssz.climbBranch index (shift + level) leaf proof := by
  induction proof generalizing level leaf with
  | nil => rfl
  | cons sibling rest ih =>
    simp only [Ssz.climbBranch, Ssz.gindexBit, Nat.testBit_shiftRight]
    rw [ih]
    simp only [Nat.add_assoc]
    rfl

end FastSszVerification
