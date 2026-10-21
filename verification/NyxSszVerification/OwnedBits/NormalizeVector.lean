import NyxSszVerification.OwnedBits.Copy
import NyxSszVerification.OwnedBits.FromBits

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace NyxSszVerification

theorem ownedVectorCount_length_iff (bytes : List U8) (n : Nat) (positive : 0 < n) :
    ownedVectorCount bytes n = n ↔ bytes.length = (n + 7) / 8 := by
  constructor
  · by_cases empty : bytes = []
    · simp [ownedVectorCount, empty]
      omega
    · have nonempty : bytes.isEmpty = false := List.isEmpty_eq_false_iff.mpr empty
      simp only [ownedVectorCount, nonempty, Bool.false_eq_true, ↓reduceIte]
      intro count
      have bytePositive : 0 < bytes.length := by cases bytes <;> simp_all
      split at count <;> omega
  · exact ownedVectorCount_of_length bytes n positive

@[step] theorem owned_normalize_vector_storage (bytes : Slice U8) (n : Usize) :
    NyxSszRust.bit_storage.normalize_vector bytes n ⦃ actual =>
      match actual with
      | .Ok output => 0 < n.val ∧ bytes.val.length = (n.val + 7) / 8 ∧
          ∃ mask : U8, (if n.val % 8 = 0 then mask = 255#u8 else mask.val = 2 ^ (n.val % 8) - 1) ∧
            output.val = packedInput bytes.val bytes.val.length mask
      | .Err error => (n.val = 0 ∧ error = .EmptyVector) ∨
          (0 < n.val ∧ bytes.val.length ≠ (n.val + 7) / 8 ∧ error = .InvalidLength) ⦄ := by
  have powSmall : 2 ^ (n.val % 8) < U8.size := by
    simpa [U8.size, U8.numBits] using
      (Nat.pow_lt_pow_right (a := 2) (by decide) (Nat.mod_lt n.val (by decide : 0 < 8)))
  have powPositive : 1 ≤ 2 ^ (n.val % 8) := Nat.one_le_pow _ _ (by decide)
  unfold NyxSszRust.bit_storage.normalize_vector
  step*
  all_goals simp_all [Nat.shiftLeft_eq, Nat.mod_eq_of_lt powSmall]
  · refine ⟨by omega, by scalar_tac, i4, i4_post1, ?_⟩
    have nonempty : 0 < bytes.val.length := by scalar_tac
    have inside : bytes.val.length - 1 < bytes.val.length := by omega
    have same : i6 = bytes.val[bytes.val.length - 1]! &&& i4 := by
      apply U8.bv_eq_imp_eq
      simpa [inside] using i6_post2
    simpa [same] using owned_set_last_mask bytes.val i4 nonempty
  · refine ⟨by omega, ?_⟩
    have lenEq : bytes.val.length = (n.val + 7) / 8 := by scalar_tac
    simpa only [← lenEq] using (packedInput_full bytes.val).symm

@[step] theorem owned_normalize_vector_refines (bytes : Slice U8) (n : Usize) :
    NyxSszRust.bit_storage.normalize_vector bytes n ⦃ actual =>
      codecEncodingAgrees actual (checkedSerialize (.bitVector n.val) (.bits (ownedVectorBits bytes.val n.val))) ⦄ := by
  apply spec_mono (owned_normalize_vector_storage bytes n)
  intro actual agrees
  cases actual with
  | Ok output =>
    rcases agrees with ⟨positive, length, mask, maskValue, data⟩
    have count := ownedVectorCount_of_length bytes.val n.val positive length
    have packed := packedInput_packBits bytes.val bytes.val.length n.val mask (by omega) length maskValue
    simp [codecEncodingAgrees, checkedSerialize, Ssz.Desc.wellFormed, Ssz.serialize,
      Nat.ne_of_gt positive, ownedVectorBits, Ssz.unpackBits, count, Bind.bind, Except.bind]
    simpa [data, Ssz.unpackBits] using packed
  | Err error =>
    rcases agrees with ⟨zero, rfl⟩ | ⟨positive, mismatch, rfl⟩
    · simp [codecEncodingAgrees, checkedSerialize, Ssz.Desc.wellFormed, zero, codecFaultAgrees,
        Bind.bind, Except.bind]
    · have countNe : ownedVectorCount bytes.val n.val ≠ n.val := by
        intro same
        exact mismatch ((ownedVectorCount_length_iff _ _ positive).mp same)
      simp [codecEncodingAgrees, checkedSerialize, Ssz.Desc.wellFormed, Ssz.serialize,
        Nat.ne_of_gt positive, countNe, codecFaultAgrees, Bind.bind, Except.bind]

end NyxSszVerification
