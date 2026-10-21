import NyxSszVerification.OwnedBits.Model

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace NyxSszVerification

@[simp] theorem ownedVectorBits_size (bytes : List U8) (n : Nat) :
    (ownedVectorBits bytes n).size = ownedVectorCount bytes n := by
  simp [ownedVectorBits, Ssz.unpackBits]

@[simp] theorem ownedListBits_size (bytes : List U8) :
    (ownedListBits bytes).size = delimitedLength bytes := by
  simp [ownedListBits, Ssz.unpackBits]

@[step] theorem owned_delimited_len_refines (bytes : Slice U8) :
    NyxSszRust.bit_storage.delimited_len bytes ⦃ count => count.val = delimitedLength bytes.val ⦄ := by
  have maximum := usize_max_le_u64
  unfold NyxSszRust.bit_storage.delimited_len
  step*
  all_goals have lookup := bytesToSpec_getElem_bang bytes.val (bytes.val.length - 1)
  all_goals simp_all [delimitedLength, Nat.mul_comm]
  · rfl
  · have inside : bytes.val.length - 1 < bytes.val.length := by omega
    simp [inside]

@[step] theorem owned_get_bit_refines (bytes : Slice U8) (index : U128) :
    NyxSszRust.bit_storage.get_bit bytes index ⦃ actual =>
      actual = if index.val / 8 < bytes.val.length then some (referenceBit bytes.val index.val) else none ⦄ := by
  have maximum := usize_max_le_u64
  have trunc : ∀ k, k < bytes.val.length → k % 2 ^ System.Platform.numBits = k := by
    intro k inside
    apply Nat.mod_eq_of_lt
    have bound := bytes.property
    have maxEq : Usize.max + 1 = 2 ^ System.Platform.numBits := by
      simp [Usize.max, Usize.numBits, UScalarTy.numBits]
    omega
  unfold NyxSszRust.bit_storage.get_bit
  step*
  all_goals simp_all
  rw [referenceBit_bv _ _ (by omega)]
  have small : index.val % 8 < 4294967296 := by omega
  simp_all [UScalar.eq_equiv_bv_eq, Nat.mod_eq_of_lt small]

@[step] theorem owned_get_list_bit_refines (bytes : Slice U8) (index : U128) :
    NyxSszRust.bit_storage.get_list_bit bytes index ⦃ actual =>
      actual = (ownedListBits bytes.val)[index.val]? ⦄ := by
  have capacity : delimitedLength bytes.val ≤ bytes.val.length * 8 := by
    have tail := highestBit_lt_eight (bytesToSpec bytes.val)[bytes.val.length - 1]!
    cases h : bytes.val with
    | nil => simp only [delimitedLength, List.length_nil, Nat.zero_sub, Nat.mul_zero, Nat.zero_add]; rfl
    | cons head rest => simp only [delimitedLength, h, List.length_cons] at *; omega
  unfold NyxSszRust.bit_storage.get_list_bit
  step*
  all_goals simp_all [ownedListBits, Ssz.unpackBits, referenceBit]
  all_goals omega

@[step] theorem owned_bit_vector_as_ssz_bytes_refines {N : Usize}
    (value : NyxSszRust.bitcollections.BitVector N) :
    NyxSszRust.bitcollections.BitVector.as_ssz_bytes value ⦃ bytes => bytes.val = value.encoded.val ⦄ := by
  simp [NyxSszRust.bitcollections.BitVector.as_ssz_bytes]

@[step] theorem owned_bit_list_as_ssz_bytes_refines {MAX : Usize}
    (value : NyxSszRust.bitcollections.BitList MAX) :
    NyxSszRust.bitcollections.BitList.as_ssz_bytes value ⦃ bytes => bytes.val = value.encoded.val ⦄ := by
  simp [NyxSszRust.bitcollections.BitList.as_ssz_bytes]

@[step] theorem owned_progressive_bit_list_as_ssz_bytes_refines
    (value : NyxSszRust.bitcollections.ProgressiveBitList) :
    NyxSszRust.bitcollections.ProgressiveBitList.as_ssz_bytes value ⦃ bytes => bytes.val = value.encoded.val ⦄ := by
  simp [NyxSszRust.bitcollections.ProgressiveBitList.as_ssz_bytes]

@[step] theorem owned_bit_list_len_bits_refines {MAX : Usize}
    (value : NyxSszRust.bitcollections.BitList MAX) :
    NyxSszRust.bitcollections.BitList.len_bits value ⦃ count => count.val = (ownedListBits value.encoded.val).size ⦄ := by
  unfold NyxSszRust.bitcollections.BitList.len_bits
  step*
  simp_all

@[step] theorem owned_progressive_bit_list_len_bits_refines
    (value : NyxSszRust.bitcollections.ProgressiveBitList) :
    NyxSszRust.bitcollections.ProgressiveBitList.len_bits value ⦃ count => count.val = (ownedListBits value.encoded.val).size ⦄ := by
  unfold NyxSszRust.bitcollections.ProgressiveBitList.len_bits
  step*
  simp_all

@[step] theorem owned_bit_list_get_refines {MAX : Usize}
    (value : NyxSszRust.bitcollections.BitList MAX) (index : U128) :
    NyxSszRust.bitcollections.BitList.get value index ⦃ actual => actual = (ownedListBits value.encoded.val)[index.val]? ⦄ := by
  unfold NyxSszRust.bitcollections.BitList.get
  step*

@[step] theorem owned_progressive_bit_list_get_refines
    (value : NyxSszRust.bitcollections.ProgressiveBitList) (index : U128) :
    NyxSszRust.bitcollections.ProgressiveBitList.get value index ⦃ actual => actual = (ownedListBits value.encoded.val)[index.val]? ⦄ := by
  unfold NyxSszRust.bitcollections.ProgressiveBitList.get
  step*

theorem ownedVectorCount_of_length (bytes : List U8) (n : Nat)
    (positive : 0 < n) (length : bytes.length = (n + 7) / 8) :
    ownedVectorCount bytes n = n := by
  unfold ownedVectorCount
  have nonempty : bytes.isEmpty = false := by
    apply List.isEmpty_eq_false_iff.mpr
    intro empty
    simp_all
    omega
  simp only [nonempty, Bool.false_eq_true, ↓reduceIte]
  split <;> omega

@[step] theorem owned_bit_vector_len_bits_refines {N : Usize}
    (value : NyxSszRust.bitcollections.BitVector N)
    (canonical : canonicalOwnedVector value.encoded.val N.val) :
    NyxSszRust.bitcollections.BitVector.len_bits value ⦃ count =>
      count.val = (ownedVectorBits value.encoded.val N.val).size ⦄ := by
  have count := ownedVectorCount_of_length value.encoded.val N.val canonical.1 canonical.2.1
  simp [NyxSszRust.bitcollections.BitVector.len_bits, count]

@[step] theorem owned_bit_vector_get_refines {N : Usize}
    (value : NyxSszRust.bitcollections.BitVector N) (index : U128)
    (canonical : canonicalOwnedVector value.encoded.val N.val) :
    NyxSszRust.bitcollections.BitVector.get value index ⦃ actual =>
      actual = (ownedVectorBits value.encoded.val N.val)[index.val]? ⦄ := by
  have count := ownedVectorCount_of_length value.encoded.val N.val canonical.1 canonical.2.1
  have capacity : N.val ≤ value.encoded.val.length * 8 := by have len := canonical.2.1; omega
  unfold NyxSszRust.bitcollections.BitVector.get
  step*
  all_goals simp_all [ownedVectorBits, Ssz.unpackBits, referenceBit]
  all_goals omega

end NyxSszVerification
