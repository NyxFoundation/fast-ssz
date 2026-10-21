import NyxSszVerification.OwnedBits.Packing

open Aeneas Aeneas.Std

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace NyxSszVerification

theorem owned_highest_spec (byte : UInt8) (nonzero : byte ≠ 0) :
    Ssz.highestBit byte < 8 ∧
    ((byte >>> UInt8.ofNat (Ssz.highestBit byte)) &&& 1 == 1) = true ∧
    ∀ offset : Fin 8, Ssz.highestBit byte < offset.val →
      ((byte >>> UInt8.ofNat offset.val) &&& 1 == 1) = false := by
  cases byte with
  | ofBitVec byte =>
    cases byte with
    | ofFin byte => revert byte; decide

/-- Every nonzero final byte is already the unique canonical delimiter encoding. -/
theorem owned_pack_delimited_canonical (bytes : List U8) (nonempty : 0 < bytes.length)
    (nonzero : (bytesToSpec bytes)[bytes.length - 1]! ≠ 0) :
    Ssz.packBitsDelimited (ownedListBits bytes) = bytesToSpec bytes := by
  have bounds := delimitedLength_bounds bytes nonempty
  obtain ⟨small, set, high⟩ := owned_highest_spec _ nonzero
  have width : (delimitedLength bytes + 8) / 8 = bytes.length := by
    unfold delimitedLength
    omega
  apply _root_.Array.ext
  · simp [Ssz.packBitsDelimited, Ssz.packBits, width]
  intro index left right
  have inside : index < bytes.length := by simpa using right
  simp only [Ssz.packBitsDelimited, Ssz.packBits, _root_.Array.getElem_ofFn]
  apply spec_byte_ext
  intro offset below
  rw [view_packByte_bit _ _ _ below, bitAt_push]
  simp only [ownedListBits_size]
  unfold ownedListBits
  rw [view_unpackBits_bit _ _ _ _ inside below]
  rw [bytesToSpec_getElem]
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem inside, Option.getD_some]
  by_cases before : index * 8 + offset < delimitedLength bytes
  · simp [before, Nat.ne_of_lt before]
  · have last : index = bytes.length - 1 := by
      unfold delimitedLength at before
      omega
    subst index
    have byteEq : byteToSpec bytes[bytes.length - 1] = (bytesToSpec bytes)[bytes.length - 1]! := by
      simp [bytesToSpec, inside]
    rw [byteEq]
    by_cases closing : (bytes.length - 1) * 8 + offset = delimitedLength bytes
    · have offsetEq : offset = Ssz.highestBit (bytesToSpec bytes)[bytes.length - 1]! := by
        unfold delimitedLength at closing
        omega
      simp [offsetEq, set]
      right
      unfold delimitedLength
      omega
    · have above : Ssz.highestBit (bytesToSpec bytes)[bytes.length - 1]! < offset := by
        unfold delimitedLength at before closing
        omega
      simp [before, closing, high ⟨offset, below⟩ above]

def ownedNormalizedList (bytes : List U8) : List U8 :=
  if bytes.isEmpty then [1#u8]
  else if bytes[bytes.length - 1]! = 0#u8 then bytes.set (bytes.length - 1) 1#u8 else bytes

@[simp] theorem ownedNormalizedList_nonempty (bytes : List U8) : 0 < (ownedNormalizedList bytes).length := by
  unfold ownedNormalizedList
  split
  · simp
  · split <;> simp_all
    all_goals cases bytes <;> simp_all

@[simp] theorem ownedNormalizedList_last (bytes : List U8) :
    (bytesToSpec (ownedNormalizedList bytes))[(ownedNormalizedList bytes).length - 1]! ≠ 0 := by
  unfold ownedNormalizedList
  split
  · decide
  · have nonempty : 0 < bytes.length := by cases bytes <;> simp_all
    have inside : bytes.length - 1 < bytes.length := by omega
    split <;> simp_all [bytesToSpec]

@[simp] theorem ownedNormalizedList_count (bytes : List U8) :
    delimitedLength (ownedNormalizedList bytes) = delimitedLength bytes := by
  unfold ownedNormalizedList
  split
  · simp_all [delimitedLength]
    rfl
  · have nonempty : 0 < bytes.length := by cases bytes <;> simp_all
    have inside : bytes.length - 1 < bytes.length := by omega
    split <;> simp_all [delimitedLength, bytesToSpec]
    rfl

theorem ownedNormalizedList_bits (bytes : List U8) :
    ownedListBits (ownedNormalizedList bytes) = ownedListBits bytes := by
  apply _root_.Array.ext
  · simp
  intro index left right
  have bitBound : index < delimitedLength bytes := by simpa using right
  simp only [ownedListBits, ownedNormalizedList_count, Ssz.unpackBits, _root_.Array.getElem_map,
    _root_.Array.getElem_range]
  congr 2
  unfold ownedNormalizedList
  split
  · rename_i empty
    have emptyBytes : bytes = [] := List.isEmpty_iff.mp empty
    subst bytes
    change index < 0 at bitBound
    omega
  · split
    · rename_i nonempty zero
      have sizePositive : 0 < bytes.length := by cases bytes <;> simp_all
      have lastInRange : bytes.length - 1 < bytes.length := by omega
      have lengthEq : delimitedLength bytes = 8 * (bytes.length - 1) := by
        simp [delimitedLength, bytesToSpec_getElem_bang, zero]
        rfl
      have inside : index / 8 < bytes.length := by omega
      have different : bytes.length - 1 ≠ index / 8 := by omega
      simp [bytesToSpec, inside, different]
    · rfl

theorem ownedNormalizedList_pack (bytes : List U8) :
    bytesToSpec (ownedNormalizedList bytes) = Ssz.packBitsDelimited (ownedListBits bytes) := by
  rw [← ownedNormalizedList_bits bytes]
  exact (owned_pack_delimited_canonical _ (ownedNormalizedList_nonempty bytes)
    (ownedNormalizedList_last bytes)).symm

end NyxSszVerification
