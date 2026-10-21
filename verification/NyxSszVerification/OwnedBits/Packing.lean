import NyxSszVerification.OwnedBits.Read

open Aeneas Aeneas.Std

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace NyxSszVerification

/-- Scalar packing recovery, proved locally to avoid unrelated specification imports. -/
theorem owned_unpack_pack (bits : _root_.Array Bool) (byteCount : Nat)
    (room : bits.size ≤ 8 * byteCount) :
    Ssz.unpackBits (Ssz.packBits bits byteCount) bits.size = bits := by
  apply _root_.Array.ext
  · simp [Ssz.unpackBits]
  intro index left right
  have inside : index / 8 < byteCount := by omega
  simp only [Ssz.unpackBits, _root_.Array.getElem_map, _root_.Array.getElem_range]
  have byteIs : (Ssz.packBits bits byteCount)[index / 8]! = Ssz.packByte bits (index / 8) := by
    simp [Ssz.packBits, inside]
  rw [byteIs, view_packByte_bit _ _ _ (by omega)]
  have position : index / 8 * 8 + index % 8 = index := by omega
  simp [position, right]

theorem owned_pack_high_clear (bits : _root_.Array Bool) (index offset : Nat)
    (small : offset < 8) (past : bits.size ≤ index * 8 + offset) :
    Ssz.packByte bits index >>> UInt8.ofNat offset = 0 := by
  apply UInt8.toBitVec_inj.mp
  have shifted : (Ssz.packByte bits index >>> UInt8.ofNat offset).toBitVec =
      (Ssz.packByte bits index).toBitVec >>> offset := by interval_cases offset <;> rfl
  rw [shifted]
  apply BitVec.eq_of_getLsbD_eq
  intro position inByte
  simp only [BitVec.getLsbD_ushiftRight, UInt8.toBitVec_zero, BitVec.getLsbD_zero]
  by_cases within : offset + position < 8
  · rw [← spec_byte_bit_observation _ _ within, view_packByte_bit _ _ _ within]
    rw [_root_.Array.getElem?_eq_none (by omega)]
    rfl
  · exact BitVec.getLsbD_of_ge _ _ (by omega)

theorem owned_decode_packed_vector (n : Nat) (bits : _root_.Array Bool)
    (positive : 0 < n) (fits : bits.size = n) :
    checkedDeserialize (.bitVector n) (Ssz.packBits bits ((n + 7) / 8)) = .ok (.bits bits) := by
  have width : (Ssz.packBits bits ((n + 7) / 8)).size = (n + 7) / 8 := by simp [Ssz.packBits]
  have recovered : Ssz.unpackBits (Ssz.packBits bits ((n + 7) / 8)) n = bits := by
    simpa [fits] using owned_unpack_pack bits ((n + 7) / 8) (by omega)
  have padded (odd : n % 8 ≠ 0) :
      (Ssz.packBits bits ((n + 7) / 8))[(n + 7) / 8 - 1]! >>> UInt8.ofNat (n % 8) = 0 := by
    have inside : (n + 7) / 8 - 1 < (n + 7) / 8 := by omega
    simp only [Ssz.packBits, _root_.Array.getElem!_ofFn, inside]
    apply owned_pack_high_clear _ _ _ (by omega)
    omega
  simp [checkedDeserialize, Ssz.Desc.wellFormed, Ssz.deserialize, width,
    Nat.ne_of_gt positive, recovered, Bind.bind, Except.bind, Pure.pure, Except.pure]
  intro odd _
  exact padded odd

theorem owned_highest_eq (byte : UInt8) (offset : Nat) (small : offset < 8)
    (isSet : (byte >>> UInt8.ofNat offset) &&& 1 = 1)
    (above : ∀ j, offset < j → j < 8 → (byte >>> UInt8.ofNat j) &&& 1 ≠ 1) :
    Ssz.highestBit byte = offset := by
  interval_cases offset <;> simp only [Ssz.highestBit, beq_iff_eq]
  all_goals
    repeat first
      | rw [if_neg (above 7 (by omega) (by omega))]
      | rw [if_neg (above 6 (by omega) (by omega))]
      | rw [if_neg (above 5 (by omega) (by omega))]
      | rw [if_neg (above 4 (by omega) (by omega))]
      | rw [if_neg (above 3 (by omega) (by omega))]
      | rw [if_neg (above 2 (by omega) (by omega))]
      | rw [if_neg (above 1 (by omega) (by omega))]
      | rw [if_pos isSet]
      | rfl

theorem owned_unpack_pack_push (bits : _root_.Array Bool) (byteCount : Nat)
    (room : bits.size + 1 ≤ 8 * byteCount) :
    Ssz.unpackBits (Ssz.packBits (bits.push true) byteCount) bits.size = bits := by
  apply _root_.Array.ext
  · simp [Ssz.unpackBits]
  intro index left right
  have inside : index / 8 < byteCount := by omega
  simp only [Ssz.unpackBits, _root_.Array.getElem_map, _root_.Array.getElem_range]
  have byteIs : (Ssz.packBits (bits.push true) byteCount)[index / 8]! =
      Ssz.packByte (bits.push true) (index / 8) := by simp [Ssz.packBits, inside]
  rw [byteIs, view_packByte_bit _ _ _ (by omega)]
  have position : index / 8 * 8 + index % 8 = index := by omega
  rw [position, _root_.Array.getElem?_eq_getElem (by simp; omega), Option.getD_some,
    _root_.Array.getElem_push_lt right]

theorem owned_unpack_delimited_pack (limit : Option Nat) (bits : _root_.Array Bool)
    (within : ∀ cap, limit = some cap → bits.size ≤ cap) :
    Ssz.unpackDelimited limit (Ssz.packBitsDelimited bits) = .ok bits := by
  show Ssz.unpackDelimited limit (Ssz.packBits (bits.push true) ((bits.size + 8) / 8)) = .ok bits
  have width : (Ssz.packBits (bits.push true) ((bits.size + 8) / 8)).size = (bits.size + 8) / 8 := by
    simp [Ssz.packBits]
  have finalIs : (Ssz.packBits (bits.push true) ((bits.size + 8) / 8))[bits.size / 8]! =
      Ssz.packByte (bits.push true) (bits.size / 8) := by simp [Ssz.packBits]
  have isSet : (Ssz.packByte (bits.push true) (bits.size / 8) >>> UInt8.ofNat (bits.size % 8)) &&& 1 = 1 := by
    have found := view_packByte_bit (bits.push true) (bits.size / 8) (bits.size % 8) (by omega)
    rw [show bits.size / 8 * 8 + bits.size % 8 = bits.size by omega] at found
    simpa using found
  have above : ∀ j, bits.size % 8 < j → j < 8 →
      (Ssz.packByte (bits.push true) (bits.size / 8) >>> UInt8.ofNat j) &&& 1 ≠ 1 := by
    intro j over small
    have clear := view_packByte_bit (bits.push true) (bits.size / 8) j small
    rw [_root_.Array.getElem?_eq_none (by simp; omega)] at clear
    simpa using clear
  have notZero : Ssz.packByte (bits.push true) (bits.size / 8) ≠ 0 := by
    intro zero
    rw [zero] at isSet
    simp at isSet
  have counted : 8 * ((bits.size + 8) / 8 - 1) +
      Ssz.highestBit (Ssz.packByte (bits.push true) (bits.size / 8)) = bits.size := by
    rw [owned_highest_eq _ (bits.size % 8) (by omega) isSet above]
    omega
  have recovered := owned_unpack_pack_push bits ((bits.size + 8) / 8) (by omega)
  simp only [Ssz.unpackDelimited, width, beq_iff_eq,
    show ¬(bits.size + 8) / 8 = 0 by omega, if_neg, not_false_eq_true,
    show (bits.size + 8) / 8 - 1 = bits.size / 8 by omega, finalIs, if_neg notZero]
  rw [show (bits.size + 8) / 8 - 1 = bits.size / 8 by omega] at counted
  cases limit with
  | none =>
    simp [counted, Bind.bind, Except.bind, Pure.pure, Except.pure]
    simpa using recovered
  | some cap =>
    have fits := within cap rfl
    simp [counted, Nat.not_lt.mpr fits, Bind.bind, Except.bind, Pure.pure, Except.pure]
    simpa using recovered

theorem owned_vector_roundtrip (n : Nat) (bits : _root_.Array Bool) (bytes : Ssz.Bytes)
    (encoded : checkedSerialize (.bitVector n) (.bits bits) = .ok bytes) :
    checkedDeserialize (.bitVector n) bytes = .ok (.bits bits) := by
  unfold checkedSerialize at encoded
  simp only [Ssz.Desc.wellFormed, Ssz.serialize, Bind.bind, Except.bind] at encoded
  split_ifs at encoded
  simp_all
  rw [← encoded]
  exact owned_decode_packed_vector n bits (by omega) (by omega)

theorem owned_list_roundtrip (limit : Option Nat) (bits : _root_.Array Bool) (bytes : Ssz.Bytes)
    (encoded : checkedSerialize (.progressiveBitList limit) (.bits bits) = .ok bytes) :
    checkedDeserialize (.progressiveBitList limit) bytes = .ok (.bits bits) := by
  cases limit with
  | none =>
    simp [checkedSerialize, Ssz.Desc.wellFormed, Ssz.serialize, Ssz.boundCheck,
      Bind.bind, Except.bind, Pure.pure, Except.pure] at encoded
    subst bytes
    simp [checkedDeserialize, Ssz.Desc.wellFormed, Ssz.deserialize,
      owned_unpack_delimited_pack none bits (by simp), Bind.bind, Except.bind, Pure.pure, Except.pure]
  | some cap =>
    simp [checkedSerialize, Ssz.Desc.wellFormed, Ssz.serialize, Ssz.boundCheck,
      Bind.bind, Except.bind, Pure.pure, Except.pure] at encoded
    split_ifs at encoded
    simp_all
    subst bytes
    simp [checkedDeserialize, Ssz.Desc.wellFormed, Ssz.deserialize,
      owned_unpack_delimited_pack (some cap) bits (by simp_all), Bind.bind, Except.bind, Pure.pure, Except.pure]

end NyxSszVerification
