import NyxSszVerification.PackedRoots.Pack
import NyxSszVerification.Bitfield.DelimitedPack

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace NyxSszVerification

theorem highestBit_lt_eight (byte : UInt8) : Ssz.highestBit byte < 8 := by
  unfold Ssz.highestBit
  split <;> (try omega)
  all_goals repeat first | split | omega

@[simp] theorem viewBits_size (view : NyxSszRust.bitfield.BitListView) :
    (viewBits view).size = delimitedLength view.encoded.val := by
  simp [viewBits, Ssz.unpackBits]

/-- A masked native-byte bit test is its ordinary bit-vector observation. -/
theorem spec_byte_bit_observation (byte : UInt8) (offset : Nat) (inside : offset < 8) :
    ((byte >>> UInt8.ofNat offset) &&& 1 == 1) = byte.toBitVec.getLsbD offset := by
  have shifted : (byte >>> UInt8.ofNat offset).toBitVec = byte.toBitVec >>> offset := by
    interval_cases offset <;> rfl
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  rw [← UInt8.toBitVec_inj]
  change ((byte >>> UInt8.ofNat offset).toBitVec &&& 1#8 = 1#8) ↔ _
  rw [shifted, BitVec.and_one_eq_setWidth_ofBool_getLsbD]
  simp only [BitVec.getLsbD_ushiftRight]
  cases byte.toBitVec.getLsbD offset <;> decide

/-- A byte is determined by its eight single-bit observations. -/
theorem spec_byte_ext (left right : UInt8)
    (same : ∀ offset, offset < 8 →
      ((left >>> UInt8.ofNat offset) &&& 1 == 1) =
      ((right >>> UInt8.ofNat offset) &&& 1 == 1)) : left = right := by
  apply UInt8.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro offset inside
  simpa only [spec_byte_bit_observation _ _ inside] using same offset inside

/-- The low-bit mask preserves exactly the positions below its width. -/
theorem low_mask_observation (byte mask : U8) (width offset : Nat)
    (small : width < 8) (inside : offset < 8) (value : mask.val = 2 ^ width - 1) :
    ((byteToSpec (byte &&& mask) >>> UInt8.ofNat offset) &&& 1 == 1) =
      (((byteToSpec byte >>> UInt8.ofNat offset) &&& 1 == 1) && decide (offset < width)) := by
  have maskEq : mask = UScalar.ofNatCore (ty := .U8) (2 ^ width - 1) (by scalar_tac) := by
    apply UScalar.eq_of_val_eq
    simpa using value
  rw [spec_byte_bit_observation _ _ inside, spec_byte_bit_observation _ _ inside]
  change (byte.bv &&& mask.bv).getLsbD offset = (byte.bv.getLsbD offset && decide (offset < width))
  rw [BitVec.getLsbD_and]
  congr 1
  rw [maskEq]
  simp only [U8.bv, UScalar.ofNatCore_bv]
  interval_cases width <;> interval_cases offset <;> decide

/-- Single-bit packing law, as in the pinned codec's `packByte_bit` proof.
Kept local to avoid importing its unrelated decoder-admissibility dependency. -/
theorem view_packByte_bit (bits : _root_.Array Bool) (index offset : Nat)
    (inside : offset < 8) :
    ((Ssz.packByte bits index >>> UInt8.ofNat offset) &&& 1 == 1) =
      bits[index * 8 + offset]?.getD false := by
  interval_cases offset <;> simp only [Ssz.packByte]
  all_goals
    generalize bits[index * 8 + 0]?.getD false = b0
    generalize bits[index * 8 + 1]?.getD false = b1
    generalize bits[index * 8 + 2]?.getD false = b2
    generalize bits[index * 8 + 3]?.getD false = b3
    generalize bits[index * 8 + 4]?.getD false = b4
    generalize bits[index * 8 + 5]?.getD false = b5
    generalize bits[index * 8 + 6]?.getD false = b6
    generalize bits[index * 8 + 7]?.getD false = b7
    revert b0 b1 b2 b3 b4 b5 b6 b7
    decide

/-- Unpacking retains the bit exactly when it precedes the declared bit count. -/
theorem view_unpackBits_bit (bytes : List U8) (count index offset : Nat)
    (inside : index < bytes.length) (small : offset < 8) :
    (Ssz.unpackBits (bytesToSpec bytes) count)[index * 8 + offset]?.getD false =
      (((byteToSpec bytes[index] >>> UInt8.ofNat offset) &&& 1 == 1) &&
        decide (index * 8 + offset < count)) := by
  have quotient : (index * 8 + offset) / 8 = index := by omega
  have remainder : (index * 8 + offset) % 8 = offset := by omega
  by_cases held : index * 8 + offset < count
  · simp [Ssz.unpackBits, held, quotient, remainder, bytesToSpec, inside]
  · simp [Ssz.unpackBits, held]

/-- Full-byte masks are the identity. -/
theorem byte_and_full (byte : U8) : byte &&& 255#u8 = byte := by
  apply UScalar.eq_of_val_eq
  change byte.val &&& (2 ^ 8 - 1) = byte.val
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt byte.hBounds

/-- Complete packing, including the partial final byte and the empty payload. -/
theorem packedInput_packBits (bytes : List U8) (count bitCount : Nat) (mask : U8)
    (within : count ≤ bytes.length) (width : count = (bitCount + 7) / 8)
    (maskValue : if bitCount % 8 = 0 then mask = 255#u8
      else mask.val = 2 ^ (bitCount % 8) - 1) :
    bytesToSpec (packedInput bytes count mask) =
      Ssz.packBits (Ssz.unpackBits (bytesToSpec bytes) bitCount) ((bitCount + 7) / 8) := by
  apply _root_.Array.ext
  · rw [bytesToSpec_size, packedInput_length _ _ _ within]
    simp only [Ssz.packBits, _root_.Array.size_ofFn, width]
  intro index left right
  have active : index < count := by simpa [within] using left
  have inBytes : index < bytes.length := by omega
  rw [bytesToSpec_getElem]
  simp only [List.getElem!_eq_getElem?_getD,
    List.getElem?_eq_getElem (show index < (packedInput bytes count mask).length by
      simp [within]; omega), Option.getD_some]
  rw [packedInput_get _ _ _ _ within active]
  simp only [Ssz.packBits, _root_.Array.getElem_ofFn]
  apply spec_byte_ext
  intro offset small
  rw [view_packByte_bit _ _ _ small, view_unpackBits_bit _ _ _ _ inBytes small]
  by_cases aligned : bitCount % 8 = 0
  · have full : index * 8 + offset < bitCount := by omega
    simp only [aligned, ↓reduceIte] at maskValue
    simp [maskValue, full]
  · simp only [aligned, ↓reduceIte] at maskValue
    by_cases ending : index + 1 = count
    · have position : (index * 8 + offset < bitCount) ↔ offset < bitCount % 8 := by omega
      simp only [ending, ↓reduceIte]
      rw [low_mask_observation _ _ _ _ (Nat.mod_lt _ (by decide)) small maskValue]
      simp only [position]
    · have full : index * 8 + offset < bitCount := by omega
      simp [ending, full]

/-- The delimiter contributes at most seven bits after the complete prefix bytes. -/
theorem delimitedLength_bounds (bytes : List U8) (nonempty : 0 < bytes.length) :
    delimitedLength bytes / 8 = bytes.length - 1 ∧
    delimitedLength bytes % 8 = Ssz.highestBit (bytesToSpec bytes)[bytes.length - 1]! ∧
    (delimitedLength bytes + 7) / 8 ≤ bytes.length := by
  have small := highestBit_lt_eight (bytesToSpec bytes)[bytes.length - 1]!
  unfold delimitedLength
  omega

end NyxSszVerification
