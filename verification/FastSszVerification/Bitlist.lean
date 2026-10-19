import FastSszVerification.Bitfield
import FastSszVerification.Bitfield.Delimiter
import FastSszVerification.Bitfield.DelimitedPack

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace FastSszVerification

@[step] theorem decode_bit_list_refines (bytes : Slice U8) (limit : Usize) :
    FastSszRust.bitfield.decode_bit_list bytes limit ⦃ actual =>
      bitDecodingAgrees actual
        (checkedDeserialize (.bitList limit.val) (bytesToSpec bytes.val)) ⦄ := by
  unfold FastSszRust.bitfield.decode_bit_list
  step*
  all_goals have lastLookup := bytesToSpec_getElem_bang bytes.val (bytes.val.length - 1)
  all_goals simp_all [checkedDeserialize, Ssz.Desc.wellFormed, Ssz.deserialize,
    Ssz.unpackDelimited, bitDecodingAgrees, bitFaultAgrees,
    Bind.bind, Except.bind, Pure.pure, Except.pure, MonadExcept.throw, throwThe,
    MonadExceptOf.throw]
  all_goals have lastInRange : bytes.val.length - 1 < bytes.val.length := by omega
  all_goals simp_all
  all_goals split_ifs <;> simp_all [Nat.mul_comm]
  all_goals omega

@[step] theorem encode_bit_list_refines (bits : Slice Bool) (limit : Usize) :
    FastSszRust.bitfield.encode_bit_list bits limit ⦃ actual =>
      bitEncodingAgrees actual
        (checkedSerialize (.bitList limit.val) (.bits (bitsToSpec bits.val))) ⦄ := by
  unfold FastSszRust.bitfield.encode_bit_list
  step*
  all_goals simp_all [checkedSerialize, Ssz.Desc.wellFormed, Ssz.serialize,
    bitEncodingAgrees, bitFaultAgrees, Bind.bind, Except.bind]
  · have noSpace : ¬bits.val.length ≤ limit.val := by omega
    rw [if_neg noSpace]
    trivial
  all_goals have outputLength := congrArg _root_.Array.size output_post
  all_goals simp only [Ssz.packBits, bytesToSpec_size, _root_.Array.size_ofFn] at outputLength
  · rw [outputLength]
    scalar_tac
  · have aligned : (bitsToSpec bits.val).size % 8 = 0 := by simp_all
    rw [bytesToSpec_push, output_post, packBitsDelimited_aligned _ aligned]
    rfl
  · rw [outputLength]
    omega
  · have unaligned : (bitsToSpec bits.val).size % 8 ≠ 0 := by simp_all
    have lastIndex : output.val.length - 1 = bits.val.length / 8 := by simp_all; omega
    have validLast : output.val.length - 1 < output.val.length := by simp_all; omega
    have insidePacking : bits.val.length / 8 < (bits.val.length + 7) / 8 := by simp_all
    have originalByte : byteToSpec output.val[output.val.length - 1]! =
        Ssz.packByte (bitsToSpec bits.val) (bits.val.length / 8) := by
      have known := congrArg (fun bytes : _root_.Array UInt8 => bytes[bits.val.length / 8]!) output_post
      simpa [bytesToSpec_getElem_bang, Ssz.packBits, insidePacking, lastIndex] using known
    have updatedByte : byteToSpec i5 = byteToSpec output.val[output.val.length - 1]! |||
        (1 <<< UInt8.ofNat (bits.val.length % 8)) := by
      apply byte_or_shift_one _ _ _ (Nat.mod_lt _ (by decide))
      simpa [validLast] using i5_post2
    rw [bytesToSpec_set, updatedByte, originalByte, output_post, lastIndex]
    exact (packBitsDelimited_unaligned _ unaligned).symm

end FastSszVerification
