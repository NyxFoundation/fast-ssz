import FastSszVerification.Representation.Bytes
import Ssz.Proofs.Codec.Table

open Aeneas Aeneas.Std

namespace FastSszVerification

theorem little_endian_head {width : Nat} (word : BitVec width) :
    UInt8.ofBitVec (word.setWidth 8) = UInt8.ofNat (word.toNat % 256) := by
  have same : word.setWidth 8 = BitVec.ofNat 8 (word.toNat % 256) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth]
  exact congrArg UInt8.ofBitVec same

theorem little_endian_encode_refines (width : Nat) (word : BitVec (8 * width)) :
    (word.toLEBytes.map UInt8.ofBitVec).toArray = Ssz.uintBytes width word.toNat := by
  induction width with
  | zero => simp [BitVec.toLEBytes, Ssz.uintBytes]
  | succ width ih =>
    have positive : 0 < 8 * (width + 1) := by omega
    have remaining : 8 * (width + 1) - 8 = 8 * width := by omega
    have bounded := word.isLt
    simp only [Nat.mul_add, Nat.mul_one, Nat.pow_add, Nat.reducePow] at bounded
    have shifted : ((word >>> 8).setWidth (8 * width)).toNat = word.toNat / 256 := by
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
        Nat.reducePow]
      apply Nat.mod_eq_of_lt
      omega
    rw [BitVec.toLEBytes]
    simp only [positive, if_pos]
    rw [List.map_cons, List.toArray_cons, Ssz.uintBytes, little_endian_head,
      remaining, ih, shifted]

theorem serialize_uint_bits (width : Nat) (word : BitVec (8 * width)) :
    Ssz.serialize (.uint width) (.uint word.toNat) =
      .ok (word.toLEBytes.map UInt8.ofBitVec).toArray := by
  have bounded := word.isLt
  rw [little_endian_encode_refines]
  simp only [Ssz.serialize, if_pos bounded]

theorem little_endian_roundtrip (bytes : List Byte) :
    (BitVec.fromLEBytes bytes).toLEBytes = bytes := by
  have sized : (BitVec.fromLEBytes bytes).toLEBytes.length = bytes.length := by
    rw [BitVec.toLEBytes_length]
    omega
  apply List.ext_getElem sized
  intro index left right
  apply (Byte.eq_iff _ _).mpr
  intro bit inside
  have position : 8 * index + bit < 8 * bytes.length := by omega
  rw [BitVec.toLEBytes_getElem_testBit _ index bit left ⟨inside, position⟩,
    BitVec.fromLEBytes_getElem bytes (8 * index + bit) position]
  have quotient : (8 * index + bit) / 8 = index := by omega
  have remainder : (8 * index + bit) % 8 = bit := by omega
  simp only [quotient, remainder]

theorem little_endian_decode_refines (bytes : List Byte) :
    Ssz.readUint (bytes.map UInt8.ofBitVec).toArray 0 bytes.length =
      (BitVec.fromLEBytes bytes).toNat := by
  have encoded := little_endian_encode_refines bytes.length (BitVec.fromLEBytes bytes)
  rw [little_endian_roundtrip] at encoded
  rw [encoded]
  exact Ssz.readUint_uintBytes _ _ (BitVec.fromLEBytes bytes).isLt

theorem readUint_bytesToSpec (bytes : List U8) {width : Nat} (sized : bytes.length = width) :
    Ssz.readUint (bytesToSpec bytes) 0 width =
      (BitVec.fromLEBytes (bytes.map U8.bv)).toNat := by
  rw [← sized]
  unfold bytesToSpec byteToSpec
  simpa only [List.length_map, List.map_map, Function.comp_def]
    using little_endian_decode_refines (bytes.map U8.bv)

theorem deserialize_uint_form (width : Nat) (bytes : Ssz.Bytes) :
    Ssz.deserialize (.uint width) bytes =
      if bytes.size = width then .ok (.uint (Ssz.readUint bytes 0 width))
      else .error (.scope width bytes.size) := by
  by_cases sized : bytes.size = width <;>
    simp [Ssz.deserialize, sized, Bind.bind, Except.bind, Pure.pure, Except.pure,
      MonadExcept.throw, throwThe, MonadExceptOf.throw]

end FastSszVerification
