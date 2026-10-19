import FastSszRust.Scalar
import FastSszVerification.Representation.Integers

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace FastSszVerification

theorem encode_u8_refines (value : U8) :
    FastSszRust.scalar.encode_u8 value ⦃ encoded =>
      Ssz.serialize (.uint 1) (.uint value.val) = .ok (bytesToSpec encoded.val) ⦄ := by
  simpa [FastSszRust.scalar.encode_u8, core.num.U8.to_le_bytes,
    bytesToSpec, byteToSpec, List.map_map, Function.comp_def]
    using serialize_uint_bits 1 value.bv

theorem encode_u16_refines (value : U16) :
    FastSszRust.scalar.encode_u16 value ⦃ encoded =>
      Ssz.serialize (.uint 2) (.uint value.val) = .ok (bytesToSpec encoded.val) ⦄ := by
  simpa [FastSszRust.scalar.encode_u16, core.num.U16.to_le_bytes,
    bytesToSpec, byteToSpec, List.map_map, Function.comp_def]
    using serialize_uint_bits 2 value.bv

theorem encode_u32_refines (value : U32) :
    FastSszRust.scalar.encode_u32 value ⦃ encoded =>
      Ssz.serialize (.uint 4) (.uint value.val) = .ok (bytesToSpec encoded.val) ⦄ := by
  simpa [FastSszRust.scalar.encode_u32, core.num.U32.to_le_bytes,
    bytesToSpec, byteToSpec, List.map_map, Function.comp_def]
    using serialize_uint_bits 4 value.bv

theorem encode_u64_refines (value : U64) :
    FastSszRust.scalar.encode_u64 value ⦃ encoded =>
      Ssz.serialize (.uint 8) (.uint value.val) = .ok (bytesToSpec encoded.val) ⦄ := by
  simpa [FastSszRust.scalar.encode_u64, core.num.U64.to_le_bytes,
    bytesToSpec, byteToSpec, List.map_map, Function.comp_def]
    using serialize_uint_bits 8 value.bv

theorem encode_u128_refines (value : U128) :
    FastSszRust.scalar.encode_u128 value ⦃ encoded =>
      Ssz.serialize (.uint 16) (.uint value.val) = .ok (bytesToSpec encoded.val) ⦄ := by
  simpa [FastSszRust.scalar.encode_u128, core.num.U128.to_le_bytes,
    bytesToSpec, byteToSpec, List.map_map, Function.comp_def]
    using serialize_uint_bits 16 value.bv

def uintResultAgrees {α : Type} (observe : α → Nat) :
    core.result.Result α FastSszRust.scalar.ScalarError → Except Ssz.Err Ssz.Value → Prop
  | .Ok actual, .ok (.uint expected) => observe actual = expected
  | .Err .InvalidLength, .error (.scope _ _) => True
  | _, _ => False

theorem decode_u8_refines (bytes : Slice U8) :
    FastSszRust.scalar.decode_u8 bytes ⦃ actual =>
      uintResultAgrees (fun value : U8 => value.val) actual
        (Ssz.deserialize (.uint 1) (bytesToSpec bytes.val)) ⦄ := by
  unfold FastSszRust.scalar.decode_u8
  step*
  · have shape := array.property
    have parsed := congrArg BitVec.toNat i_post
    simp only [UScalar.bv_toNat, BitVec.toNat_cast] at parsed
    simp_all [uintResultAgrees, deserialize_uint_form, readUint_bytesToSpec]
    rw [r_post]
  · simp_all [uintResultAgrees, deserialize_uint_form]

theorem decode_u16_refines (bytes : Slice U8) :
    FastSszRust.scalar.decode_u16 bytes ⦃ actual =>
      uintResultAgrees (fun value : U16 => value.val) actual
        (Ssz.deserialize (.uint 2) (bytesToSpec bytes.val)) ⦄ := by
  unfold FastSszRust.scalar.decode_u16
  step*
  · have shape := array.property
    have parsed := congrArg BitVec.toNat i_post
    simp only [UScalar.bv_toNat, BitVec.toNat_cast] at parsed
    simp_all [uintResultAgrees, deserialize_uint_form, readUint_bytesToSpec]
    rw [r_post]
  · simp_all [uintResultAgrees, deserialize_uint_form]

theorem decode_u32_refines (bytes : Slice U8) :
    FastSszRust.scalar.decode_u32 bytes ⦃ actual =>
      uintResultAgrees (fun value : U32 => value.val) actual
        (Ssz.deserialize (.uint 4) (bytesToSpec bytes.val)) ⦄ := by
  unfold FastSszRust.scalar.decode_u32
  step*
  · have shape := array.property
    have parsed := congrArg BitVec.toNat i_post
    simp only [UScalar.bv_toNat, BitVec.toNat_cast] at parsed
    simp_all [uintResultAgrees, deserialize_uint_form, readUint_bytesToSpec]
    rw [r_post]
  · simp_all [uintResultAgrees, deserialize_uint_form]

theorem decode_u64_refines (bytes : Slice U8) :
    FastSszRust.scalar.decode_u64 bytes ⦃ actual =>
      uintResultAgrees (fun value : U64 => value.val) actual
        (Ssz.deserialize (.uint 8) (bytesToSpec bytes.val)) ⦄ := by
  unfold FastSszRust.scalar.decode_u64
  step*
  · have shape := array.property
    have parsed := congrArg BitVec.toNat i_post
    simp only [UScalar.bv_toNat, BitVec.toNat_cast] at parsed
    simp_all [uintResultAgrees, deserialize_uint_form, readUint_bytesToSpec]
    rw [r_post]
  · simp_all [uintResultAgrees, deserialize_uint_form]

theorem decode_u128_refines (bytes : Slice U8) :
    FastSszRust.scalar.decode_u128 bytes ⦃ actual =>
      uintResultAgrees (fun value : U128 => value.val) actual
        (Ssz.deserialize (.uint 16) (bytesToSpec bytes.val)) ⦄ := by
  unfold FastSszRust.scalar.decode_u128
  step*
  · have shape := array.property
    have parsed := congrArg BitVec.toNat i_post
    simp only [UScalar.bv_toNat, BitVec.toNat_cast] at parsed
    simp_all [uintResultAgrees, deserialize_uint_form, readUint_bytesToSpec]
    rw [r_post]
  · simp_all [uintResultAgrees, deserialize_uint_form]

end FastSszVerification
