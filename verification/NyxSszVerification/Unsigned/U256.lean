import NyxSszVerification.Unsigned
import NyxSszVerification.Unsigned.Ruint
import NyxSszVerification.Representation.Limbs

open Aeneas Aeneas.Std Aeneas.Std.WP ControlFlow

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace NyxSszVerification

/-- Ruint's least-significant-first limbs as one unsigned bitvector. -/
def u256Bits (value : RustU256) : BitVec 256 :=
  ((value.limbs.val[3]!.bv ++ value.limbs.val[2]!.bv) ++ value.limbs.val[1]!.bv) ++
    value.limbs.val[0]!.bv

def u256Value (value : RustU256) : Nat := (u256Bits value).toNat

theorem u256Bits_bytes (value : RustU256) :
    (u256Bits value).toLEBytes =
      value.limbs.val[0]!.bv.toLEBytes ++ value.limbs.val[1]!.bv.toLEBytes ++
        value.limbs.val[2]!.bv.toLEBytes ++ value.limbs.val[3]!.bv.toLEBytes := by
  unfold u256Bits
  rw [little_endian_append 8 24, little_endian_append 8 16, little_endian_append 8 8]
  simp only [List.append_assoc]

@[step] theorem encode_u64_bytes (value : U64) :
    NyxSszRust.scalar.encode_u64 value ⦃ encoded =>
      encoded.val = value.bv.toLEBytes.map (@UScalar.mk .U8) ⦄ := by
  simp [NyxSszRust.scalar.encode_u64, core.num.U64.to_le_bytes]

@[step] theorem u64_decode_bytes (bytes : Array U8 8#usize) :
    (lift (core.num.U64.from_le_bytes bytes) : RustM U64) ⦃ value =>
      value.bv.toLEBytes.map (@UScalar.mk .U8) = bytes.val ⦄ := by
  simp only [spec_ok, lift, core.num.U64.from_le_bytes]
  rw [little_endian_cast, little_endian_roundtrip]
  simp only [List.map_map, Function.comp_def]
  have identity : (fun value : U8 => (UScalar.mk value.bv : U8)) = id := by
    funext value
    cases value
    rfl
  rw [identity, List.map_id]

theorem encode_u256_refines (value : RustU256) :
    NyxSszRust.scalar.encode_u256 value ⦃ encoded =>
      Ssz.serialize (.uint 32) (.uint (u256Value value)) =
        .ok (bytesToSpec encoded.val) ⦄ := by
  unfold NyxSszRust.scalar.encode_u256
  step*
  have aSize : a.val.length = 8 := by have shape := a.property; scalar_tac
  have bSize : b.val.length = 8 := by have shape := b.property; scalar_tac
  have cSize : c.val.length = 8 := by have shape := c.property; scalar_tac
  have dSize : d.val.length = 8 := by have shape := d.property; scalar_tac
  have blocks : (u256Bits value).toLEBytes.map (@UScalar.mk .U8) =
      a.val ++ b.val ++ c.val ++ d.val := by
    rw [u256Bits_bytes]
    simp_all only [List.map_append, List.Inhabited_getElem_eq_getElem!]
  change Ssz.serialize (.uint 32) (.uint (u256Bits value).toNat) = _
  rw [serialize_uint_bits 32 (u256Bits value), ← bytesToSpec_of_bits, blocks]
  rw [← list_eight_eta a.val aSize, ← list_eight_eta b.val bSize,
    ← list_eight_eta c.val cSize, ← list_eight_eta d.val dSize]
  simp_all only [Array.make, List.Inhabited_getElem_eq_getElem!, List.cons_append, List.nil_append]

theorem decode_u256_refines (bytes : Slice U8) :
    NyxSszRust.scalar.decode_u256 bytes ⦃ actual =>
      uintResultAgrees u256Value actual
        (Ssz.deserialize (.uint 32) (bytesToSpec bytes.val)) ⦄ := by
  unfold NyxSszRust.scalar.decode_u256
  step*
  · have size : array.val.length = 32 := by have shape := array.property; scalar_tac
    have assembled : (u256Bits u).toLEBytes.map (@UScalar.mk .U8) = array.val := by
      rw [u256Bits_bytes]
      simp only [u_post, Array.make, List.getElem!_cons_zero, List.getElem!_cons_succ,
        List.map_append]
      rw [a_post, b_post, c_post, d_post]
      simp only [Array.make, List.cons_append, List.nil_append]
      rw [← list_thirtytwo_eta array.val size]
      simp_all only [List.Inhabited_getElem_eq_getElem!]
    have encoded : bytesToSpec array.val = Ssz.uintBytes 32 (u256Value u) := by
      rw [← assembled, bytesToSpec_of_bits, little_endian_encode_refines 32 (u256Bits u)]
      rfl
    have decoded : Ssz.readUint (bytesToSpec array.val) 0 32 = u256Value u := by
      rw [encoded]
      exact Ssz.readUint_uintBytes _ _ (u256Bits u).isLt
    simp_all [uintResultAgrees, deserialize_uint_form, Ssz.uintBytes_size]
  · simp_all [uintResultAgrees, deserialize_uint_form]

end NyxSszVerification
