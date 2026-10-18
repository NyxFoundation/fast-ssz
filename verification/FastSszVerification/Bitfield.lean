import FastSszVerification.Bitfield.Pack
import FastSszVerification.Bitfield.Unpack
import FastSszVerification.Bytes

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace FastSszVerification

def bitFaultAgrees : FastSszRust.bitfield.BitfieldError → Ssz.Err → Prop
  | .EmptyVector, .vectorEmpty => True
  | .InvalidLength, .scope _ _ => True
  | .PaddingBits, .paddingBits => True
  | _, _ => False

def bitEncodingAgrees : core.result.Result (alloc.vec.Vec U8) FastSszRust.bitfield.BitfieldError →
    Except Ssz.Err Ssz.Bytes → Prop
  | .Ok output, .ok bytes => bytesToSpec output.val = bytes
  | .Err actual, .error expected => bitFaultAgrees actual expected
  | _, _ => False

def bitDecodingAgrees : core.result.Result (alloc.vec.Vec Bool) FastSszRust.bitfield.BitfieldError →
    Except Ssz.Err Ssz.Value → Prop
  | .Ok output, .ok (.bits bits) => bitsToSpec output.val = bits
  | .Err actual, .error expected => bitFaultAgrees actual expected
  | _, _ => False

@[step] theorem encode_bit_vector_refines (bits : Slice Bool) (length : Usize) :
    FastSszRust.bitfield.encode_bit_vector bits length ⦃ actual =>
      bitEncodingAgrees actual
        (checkedSerialize (.bitVector length.val) (.bits (bitsToSpec bits.val))) ⦄ := by
  unfold FastSszRust.bitfield.encode_bit_vector
  step*
  all_goals
    simp_all [checkedSerialize, Ssz.Desc.wellFormed, Ssz.serialize, bitEncodingAgrees,
      bitFaultAgrees, Bind.bind, Except.bind]

@[step] theorem decode_bit_vector_refines (bytes : Slice U8) (length : Usize) :
    FastSszRust.bitfield.decode_bit_vector bytes length ⦃ actual =>
      bitDecodingAgrees actual
        (checkedDeserialize (.bitVector length.val) (bytesToSpec bytes.val)) ⦄ := by
  unfold FastSszRust.bitfield.decode_bit_vector
  step*
  all_goals
    simp_all [checkedDeserialize, Ssz.Desc.wellFormed, Ssz.deserialize, bitDecodingAgrees,
      bitFaultAgrees, bytesToSpec_getElem, byte_shift_zero_nat, Nat.one_le_iff_ne_zero,
      Bind.bind, Except.bind, Pure.pure, Except.pure, MonadExcept.throw, throwThe,
      MonadExceptOf.throw]

end FastSszVerification
