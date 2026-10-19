import NyxSszVerification.Bitfield.Pack
import NyxSszVerification.Bitfield.Unpack
import NyxSszVerification.Bytes

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace NyxSszVerification

def bitFaultAgrees : NyxSszRust.bitfield.BitfieldError → Ssz.Err → Prop
  | .EmptyVector, .vectorEmpty => True
  | .InvalidLength, .scope _ _ => True
  | .PaddingBits, .paddingBits => True
  | .OverLimit, .overLimit _ _ => True
  | .EmptyEncoding, .emptyEncoding => True
  | .NoDelimiter, .noDelimiter => True
  | .TrailingZeros, .trailingZeros => True
  | _, _ => False

def bitEncodingAgrees : core.result.Result (alloc.vec.Vec U8) NyxSszRust.bitfield.BitfieldError →
    Except Ssz.Err Ssz.Bytes → Prop
  | .Ok output, .ok bytes => bytesToSpec output.val = bytes
  | .Err actual, .error expected => bitFaultAgrees actual expected
  | _, _ => False

def bitDecodingAgrees : core.result.Result (alloc.vec.Vec Bool) NyxSszRust.bitfield.BitfieldError →
    Except Ssz.Err Ssz.Value → Prop
  | .Ok output, .ok (.bits bits) => bitsToSpec output.val = bits
  | .Err actual, .error expected => bitFaultAgrees actual expected
  | _, _ => False

@[step] theorem encode_bit_vector_refines (bits : Slice Bool) (length : Usize) :
    NyxSszRust.bitfield.encode_bit_vector bits length ⦃ actual =>
      bitEncodingAgrees actual
        (checkedSerialize (.bitVector length.val) (.bits (bitsToSpec bits.val))) ⦄ := by
  unfold NyxSszRust.bitfield.encode_bit_vector
  step*
  all_goals
    simp_all [checkedSerialize, Ssz.Desc.wellFormed, Ssz.serialize, bitEncodingAgrees,
      bitFaultAgrees, Bind.bind, Except.bind]

@[step] theorem decode_bit_vector_refines (bytes : Slice U8) (length : Usize) :
    NyxSszRust.bitfield.decode_bit_vector bytes length ⦃ actual =>
      bitDecodingAgrees actual
        (checkedDeserialize (.bitVector length.val) (bytesToSpec bytes.val)) ⦄ := by
  unfold NyxSszRust.bitfield.decode_bit_vector
  step*
  all_goals
    simp_all [checkedDeserialize, Ssz.Desc.wellFormed, Ssz.deserialize, bitDecodingAgrees,
      bitFaultAgrees, bytesToSpec_getElem, byte_shift_zero_nat, Nat.one_le_iff_ne_zero,
      Bind.bind, Except.bind, Pure.pure, Except.pure, MonadExcept.throw, throwThe,
      MonadExceptOf.throw]

end NyxSszVerification
