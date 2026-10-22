import NyxSszVerification.BoundedProgressiveBits.Storage

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace NyxSszVerification

@[step] theorem owned_bounded_progressive_encode_refines {MAX : Usize} (value : NyxSszRust.bitcollections.BoundedProgressiveBitList MAX) :
    NyxSszRust.bitcollections.BoundedProgressiveBitList.Insts.Nyx_sszCodecSszTuple.encode value ⦃ actual =>
      codecEncodingAgrees actual (checkedSerialize (.progressiveBitList (some MAX.val)) (observeOwnedBoundedProgressive value)) ⦄ := by
  unfold NyxSszRust.bitcollections.BoundedProgressiveBitList.Insts.Nyx_sszCodecSszTuple.encode
  step*
  simp_all [observeOwnedBoundedProgressive]

@[step] theorem owned_bounded_progressive_decode_refines (MAX : Usize) (bytes : Slice U8) :
    NyxSszRust.bitcollections.BoundedProgressiveBitList.Insts.Nyx_sszCodecSszTuple.decode MAX bytes ⦃ actual =>
      codecDecodingAgrees observeOwnedBoundedProgressive actual (checkedDeserialize (.progressiveBitList (some MAX.val)) (bytesToSpec bytes.val)) ∧
      (match actual with | .Ok value => canonicalOwnedList value.encoded.val (some MAX.val) | .Err _ => True) ⦄ := by
  unfold NyxSszRust.bitcollections.BoundedProgressiveBitList.Insts.Nyx_sszCodecSszTuple.decode
  apply spec_bind (owned_copy_bytes_refines bytes)
  intro v data
  apply spec_bind (owned_bounded_progressive_bit_list_from_ssz_bytes_refines MAX v)
  intro r agrees
  cases r with
  | Ok value =>
    rcases agrees with ⟨same, canonical⟩
    have decoded := canonical.2
    simp_all [codecDecodingAgrees, observeOwnedBoundedProgressive]
  | Err error =>
    rcases agrees with ⟨fault, decoded, agrees⟩
    simp_all [codecDecodingAgrees]

end NyxSszVerification
