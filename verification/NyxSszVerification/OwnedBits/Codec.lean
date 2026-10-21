import NyxSszVerification.OwnedBits.NormalizeVector
import NyxSszVerification.OwnedBits.NormalizeList

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace NyxSszVerification

@[step] theorem owned_vector_encode_refines {N : Usize} (value : NyxSszRust.bitcollections.BitVector N) :
    NyxSszRust.bitcollections.BitVector.Insts.Nyx_sszCodecSszTuple.encode value ⦃ actual =>
      codecEncodingAgrees actual (checkedSerialize (.bitVector N.val) (observeOwnedVector value)) ⦄ := by
  unfold NyxSszRust.bitcollections.BitVector.Insts.Nyx_sszCodecSszTuple.encode
  step*
  simp_all [observeOwnedVector]

@[step] theorem owned_list_encode_refines {MAX : Usize} (value : NyxSszRust.bitcollections.BitList MAX) :
    NyxSszRust.bitcollections.BitList.Insts.Nyx_sszCodecSszTuple.encode value ⦃ actual =>
      codecEncodingAgrees actual (checkedSerialize (.bitList MAX.val) (observeOwnedList value)) ⦄ := by
  unfold NyxSszRust.bitcollections.BitList.Insts.Nyx_sszCodecSszTuple.encode
  step*
  simp_all [observeOwnedList, owned_list_serialize_alias]

@[step] theorem owned_progressive_encode_refines (value : NyxSszRust.bitcollections.ProgressiveBitList) :
    NyxSszRust.bitcollections.ProgressiveBitList.Insts.Nyx_sszCodecSszTuple.encode value ⦃ actual =>
      codecEncodingAgrees actual (checkedSerialize (.progressiveBitList none) (observeOwnedProgressive value)) ⦄ := by
  unfold NyxSszRust.bitcollections.ProgressiveBitList.Insts.Nyx_sszCodecSszTuple.encode
  step*
  simp_all [observeOwnedProgressive]

@[step] theorem owned_vector_decode_refines (N : Usize) (bytes : Slice U8) :
    NyxSszRust.bitcollections.BitVector.Insts.Nyx_sszCodecSszTuple.decode N bytes ⦃ actual =>
      codecDecodingAgrees observeOwnedVector actual (checkedDeserialize (.bitVector N.val) (bytesToSpec bytes.val)) ∧
      (match actual with | .Ok value => canonicalOwnedVector value.encoded.val N.val | .Err _ => True) ⦄ := by
  unfold NyxSszRust.bitcollections.BitVector.Insts.Nyx_sszCodecSszTuple.decode
  apply spec_bind (owned_copy_bytes_refines bytes)
  intro v data
  apply spec_bind (owned_bit_vector_from_ssz_bytes_refines N v)
  intro r agrees
  cases r with
  | Ok value =>
    rcases agrees with ⟨same, canonical⟩
    have decoded := canonical.2.2
    simp_all [codecDecodingAgrees, observeOwnedVector]
  | Err error =>
    rcases agrees with ⟨fault, decoded, agrees⟩
    simp_all [codecDecodingAgrees]

@[step] theorem owned_list_decode_refines (MAX : Usize) (bytes : Slice U8) :
    NyxSszRust.bitcollections.BitList.Insts.Nyx_sszCodecSszTuple.decode MAX bytes ⦃ actual =>
      codecDecodingAgrees observeOwnedList actual (checkedDeserialize (.bitList MAX.val) (bytesToSpec bytes.val)) ∧
      (match actual with | .Ok value => canonicalOwnedList value.encoded.val (some MAX.val) | .Err _ => True) ⦄ := by
  unfold NyxSszRust.bitcollections.BitList.Insts.Nyx_sszCodecSszTuple.decode
  apply spec_bind (owned_copy_bytes_refines bytes)
  intro v data
  apply spec_bind (owned_bit_list_from_ssz_bytes_refines MAX v)
  intro r agrees
  cases r with
  | Ok value =>
    rcases agrees with ⟨same, canonical⟩
    have decoded := canonical.2
    simp_all [codecDecodingAgrees, observeOwnedList, owned_list_deserialize_alias]
  | Err error =>
    rcases agrees with ⟨fault, decoded, agrees⟩
    simp_all [codecDecodingAgrees]

@[step] theorem owned_progressive_decode_refines (bytes : Slice U8) :
    NyxSszRust.bitcollections.ProgressiveBitList.Insts.Nyx_sszCodecSszTuple.decode bytes ⦃ actual =>
      codecDecodingAgrees observeOwnedProgressive actual
        (checkedDeserialize (.progressiveBitList none) (bytesToSpec bytes.val)) ∧
      (match actual with | .Ok value => canonicalOwnedList value.encoded.val none | .Err _ => True) ⦄ := by
  unfold NyxSszRust.bitcollections.ProgressiveBitList.Insts.Nyx_sszCodecSszTuple.decode
  apply spec_bind (owned_copy_bytes_refines bytes)
  intro v data
  apply spec_bind (owned_progressive_bit_list_from_ssz_bytes_refines v)
  intro r agrees
  cases r with
  | Ok value =>
    rcases agrees with ⟨same, canonical⟩
    have decoded := canonical.2
    simp_all [codecDecodingAgrees, observeOwnedProgressive]
  | Err error =>
    rcases agrees with ⟨fault, decoded, agrees⟩
    simp_all [codecDecodingAgrees]

end NyxSszVerification
