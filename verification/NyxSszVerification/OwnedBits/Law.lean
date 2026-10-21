import NyxSszVerification.OwnedBits.Roots

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace NyxSszVerification

/-- The law quantifies over all extracted struct values; no canonical-storage premise. -/
theorem owned_bit_vector_codec_refines (N : Usize) :
    CodecLaw (NyxSszRust.bitcollections.BitVector.Insts.Nyx_sszCodecSszTuple N)
      (.bitVector N.val) observeOwnedVector := by
  constructor
  · simp [NyxSszRust.bitcollections.BitVector.Insts.Nyx_sszCodecSszTuple.TYPE, typeDescriptorToSpec]
  · exact owned_vector_encode_refines
  · intro bytes
    exact spec_mono (owned_vector_decode_refines N bytes) (fun _ correct => correct.1)
  · exact owned_vector_root_refines

/-- Bounded packed storage retains exact over-limit refusal before normalization. -/
theorem owned_bit_list_codec_refines (MAX : Usize) :
    CodecLaw (NyxSszRust.bitcollections.BitList.Insts.Nyx_sszCodecSszTuple MAX)
      (.bitList MAX.val) observeOwnedList := by
  constructor
  · simp [NyxSszRust.bitcollections.BitList.Insts.Nyx_sszCodecSszTuple.TYPE, typeDescriptorToSpec]
  · exact owned_list_encode_refines
  · intro bytes
    exact spec_mono (owned_list_decode_refines MAX bytes) (fun _ correct => correct.1)
  · exact owned_list_root_refines

/-- Unbounded packed lists mix in the actual widened bit count. -/
theorem owned_progressive_bit_list_codec_refines :
    CodecLaw NyxSszRust.bitcollections.ProgressiveBitList.Insts.Nyx_sszCodecSszTuple
      (.progressiveBitList none) observeOwnedProgressive := by
  constructor
  · simp [NyxSszRust.bitcollections.ProgressiveBitList.Insts.Nyx_sszCodecSszTuple.TYPE, typeDescriptorToSpec]
  · exact owned_progressive_encode_refines
  · intro bytes
    exact spec_mono (owned_progressive_decode_refines bytes) (fun _ correct => correct.1)
  · exact owned_progressive_root_refines

end NyxSszVerification
