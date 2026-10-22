import NyxSszVerification.BoundedProgressiveBits.Codec

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace NyxSszVerification

/-- The unchanged Progressive layout ignores its optional context cap for every logical value. -/
theorem bounded_progressive_bits_root_alias (limit : Nat) (bits : _root_.Array Bool) :
    checkedHashTreeRoot (.progressiveBitList (some limit)) (.bits bits) =
      checkedHashTreeRoot (.progressiveBitList none) (.bits bits) := by
  simp only [checkedHashTreeRoot, Ssz.Desc.wellFormed, Ssz.hashTreeRoot,
    Ssz.Desc.nesting, Ssz.hashTreeRootAt, Ssz.merkleLayout]

/-- Rooting uses exactly the existing Progressive spine, including malformed private states. -/
theorem owned_bounded_progressive_root_refines {MAX : Usize}
    (value : NyxSszRust.bitcollections.BoundedProgressiveBitList MAX) :
    NyxSszRust.bitcollections.BoundedProgressiveBitList.Insts.Nyx_sszCodecSszTuple.hash_tree_root value
      ⦃ actual => codecRootAgrees actual
        (checkedHashTreeRoot (.progressiveBitList (some MAX.val)) (observeOwnedBoundedProgressive value)) ⦄ := by
  simpa only [NyxSszRust.bitcollections.BoundedProgressiveBitList.Insts.Nyx_sszCodecSszTuple.hash_tree_root,
    NyxSszRust.bitcollections.ProgressiveBitList.Insts.Nyx_sszCodecSszTuple.hash_tree_root,
    NyxSszRust.bitcollections.ProgressiveBitList.Insts.Nyx_sszCodecSszTuple.encode,
    NyxSszRust.bitcollections.ProgressiveBitList.as_ssz_bytes,
    NyxSszRust.bitcollections.BoundedProgressiveBitList.as_ssz_bytes,
    observeOwnedBoundedProgressive, observeOwnedProgressive, bounded_progressive_bits_root_alias,
    bind_assoc_eq, bind_tc_ok]
    using owned_progressive_root_refines ⟨value.encoded⟩

/-- Every native bound retains Some(MAX) in the complete dictionary declaration. -/
theorem owned_bounded_progressive_bit_list_codec_refines (MAX : Usize) :
    CodecLaw (NyxSszRust.bitcollections.BoundedProgressiveBitList.Insts.Nyx_sszCodecSszTuple MAX)
      (.progressiveBitList (some MAX.val)) observeOwnedBoundedProgressive := by
  constructor
  · simp [NyxSszRust.bitcollections.BoundedProgressiveBitList.Insts.Nyx_sszCodecSszTuple.TYPE,
      typeDescriptorToSpec]
  · exact owned_bounded_progressive_encode_refines
  · intro bytes
    exact spec_mono (owned_bounded_progressive_decode_refines MAX bytes) (fun _ correct => correct.1)
  · exact owned_bounded_progressive_root_refines

end NyxSszVerification
