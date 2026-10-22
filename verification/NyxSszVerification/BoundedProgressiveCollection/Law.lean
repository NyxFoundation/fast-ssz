import NyxSszVerification.BoundedProgressiveCollection.Codec
import NyxSszVerification.BoundedProgressiveCollection.Root
import NyxSszVerification.BoundedProgressiveCollection.Ownership

open Aeneas Aeneas.Std

namespace NyxSszVerification

/-- Every native capacity composes with only the actual child dictionary's full law. -/
theorem bounded_progressive_list_codec_refines {T State : Type} (limit : Usize)
    (child : NyxSszRust.codec.Ssz T State) (shape : Ssz.Desc) (observe : T → Ssz.Value)
    (law : CodecLaw child shape observe) :
    CodecLaw (NyxSszRust.collections.BoundedProgressiveList.Insts.Nyx_sszCodecSszSequenceDecodeState limit child)
      (.progressiveList shape (some limit.val)) (fun value => .seq (value.values.val.map observe)) := by
  refine ⟨bounded_progressive_collection_declaration_refines limit child shape law.declaration, ?_, ?_, ?_⟩
  · exact bounded_progressive_collection_encode_refines limit child shape observe law
  · exact bounded_progressive_collection_decode_refines limit child shape observe law
  · exact bounded_progressive_collection_root_refines limit child shape observe law

end NyxSszVerification
