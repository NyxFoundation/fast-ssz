import NyxSszVerification.ProgressiveCollection.Codec
import NyxSszVerification.ProgressiveCollection.Root
import NyxSszVerification.ProgressiveCollection.Ownership

open Aeneas Aeneas.Std

namespace NyxSszVerification

/-- The actual unbounded progressive-list dictionary composes with its actual child's law. -/
theorem progressive_list_codec_refines {T State : Type}
    (child : NyxSszRust.codec.Ssz T State) (shape : Ssz.Desc) (observe : T → Ssz.Value)
    (law : CodecLaw child shape observe) :
    CodecLaw (NyxSszRust.collections.ProgressiveList.Insts.Nyx_sszCodecSszSequenceDecodeState child)
      (.progressiveList shape none) (fun value => .seq (value.values.val.map observe)) := by
  refine ⟨progressive_collection_declaration_refines child shape law.declaration, ?_, ?_, ?_⟩
  · exact progressive_collection_encode_refines child shape observe law
  · exact progressive_collection_decode_refines child shape observe law
  · exact progressive_collection_root_refines child shape observe law

end NyxSszVerification
