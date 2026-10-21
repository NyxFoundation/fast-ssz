import NyxSszVerification.Collection.Encode
import NyxSszVerification.Collection.Decode
import NyxSszVerification.Collection.Root

open Aeneas Aeneas.Std

namespace NyxSszVerification

/-- Every vector dictionary composes with the law of its actual child dictionary. -/
theorem vector_codec_refines {T State : Type} (count : Usize)
    (child : NyxSszRust.codec.Ssz T State) (shape : Ssz.Desc) (observe : T → Ssz.Value)
    (law : CodecLaw child shape observe) :
    CodecLaw (NyxSszRust.collections.Vector.Insts.Nyx_sszCodecSszSequenceDecodeState count child)
      (.vector shape count.val) (fun value => .seq (value.values.val.map observe)) := by
  refine ⟨collection_vector_declaration_refines count child shape law.declaration, ?_, ?_, ?_⟩
  · exact collection_encode_vector_refines count child shape observe law
  · exact collection_decode_vector_refines count child shape observe law
  · exact collection_root_vector_refines count child shape observe law

/-- Every bounded-list dictionary composes at all bounds, including zero and usize::MAX. -/
theorem list_codec_refines {T State : Type} (limit : Usize)
    (child : NyxSszRust.codec.Ssz T State) (shape : Ssz.Desc) (observe : T → Ssz.Value)
    (law : CodecLaw child shape observe) :
    CodecLaw (NyxSszRust.collections.List.Insts.Nyx_sszCodecSszSequenceDecodeState limit child)
      (.list shape limit.val) (fun value => .seq (value.values.val.map observe)) := by
  refine ⟨collection_list_declaration_refines limit child shape law.declaration, ?_, ?_, ?_⟩
  · exact collection_encode_list_refines limit child shape observe law
  · exact collection_decode_list_refines limit child shape observe law
  · exact collection_root_list_refines limit child shape observe law

end NyxSszVerification
