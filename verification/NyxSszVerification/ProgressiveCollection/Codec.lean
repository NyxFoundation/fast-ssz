import NyxSszRust.ProgressiveCodec
import NyxSszVerification.Collection.Encode
import NyxSszVerification.Collection.Decode

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxHeartbeats 2000000

namespace NyxSszVerification

@[step] theorem progressive_collection_declaration_refines {T State : Type}
    (child : NyxSszRust.codec.Ssz T State) (shape : Ssz.Desc)
    (declared : child.TYPE ⦃ actual => typeDescriptorToSpec actual = shape ⦄) :
    NyxSszRust.collections.ProgressiveList.Insts.Nyx_sszCodecSszSequenceDecodeState.TYPE child
      ⦃ actual => typeDescriptorToSpec actual = .progressiveList shape none ⦄ := by
  simp only [NyxSszRust.collections.ProgressiveList.Insts.Nyx_sszCodecSszSequenceDecodeState.TYPE]
  apply spec_bind declared
  intro actual correct
  simp [typeDescriptorToSpec, correct]

theorem progressive_collection_encode_refines {T State : Type}
    (child : NyxSszRust.codec.Ssz T State) (shape : Ssz.Desc) (observe : T → Ssz.Value)
    (law : CodecLaw child shape observe) (value : NyxSszRust.collections.ProgressiveList T) :
    NyxSszRust.collections.ProgressiveList.Insts.Nyx_sszCodecSszSequenceDecodeState.encode child value
      ⦃ actual => codecEncodingAgrees actual
        (checkedSerialize (.progressiveList shape none) (.seq (value.values.val.map observe))) ⦄ := by
  unfold NyxSszRust.collections.ProgressiveList.Insts.Nyx_sszCodecSszSequenceDecodeState.encode
  apply spec_bind (codec_validate_type_refines child shape law.declaration)
  intro actual agrees
  cases actual with
  | Err kind =>
    cases validity : shape.wellFormed <;>
      simp_all [codecValidityAgrees, checkedSerialize, codecEncodingAgrees, Ssz.Desc.wellFormed,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        Bind.bind, Except.bind]
  | Ok resultUnit =>
    cases resultUnit
    have valid : shape.wellFormed = .ok () := by
      cases validity : shape.wellFormed with
      | error fault => simp [validity, codecValidityAgrees] at agrees
      | ok resultUnit => cases resultUnit; rfl
    simpa [core.result.Result.Insts.CoreOpsTry.branch,
      NyxSszRust.collections.ProgressiveList.as_slice, checkedSerialize, Ssz.Desc.wellFormed,
      valid, Ssz.serialize, Ssz.boundCheck, Bind.bind, Except.bind] using
        collection_encode_sequence_refines child shape observe law valid (alloc.vec.Vec.deref value.values)

/-- Layout and child decode failures retain the actual owned sequence state unchanged. -/
theorem progressive_collection_decode_refines {T State : Type}
    (child : NyxSszRust.codec.Ssz T State) (shape : Ssz.Desc) (observe : T → Ssz.Value)
    (law : CodecLaw child shape observe) (input : Slice U8) :
    NyxSszRust.progressive_codec.decode_progressive child input ⦃ actual =>
      codecDecodingAgrees (fun value => .seq (value.values.val.map observe)) actual
        (checkedDeserialize (.progressiveList shape none) (bytesToSpec input.val)) ⦄ := by
  unfold NyxSszRust.progressive_codec.decode_progressive
  apply spec_bind (codec_validate_type_refines child shape law.declaration)
  intro actual agrees
  cases actual with
  | Err kind =>
    cases validity : shape.wellFormed <;>
      simp_all [codecValidityAgrees, checkedDeserialize, codecDecodingAgrees,
        Ssz.Desc.wellFormed, Bind.bind, Except.bind]
  | Ok resultUnit =>
    cases resultUnit
    have valid : shape.wellFormed = .ok () := by
      cases validity : shape.wellFormed with
      | error fault => simp [validity, codecValidityAgrees] at agrees
      | ok resultUnit => cases resultUnit; rfl
    have parentValid : (Ssz.Desc.progressiveList shape none).wellFormed = .ok () := valid
    apply spec_bind (collection_list_layout_refines child shape law.declaration input none)
    intro layout layoutAgrees
    cases layout with
    | Err kind =>
      cases parts : Ssz.listSlices shape none (bytesToSpec input.val) <;>
        simp_all [sequenceViewAgrees, checkedDeserialize, codecDecodingAgrees,
          Ssz.deserialize, Bind.bind, Except.bind]
    | Ok view =>
      obtain ⟨parts, sliced, viewValid, partsEq⟩ : ∃ parts,
          Ssz.listSlices shape none (bytesToSpec input.val) = .ok parts ∧
          sequenceViewValid view ∧ (sequenceElements view).map bytesToSpec = parts := by
        cases parts : Ssz.listSlices shape none (bytesToSpec input.val) <;>
          simp_all [sequenceViewAgrees]
      apply spec_bind (decode_elements_reference child shape observe law valid view viewValid)
      intro decoded decodedAgrees
      have bodies : rangeBodies view.input view.ranges.val = parts := by
        simpa [rangeBodies, sequenceElements, List.map_map, Function.comp_def] using partsEq
      rw [bodies] at decodedAgrees
      cases decoded with
      | Err failure =>
        cases each : Ssz.deserializeEach shape parts <;>
          simp_all [sequenceListsAgrees, sequenceResultToLists, checkedDeserialize,
            codecDecodingAgrees, Ssz.deserialize, Bind.bind, Except.bind,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
      | Ok values =>
        have each : Ssz.deserializeEach shape parts = .ok (values.val.map observe) := by
          cases each : Ssz.deserializeEach shape parts <;>
            simp_all [sequenceListsAgrees, sequenceResultToLists]
        have reference : Ssz.deserialize (.progressiveList shape none) (bytesToSpec input.val) =
            .ok (.seq (values.val.map observe)) := by
          simp [Ssz.deserialize, sliced, each, Bind.bind, Except.bind, Pure.pure, Except.pure]
        obtain ⟨stored, storedEq, storedPost⟩ := progressive_list_refines values
        simp [core.result.Result.Insts.CoreOpsTry.branch, storedEq, checkedDeserialize,
          parentValid, reference, codecDecodingAgrees, storedPost, Bind.bind, Except.bind]

end NyxSszVerification
