import NyxSszVerification.Collection.Layout
import NyxSszVerification.Collection.Ownership
import NyxSszVerification.Collections
import NyxSszVerification.Collection.Count

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace NyxSszVerification

theorem collection_decode_vector_refines {T State : Type} (count : Usize)
    (child : NyxSszRust.codec.Ssz T State) (shape : Ssz.Desc) (observe : T → Ssz.Value)
    (law : CodecLaw child shape observe) (input : Slice U8) :
    NyxSszRust.collection_codec.decode_vector count child input ⦃ actual =>
      codecDecodingAgrees (fun value => .seq (value.values.val.map observe)) actual
        (checkedDeserialize (.vector shape count.val) (bytesToSpec input.val)) ⦄ := by
  unfold NyxSszRust.collection_codec.decode_vector
  apply spec_bind (collection_vector_type_refines count child shape law.declaration)
  intro actual agrees
  cases actual with
  | Err kind =>
    cases validity : (Ssz.Desc.vector shape count.val).wellFormed <;>
      simp_all [codecValidityAgrees, checkedDeserialize, codecDecodingAgrees,
        Bind.bind, Except.bind]
  | Ok resultUnit =>
    cases resultUnit
    have parentValid : (Ssz.Desc.vector shape count.val).wellFormed = .ok () := by
      cases validity : (Ssz.Desc.vector shape count.val).wellFormed with
      | error fault => simp [validity, codecValidityAgrees] at agrees
      | ok resultUnit => cases resultUnit; rfl
    have positive : 0 < count.val := by
      by_contra bad
      have zero : count.val = 0 := by omega
      simp [Ssz.Desc.wellFormed, zero, Bind.bind, Except.bind,
        MonadExcept.throw, throwThe, MonadExceptOf.throw] at parentValid
    have valid : shape.wellFormed = .ok () := by
      simpa [Ssz.Desc.wellFormed, Nat.ne_of_gt positive, Bind.bind, Except.bind,
        Pure.pure, Except.pure] using parentValid
    apply spec_bind (collection_vector_layout_refines child shape law.declaration input count positive)
    intro layout layoutAgrees
    cases layout with
    | Err kind =>
      cases parts : Ssz.vectorSlices shape count.val (bytesToSpec input.val) <;>
        simp_all [sequenceViewAgrees, checkedDeserialize, codecDecodingAgrees,
          Ssz.deserialize, Bind.bind, Except.bind]
    | Ok view =>
      obtain ⟨parts, sliced, viewValid, partsEq⟩ : ∃ parts,
          Ssz.vectorSlices shape count.val (bytesToSpec input.val) = .ok parts ∧
          sequenceViewValid view ∧ (sequenceElements view).map bytesToSpec = parts := by
        cases parts : Ssz.vectorSlices shape count.val (bytesToSpec input.val) <;>
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
        have reference : Ssz.deserialize (.vector shape count.val) (bytesToSpec input.val) =
            .ok (.seq (values.val.map observe)) := by
          simp [Ssz.deserialize, sliced, each, Bind.bind, Except.bind, Pure.pure, Except.pure]
        have counted := collection_deserialize_each_count shape parts _ each
        have length : values.val.length = count.val := by
          simpa only [List.length_map, collection_vector_slices_count shape count.val _ parts sliced]
            using counted
        obtain ⟨stored, storedEq, storedPost⟩ := vector_storage_refines count values
        cases stored with
        | Ok value =>
          simp only at storedPost
          simp [core.result.Result.Insts.CoreOpsTry.branch, storedEq, checkedDeserialize,
            parentValid, reference, codecDecodingAgrees, storedPost.2.1,
            Bind.bind, Except.bind]
        | Err failure =>
          rcases storedPost.2 with zero | wrong
          · omega
          · omega

theorem collection_decode_list_refines {T State : Type} (limit : Usize)
    (child : NyxSszRust.codec.Ssz T State) (shape : Ssz.Desc) (observe : T → Ssz.Value)
    (law : CodecLaw child shape observe) (input : Slice U8) :
    NyxSszRust.collection_codec.decode_list limit child input ⦃ actual =>
      codecDecodingAgrees (fun value => .seq (value.values.val.map observe)) actual
        (checkedDeserialize (.list shape limit.val) (bytesToSpec input.val)) ⦄ := by
  unfold NyxSszRust.collection_codec.decode_list
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
    have parentValid : (Ssz.Desc.list shape limit.val).wellFormed = .ok () := valid
    apply spec_bind (collection_list_layout_refines child shape law.declaration input limit)
    intro layout layoutAgrees
    cases layout with
    | Err kind =>
      cases parts : Ssz.listSlices shape (some limit.val) (bytesToSpec input.val) <;>
        simp_all [sequenceViewAgrees, checkedDeserialize, codecDecodingAgrees,
          Ssz.deserialize, Bind.bind, Except.bind]
    | Ok view =>
      obtain ⟨parts, sliced, viewValid, partsEq⟩ : ∃ parts,
          Ssz.listSlices shape (some limit.val) (bytesToSpec input.val) = .ok parts ∧
          sequenceViewValid view ∧ (sequenceElements view).map bytesToSpec = parts := by
        cases parts : Ssz.listSlices shape (some limit.val) (bytesToSpec input.val) <;>
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
        have reference : Ssz.deserialize (.list shape limit.val) (bytesToSpec input.val) =
            .ok (.seq (values.val.map observe)) := by
          simp [Ssz.deserialize, sliced, each, Bind.bind, Except.bind, Pure.pure, Except.pure]
        have counted := collection_deserialize_each_count shape parts _ each
        have length : values.val.length ≤ limit.val := by
          rw [List.length_map] at counted
          rw [counted]
          exact collection_list_slices_count shape limit.val _ parts sliced
        obtain ⟨stored, storedEq, storedPost⟩ := list_storage_refines limit values
        cases stored with
        | Ok value =>
          simp only at storedPost
          simp [core.result.Result.Insts.CoreOpsTry.branch, storedEq, checkedDeserialize,
            parentValid, reference, codecDecodingAgrees, storedPost.1,
            Bind.bind, Except.bind]
        | Err failure => omega

end NyxSszVerification
