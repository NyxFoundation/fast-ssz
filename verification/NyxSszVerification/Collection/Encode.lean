import NyxSszVerification.Collection.Assemble
import NyxSszVerification.Collection.Native
import NyxSszVerification.Collection.Metadata

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxHeartbeats 2000000

namespace NyxSszVerification

@[step] theorem collection_encode_sequence_refines {T State : Type}
    (child : NyxSszRust.codec.Ssz T State) (shape : Ssz.Desc) (observe : T → Ssz.Value)
    (law : CodecLaw child shape observe) (valid : shape.wellFormed = .ok ()) (values : Slice T) :
    NyxSszRust.collection_wire.encode_sequence child values ⦃ actual =>
      codecEncodingAgrees actual (Ssz.serializeSequence shape (values.val.map observe)) ⦄ := by
  unfold NyxSszRust.collection_wire.encode_sequence
  apply spec_bind (collection_encode_parts_refines child shape observe law valid values)
  intro actual correct
  cases actual with
  | Err kind =>
    cases encoded : Ssz.serializeEach shape (values.val.map observe) <;>
      simp_all [collectionPartsAgrees, Ssz.serializeSequence, codecEncodingAgrees,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        Bind.bind, Except.bind]
  | Ok held =>
    cases held with
    | none =>
      obtain ⟨data, encoded, large⟩ : ∃ data,
          Ssz.serializeEach shape (values.val.map observe) = .ok data ∧
          ∃ part ∈ data, Usize.max < part.size := by
        cases encoded : Ssz.serializeEach shape (values.val.map observe) <;>
          simp_all [collectionPartsAgrees]
      obtain ⟨fault, refused, faultAgrees⟩ := collection_assemble_native data shape.isFixed large
      have reference : Ssz.serializeSequence shape (values.val.map observe) = .error fault := by
        simp only [Ssz.serializeSequence, encoded, Bind.bind, Except.bind, refused]
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]
      apply spec_bind (codec_fixed_size_refines child shape law.declaration)
      intro width widthAgrees
      cases width with
      | Ok held => cases held <;> simpa [reference, codecEncodingAgrees] using faultAgrees
      | Err kind =>
        cases expected : shape.fixedSize <;> cases kind <;>
          simp_all [codecWidthAgrees, codecEncodingAgrees]
    | some parts =>
      have encoded : Ssz.serializeEach shape (values.val.map observe) =
          .ok (parts.val.map fun part => bytesToSpec part.val) := by
        cases encoded : Ssz.serializeEach shape (values.val.map observe) <;>
          simp_all [collectionPartsAgrees]
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]
      apply spec_bind (codec_fixed_size_refines child shape law.declaration)
      intro width widthAgrees
      have finish (fixed : Bool) (same : fixed = shape.isFixed) :
          NyxSszRust.collection_wire.assemble (alloc.vec.Vec.deref parts) fixed ⦃ actual =>
            codecEncodingAgrees actual (Ssz.serializeSequence shape (values.val.map observe)) ⦄ := by
        simpa only [Ssz.serializeSequence, encoded, Bind.bind, Except.bind,
          collection_deref_values, same] using collection_assemble_refines (alloc.vec.Vec.deref parts) fixed
      cases width with
      | Ok held =>
        cases held with
        | none =>
          have variableWidth : shape.fixedSize = none := by
            cases expected : shape.fixedSize <;> simp_all [codecWidthAgrees]
          exact finish false (by simp [Ssz.Desc.isFixed, variableWidth])
        | some width =>
          have fixed : shape.fixedSize.isSome = true := by
            cases expected : shape.fixedSize <;> simp_all [codecWidthAgrees]
          exact finish true fixed.symm
      | Err kind =>
        cases expected : shape.fixedSize <;> cases kind <;> simp only [expected, codecWidthAgrees] at widthAgrees
        exact finish true (by simp [Ssz.Desc.isFixed, expected])
theorem collection_encode_vector_refines {T State : Type} (count : Usize)
    (child : NyxSszRust.codec.Ssz T State) (shape : Ssz.Desc) (observe : T → Ssz.Value)
    (law : CodecLaw child shape observe) (value : NyxSszRust.collections.Vector T count) :
    NyxSszRust.collections.Vector.Insts.Nyx_sszCodecSszSequenceDecodeState.encode child value
      ⦃ actual => codecEncodingAgrees actual
        (checkedSerialize (.vector shape count.val) (.seq (value.values.val.map observe))) ⦄ := by
  unfold NyxSszRust.collections.Vector.Insts.Nyx_sszCodecSszSequenceDecodeState.encode
  apply spec_bind (collection_vector_type_refines count child shape law.declaration)
  intro actual agrees
  cases actual with
  | Err kind =>
    cases validity : (Ssz.Desc.vector shape count.val).wellFormed <;>
      simp_all [codecValidityAgrees, checkedSerialize, codecEncodingAgrees,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
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
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok,
      NyxSszRust.collections.Vector.as_slice]
    by_cases length : value.values.val.length = count.val
    · have equal : Slice.len (alloc.vec.Vec.deref value.values) = count := by scalar_tac
      simpa [equal, checkedSerialize, parentValid, Ssz.serialize, length,
        Bind.bind, Except.bind] using
        collection_encode_sequence_refines child shape observe law valid (alloc.vec.Vec.deref value.values)
    · simp [bne_iff_ne, checkedSerialize, parentValid, Ssz.serialize, length,
        codecEncodingAgrees, codecFaultAgrees, Bind.bind, Except.bind]

theorem collection_encode_list_refines {T State : Type} (limit : Usize)
    (child : NyxSszRust.codec.Ssz T State) (shape : Ssz.Desc) (observe : T → Ssz.Value)
    (law : CodecLaw child shape observe) (value : NyxSszRust.collections.List T limit) :
    NyxSszRust.collections.List.Insts.Nyx_sszCodecSszSequenceDecodeState.encode child value
      ⦃ actual => codecEncodingAgrees actual
        (checkedSerialize (.list shape limit.val) (.seq (value.values.val.map observe))) ⦄ := by
  unfold NyxSszRust.collections.List.Insts.Nyx_sszCodecSszSequenceDecodeState.encode
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
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok,
      NyxSszRust.collections.List.as_slice]
    by_cases length : value.values.val.length ≤ limit.val
    · simpa [Nat.not_lt.mpr length, checkedSerialize, Ssz.Desc.wellFormed, valid, Ssz.serialize, length,
        Bind.bind, Except.bind] using
        collection_encode_sequence_refines child shape observe law valid (alloc.vec.Vec.deref value.values)
    · simp [Nat.lt_of_not_ge length, checkedSerialize, Ssz.Desc.wellFormed, valid, Ssz.serialize, length,
        codecEncodingAgrees, codecFaultAgrees, Bind.bind, Except.bind]

end NyxSszVerification
