import NyxSszRust.CollectionCodec
import NyxSszVerification.Codec.Elements

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace NyxSszVerification

/-- Layout and declaration failures carry neither completed values nor child state. -/
@[simp] theorem collection_empty_failure {T State : Type}
    (child : NyxSszRust.codec.Ssz T State) (kind : NyxSszRust.error.CodecError) :
    NyxSszRust.collection_codec.empty_failure child kind =
      RustM.ok ⟨kind, ⟨alloc.vec.Vec.new T, none⟩⟩ := rfl

/-- Storage rejection returns every decoded value, without manufacturing child state. -/
theorem collection_storage_failure {T State : Type}
    (child : NyxSszRust.codec.Ssz T State) (failure : NyxSszRust.collections.LengthError T) :
    NyxSszRust.collection_codec.storage_failure child failure ⦃ actual =>
      actual.state.values = failure.values ∧ actual.state.child = none ⦄ := by
  unfold NyxSszRust.collection_codec.storage_failure
  split <;> simp

/-- A rejected vector declaration leaves the initial owned state empty. -/
theorem vector_decode_declaration_failure {T State : Type} (count : Usize)
    (child : NyxSszRust.codec.Ssz T State) (input : Slice U8)
    (kind : NyxSszRust.error.CodecError)
    (rejected : NyxSszRust.collection_codec.vector_type count child = RustM.ok (.Err kind)) :
    NyxSszRust.collection_codec.decode_vector count child input =
      RustM.ok (.Err ⟨kind, ⟨alloc.vec.Vec.new T, none⟩⟩) := by
  simp [NyxSszRust.collection_codec.decode_vector, rejected]

/-- A rejected list declaration leaves the initial owned state empty. -/
theorem list_decode_declaration_failure {T State : Type} (limit : Usize)
    (child : NyxSszRust.codec.Ssz T State) (input : Slice U8)
    (kind : NyxSszRust.error.CodecError)
    (rejected : NyxSszRust.codec.validate_type child = RustM.ok (.Err kind)) :
    NyxSszRust.collection_codec.decode_list limit child input =
      RustM.ok (.Err ⟨kind, ⟨alloc.vec.Vec.new T, none⟩⟩) := by
  simp [NyxSszRust.collection_codec.decode_list, rejected]

/-- A layout failure cannot consume an element or create nested failure state. -/
theorem vector_decode_layout_failure {T State : Type} (count : Usize)
    (child : NyxSszRust.codec.Ssz T State) (input : Slice U8)
    (kind : NyxSszRust.error.CodecError)
    (declared : NyxSszRust.collection_codec.vector_type count child = RustM.ok (.Ok ()))
    (rejected : NyxSszRust.collection_codec.vector_layout child input count = RustM.ok (.Err kind)) :
    NyxSszRust.collection_codec.decode_vector count child input =
      RustM.ok (.Err ⟨kind, ⟨alloc.vec.Vec.new T, none⟩⟩) := by
  simp [NyxSszRust.collection_codec.decode_vector, declared, rejected]

/-- List layout rejection has the same empty-state ownership behavior. -/
theorem list_decode_layout_failure {T State : Type} (limit : Usize)
    (child : NyxSszRust.codec.Ssz T State) (input : Slice U8)
    (kind : NyxSszRust.error.CodecError)
    (declared : NyxSszRust.codec.validate_type child = RustM.ok (.Ok ()))
    (rejected : NyxSszRust.collection_codec.list_layout child input (some limit) = RustM.ok (.Err kind)) :
    NyxSszRust.collection_codec.decode_list limit child input =
      RustM.ok (.Err ⟨kind, ⟨alloc.vec.Vec.new T, none⟩⟩) := by
  simp [NyxSszRust.collection_codec.decode_list, declared, rejected]

/-- Parent vector decoding forwards the entire typed callback failure unchanged. -/
theorem vector_decode_callback_failure {T State : Type} (count : Usize)
    (child : NyxSszRust.codec.Ssz T State) (input : Slice U8)
    (view : NyxSszRust.sequence.SequenceView)
    (failure : NyxSszRust.error.DecodeFailure (NyxSszRust.codec.SequenceDecodeState T State))
    (declared : NyxSszRust.collection_codec.vector_type count child = RustM.ok (.Ok ()))
    (layout : NyxSszRust.collection_codec.vector_layout child input count = RustM.ok (.Ok view))
    (callback : NyxSszRust.codec.decode_elements child view = RustM.ok (.Err failure)) :
    NyxSszRust.collection_codec.decode_vector count child input = RustM.ok (.Err failure) := by
  simp [NyxSszRust.collection_codec.decode_vector, declared, layout, callback,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]

/-- Parent list decoding forwards the entire typed callback failure unchanged. -/
theorem list_decode_callback_failure {T State : Type} (limit : Usize)
    (child : NyxSszRust.codec.Ssz T State) (input : Slice U8)
    (view : NyxSszRust.sequence.SequenceView)
    (failure : NyxSszRust.error.DecodeFailure (NyxSszRust.codec.SequenceDecodeState T State))
    (declared : NyxSszRust.codec.validate_type child = RustM.ok (.Ok ()))
    (layout : NyxSszRust.collection_codec.list_layout child input (some limit) = RustM.ok (.Ok view))
    (callback : NyxSszRust.codec.decode_elements child view = RustM.ok (.Err failure)) :
    NyxSszRust.collection_codec.decode_list limit child input = RustM.ok (.Err failure) := by
  simp [NyxSszRust.collection_codec.decode_list, declared, layout, callback,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]

/-- The callback model records the exact owned prefix and exact failing child state. -/
theorem decode_ranges_failure_state {T State : Type}
    (child : NyxSszRust.codec.Ssz T State) (input : Slice U8)
    (range : NyxSszRust.sequence.BodyRange) (rest : List NyxSszRust.sequence.BodyRange)
    (completed : List T) (failure : NyxSszRust.error.DecodeFailure State)
    (callback : NyxSszRust.codec.decode_range child input range.start range.end =
      RustM.ok (.Err failure)) :
    decodeRangesModel child input (range :: rest) completed =
      RustM.ok (.Err ⟨failure.kind, (completed, some failure.state)⟩) := by
  simp [decodeRangesModel, callback]

/-- Retention is stronger than error-code conformance: both state projections are exact. -/
theorem decode_elements_failure_state {T State : Type}
    (child : NyxSszRust.codec.Ssz T State) (shape : Ssz.Desc) (observe : T → Ssz.Value)
    (law : CodecLaw child shape observe) (view : NyxSszRust.sequence.SequenceView)
    (valid : sequenceViewValid view) (kind : NyxSszRust.error.CodecError)
    (completed : List T) (state : State)
    (trace : decodeRangesModel child view.input view.ranges.val [] =
      RustM.ok (.Err ⟨kind, (completed, some state)⟩)) :
    NyxSszRust.codec.decode_elements child view ⦃ actual =>
      ∃ failure, actual = .Err failure ∧ failure.kind = kind ∧
        failure.state.values.val = completed ∧ failure.state.child = some state ⦄ := by
  apply spec_mono (decode_elements_retains child shape observe law view valid)
  intro actual retained
  rw [trace] at retained
  cases actual with
  | Ok values => simp [sequenceResultToLists] at retained
  | Err failure =>
    simp only [sequenceResultToLists, RustM.ok.injEq,
      core.result.Result.Err.injEq] at retained
    cases failure with
    | mk actualKind actualState =>
      cases actualState with
      | mk values nested =>
        simp only [NyxSszRust.error.DecodeFailure.mk.injEq, Prod.mk.injEq] at retained
        exact ⟨_, rfl, retained.1.symm, retained.2.1.symm, retained.2.2.symm⟩

/-- An observed callback trace determines the vector's exact owned failure state. -/
theorem vector_decode_retains_trace {T State : Type} (count : Usize)
    (child : NyxSszRust.codec.Ssz T State) (shape : Ssz.Desc) (observe : T → Ssz.Value)
    (law : CodecLaw child shape observe) (input : Slice U8)
    (view : NyxSszRust.sequence.SequenceView) (valid : sequenceViewValid view)
    (kind : NyxSszRust.error.CodecError) (completed : List T) (state : State)
    (declared : NyxSszRust.collection_codec.vector_type count child = RustM.ok (.Ok ()))
    (layout : NyxSszRust.collection_codec.vector_layout child input count = RustM.ok (.Ok view))
    (trace : decodeRangesModel child view.input view.ranges.val [] =
      RustM.ok (.Err ⟨kind, (completed, some state)⟩)) :
    NyxSszRust.collections.Vector.Insts.Nyx_sszCodecSszSequenceDecodeState.decode count child input
      ⦃ actual => ∃ failure, actual = .Err failure ∧ failure.kind = kind ∧
        failure.state.values.val = completed ∧ failure.state.child = some state ⦄ := by
  obtain ⟨actual, callback, failure, same, kindEq, valuesEq, stateEq⟩ := spec_imp_exists
    (decode_elements_failure_state child shape observe law view valid kind completed state trace)
  subst actual
  rw [NyxSszRust.collections.Vector.Insts.Nyx_sszCodecSszSequenceDecodeState.decode,
    vector_decode_callback_failure count child input view failure declared layout callback]
  exact ⟨failure, rfl, kindEq, valuesEq, stateEq⟩

/-- The same callback trace is retained by the actual bounded-list dictionary. -/
theorem list_decode_retains_trace {T State : Type} (limit : Usize)
    (child : NyxSszRust.codec.Ssz T State) (shape : Ssz.Desc) (observe : T → Ssz.Value)
    (law : CodecLaw child shape observe) (input : Slice U8)
    (view : NyxSszRust.sequence.SequenceView) (valid : sequenceViewValid view)
    (kind : NyxSszRust.error.CodecError) (completed : List T) (state : State)
    (declared : NyxSszRust.codec.validate_type child = RustM.ok (.Ok ()))
    (layout : NyxSszRust.collection_codec.list_layout child input (some limit) = RustM.ok (.Ok view))
    (trace : decodeRangesModel child view.input view.ranges.val [] =
      RustM.ok (.Err ⟨kind, (completed, some state)⟩)) :
    NyxSszRust.collections.List.Insts.Nyx_sszCodecSszSequenceDecodeState.decode limit child input
      ⦃ actual => ∃ failure, actual = .Err failure ∧ failure.kind = kind ∧
        failure.state.values.val = completed ∧ failure.state.child = some state ⦄ := by
  obtain ⟨actual, callback, failure, same, kindEq, valuesEq, stateEq⟩ := spec_imp_exists
    (decode_elements_failure_state child shape observe law view valid kind completed state trace)
  subst actual
  rw [NyxSszRust.collections.List.Insts.Nyx_sszCodecSszSequenceDecodeState.decode,
    list_decode_callback_failure limit child input view failure declared layout callback]
  exact ⟨failure, rfl, kindEq, valuesEq, stateEq⟩

end NyxSszVerification
