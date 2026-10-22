import NyxSszRust.ProgressiveCodec
import NyxSszVerification.Collection.Ownership
import NyxSszVerification.BoundedProgressiveCollection.Storage

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace NyxSszVerification

/-- A rejected child declaration leaves the progressive list's owned state empty. -/
theorem bounded_progressive_list_decode_declaration_failure {T State : Type} (limit : Usize)
    (child : NyxSszRust.codec.Ssz T State) (input : Slice U8)
    (kind : NyxSszRust.error.CodecError)
    (rejected : NyxSszRust.codec.validate_type child = RustM.ok (.Err kind)) :
    NyxSszRust.progressive_codec.decode_bounded_progressive limit child input =
      RustM.ok (.Err ⟨kind, ⟨alloc.vec.Vec.new T, none⟩⟩) := by
  simp [NyxSszRust.progressive_codec.decode_bounded_progressive, rejected]

/-- Layout rejection consumes no elements and creates no nested state. -/
theorem bounded_progressive_list_decode_layout_failure {T State : Type} (limit : Usize)
    (child : NyxSszRust.codec.Ssz T State) (input : Slice U8)
    (kind : NyxSszRust.error.CodecError)
    (declared : NyxSszRust.codec.validate_type child = RustM.ok (.Ok ()))
    (rejected : NyxSszRust.collection_codec.list_layout child input (some limit) = RustM.ok (.Err kind)) :
    NyxSszRust.progressive_codec.decode_bounded_progressive limit child input =
      RustM.ok (.Err ⟨kind, ⟨alloc.vec.Vec.new T, none⟩⟩) := by
  simp [NyxSszRust.progressive_codec.decode_bounded_progressive, declared, rejected]

/-- The parent forwards the complete typed callback failure without changing either state. -/
theorem bounded_progressive_list_decode_callback_failure {T State : Type} (limit : Usize)
    (child : NyxSszRust.codec.Ssz T State) (input : Slice U8)
    (view : NyxSszRust.sequence.SequenceView)
    (failure : NyxSszRust.error.DecodeFailure (NyxSszRust.codec.SequenceDecodeState T State))
    (declared : NyxSszRust.codec.validate_type child = RustM.ok (.Ok ()))
    (layout : NyxSszRust.collection_codec.list_layout child input (some limit) = RustM.ok (.Ok view))
    (callback : NyxSszRust.codec.decode_elements child view = RustM.ok (.Err failure)) :
    NyxSszRust.progressive_codec.decode_bounded_progressive limit child input = RustM.ok (.Err failure) := by
  simp [NyxSszRust.progressive_codec.decode_bounded_progressive, declared, layout, callback,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]

/-- Success moves every decoded owner unchanged, without copying or dropping it. -/
theorem bounded_progressive_list_decode_callback_success {T State : Type} (limit : Usize)
    (child : NyxSszRust.codec.Ssz T State) (input : Slice U8)
    (view : NyxSszRust.sequence.SequenceView) (values : alloc.vec.Vec T)
    (within : values.val.length ≤ limit.val)
    (declared : NyxSszRust.codec.validate_type child = RustM.ok (.Ok ()))
    (layout : NyxSszRust.collection_codec.list_layout child input (some limit) = RustM.ok (.Ok view))
    (callback : NyxSszRust.codec.decode_elements child view = RustM.ok (.Ok values)) :
    NyxSszRust.progressive_codec.decode_bounded_progressive limit child input =
      RustM.ok (.Ok ⟨values, Array.repeat limit ()⟩) := by
  simp [NyxSszRust.progressive_codec.decode_bounded_progressive, declared, layout, callback,
    core.result.Result.Insts.CoreOpsTry.branch, NyxSszRust.collections.bounded_progressive_list,
    NyxSszRust.collections.BoundedProgressiveList.as_slice, Nat.not_lt.mpr within]

/-- The actual dictionary retains the exact owned prefix and arbitrary failing child's state. -/
theorem bounded_progressive_list_decode_retains_trace {T State : Type} (limit : Usize)
    (child : NyxSszRust.codec.Ssz T State) (shape : Ssz.Desc) (observe : T → Ssz.Value)
    (law : CodecLaw child shape observe) (input : Slice U8)
    (view : NyxSszRust.sequence.SequenceView) (valid : sequenceViewValid view)
    (kind : NyxSszRust.error.CodecError) (completed : List T) (state : State)
    (declared : NyxSszRust.codec.validate_type child = RustM.ok (.Ok ()))
    (layout : NyxSszRust.collection_codec.list_layout child input (some limit) = RustM.ok (.Ok view))
    (trace : decodeRangesModel child view.input view.ranges.val [] =
      RustM.ok (.Err ⟨kind, (completed, some state)⟩)) :
    NyxSszRust.collections.BoundedProgressiveList.Insts.Nyx_sszCodecSszSequenceDecodeState.decode limit child input
      ⦃ actual => ∃ failure, actual = .Err failure ∧ failure.kind = kind ∧
        failure.state.values.val = completed ∧ failure.state.child = some state ⦄ := by
  obtain ⟨actual, callback, failure, same, kindEq, valuesEq, stateEq⟩ := spec_imp_exists
    (decode_elements_failure_state child shape observe law view valid kind completed state trace)
  subst actual
  rw [NyxSszRust.collections.BoundedProgressiveList.Insts.Nyx_sszCodecSszSequenceDecodeState.decode,
    bounded_progressive_list_decode_callback_failure limit child input view failure declared layout callback]
  exact ⟨failure, rfl, kindEq, valuesEq, stateEq⟩

end NyxSszVerification
