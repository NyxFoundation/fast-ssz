import NyxSszVerification.Codec.Law
import NyxSszVerification.Sequence.View
import NyxSszVerification.Sequence.Reference

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace NyxSszVerification

def sequenceResultToLists {T State : Type}
    (actual : core.result.Result (alloc.vec.Vec T)
      (NyxSszRust.error.DecodeFailure (NyxSszRust.codec.SequenceDecodeState T State))) :
    core.result.Result (List T) (NyxSszRust.error.DecodeFailure (List T × Option State)) :=
  match actual with
  | .Ok values => .Ok values.val
  | .Err failure => .Err ⟨failure.kind, (failure.state.values.val, failure.state.child)⟩

/-- The exact callback trace; prefixes and nested state are never projected away. -/
def decodeRangesModel {T State : Type} (codecInst : NyxSszRust.codec.Ssz T State)
    (input : Slice U8) : List NyxSszRust.sequence.BodyRange → List T →
      RustM (core.result.Result (List T) (NyxSszRust.error.DecodeFailure (List T × Option State)))
  | [], values => RustM.ok (.Ok values)
  | range :: rest, values => do
    let actual ← NyxSszRust.codec.decode_range codecInst input range.start range.end
    match actual with
    | .Ok value => decodeRangesModel codecInst input rest (values ++ [value])
    | .Err failure => RustM.ok (.Err ⟨failure.kind, (values, some failure.state)⟩)

def rangesValid (input : Slice U8) (ranges : List NyxSszRust.sequence.BodyRange) : Prop :=
  ∀ range ∈ ranges, range.start.val ≤ range.end.val ∧ range.end.val ≤ input.val.length

@[step] theorem decode_range_refines {T State : Type} (codecInst : NyxSszRust.codec.Ssz T State)
    (shape : Ssz.Desc) (observe : T → Ssz.Value) (law : CodecLaw codecInst shape observe)
    (input : Slice U8) (start stop : Usize)
    (ordered : start.val ≤ stop.val) (bounded : stop.val ≤ input.val.length) :
    NyxSszRust.codec.decode_range codecInst input start stop ⦃ actual =>
      NyxSszRust.codec.decode_range codecInst input start stop = RustM.ok actual ∧
      codecDecodingAgrees observe actual
        (checkedDeserialize shape (bytesToSpec (input.val.slice start.val stop.val))) ⦄ := by
  have protocol : NyxSszRust.codec.decode_range codecInst input start stop ⦃ actual =>
      codecDecodingAgrees observe actual
        (checkedDeserialize shape (bytesToSpec (input.val.slice start.val stop.val))) ⦄ := by
    unfold NyxSszRust.codec.decode_range
    step
    apply spec_mono (law.decode s)
    intro actual agrees
    simpa only [s_post1] using agrees
  obtain ⟨actual, runs, correct⟩ := spec_imp_exists protocol
  exact exists_imp_spec ⟨actual, runs, runs, correct⟩

end NyxSszVerification
