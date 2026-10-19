import NyxSszVerification.Codec.Elements.Model

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace NyxSszVerification

def checkedDeserializeEach (shape : Ssz.Desc) : List Ssz.Bytes → Except Ssz.Err (List Ssz.Value)
  | [] => .ok []
  | bytes :: rest => do
    let value ← checkedDeserialize shape bytes
    let values ← checkedDeserializeEach shape rest
    return value :: values

def rangeBodies (input : Slice U8) (ranges : List NyxSszRust.sequence.BodyRange) : List Ssz.Bytes :=
  ranges.map fun range => bytesToSpec (input.val.slice range.start.val range.end.val)

@[simp] theorem rangeBodies_cons (input : Slice U8) (range : NyxSszRust.sequence.BodyRange)
    (rest : List NyxSszRust.sequence.BodyRange) :
    rangeBodies input (range :: rest) =
      bytesToSpec (input.val.slice range.start.val range.end.val) :: rangeBodies input rest := rfl

def sequenceListsAgrees {T State : Type} (observe : T → Ssz.Value)
    (actual : core.result.Result (List T) (NyxSszRust.error.DecodeFailure (List T × Option State)))
    (expected : Except Ssz.Err (List Ssz.Value)) : Prop :=
  match actual, expected with
  | .Ok values, .ok expectedValues => values.map observe = expectedValues
  | .Err failure, .error fault => codecFaultAgrees failure.kind fault
  | _, _ => False

theorem checked_each_reference (shape : Ssz.Desc) (valid : shape.wellFormed = .ok ())
    (parts : List Ssz.Bytes) : checkedDeserializeEach shape parts = Ssz.deserializeEach shape parts := by
  induction parts with
  | nil => simp [checkedDeserializeEach, Ssz.deserializeEach]
  | cons bytes rest ih =>
    simp [checkedDeserializeEach, checkedDeserialize, valid, Ssz.deserializeEach, ih,
      Bind.bind, Except.bind]

theorem decode_ranges_model_wire {T State : Type} (codecInst : NyxSszRust.codec.Ssz T State)
    (shape : Ssz.Desc) (observe : T → Ssz.Value) (law : CodecLaw codecInst shape observe)
    (input : Slice U8) (ranges : List NyxSszRust.sequence.BodyRange) (valid : rangesValid input ranges)
    (completed : List T) :
    decodeRangesModel codecInst input ranges completed ⦃ actual =>
      sequenceListsAgrees observe actual
        ((checkedDeserializeEach shape (rangeBodies input ranges)).map (completed.map observe ++ ·)) ⦄ := by
  induction ranges generalizing completed with
  | nil => simp [decodeRangesModel, rangeBodies, checkedDeserializeEach, sequenceListsAgrees, Except.map]
  | cons range rest ih =>
    have safety := valid range (by simp)
    have tailValid : rangesValid input rest := fun part member => valid part (by simp [member])
    rw [decodeRangesModel]
    apply spec_bind (decode_range_refines codecInst shape observe law input range.start range.end
      safety.1 safety.2)
    intro actual actualPost
    cases actual with
    | Ok value =>
      have success : checkedDeserialize shape
          (bytesToSpec (input.val.slice range.start.val range.end.val)) = .ok (observe value) := by
        cases expected : checkedDeserialize shape
            (bytesToSpec (input.val.slice range.start.val range.end.val)) <;>
          simp_all [codecDecodingAgrees]
      apply spec_mono (ih tailValid (completed ++ [value]))
      intro actual agrees
      have expectedEq :
          ((checkedDeserializeEach shape (rangeBodies input (range :: rest))).map (completed.map observe ++ ·)) =
          ((checkedDeserializeEach shape (rangeBodies input rest)).map ((completed ++ [value]).map observe ++ ·)) := by
        simp only [rangeBodies_cons, checkedDeserializeEach, success, Bind.bind, Except.bind]
        cases checkedDeserializeEach shape (rangeBodies input rest) <;>
          simp [Except.map, Pure.pure, Except.pure, List.map_append, List.append_assoc]
      rw [expectedEq]
      exact agrees
    | Err failure =>
      obtain ⟨fault, failed, agrees⟩ : ∃ fault,
          checkedDeserialize shape (bytesToSpec (input.val.slice range.start.val range.end.val)) = .error fault ∧
          codecFaultAgrees failure.kind fault := by
        cases expected : checkedDeserialize shape
            (bytesToSpec (input.val.slice range.start.val range.end.val)) <;>
          simp_all [codecDecodingAgrees]
      simpa [checkedDeserializeEach, failed, sequenceListsAgrees,
        Bind.bind, Except.bind, Except.map] using agrees

end NyxSszVerification
