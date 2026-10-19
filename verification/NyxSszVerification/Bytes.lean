import NyxSszVerification.Representation
import Ssz.Codec.Deserialize
import NyxSszRust.Bytes
import Ssz.Type.Valid

open Aeneas Aeneas.Std
namespace NyxSszVerification

/-- Validate declarations before invoking the upstream low-level codecs. -/
def checkedSerialize (shape : Ssz.Desc) (value : Ssz.Value) : Except Ssz.Err Ssz.Bytes := do
  shape.wellFormed
  Ssz.serialize shape value

def checkedDeserialize (shape : Ssz.Desc) (data : Ssz.Bytes) : Except Ssz.Err Ssz.Value := do
  shape.wellFormed
  Ssz.deserialize shape data

/-- Unmapped reference faults cannot silently satisfy correspondence. -/
def byteFaultAgrees (actual : NyxSszRust.bytes.ByteError) (expected : Ssz.Err) : Prop :=
  match actual, expected with
  | .EmptyVector, .vectorEmpty => True
  | .InvalidLength, .scope _ _ => True
  | .OverLimit, .overLimit _ _ => True
  | .OffsetOverflow, .offsetOverflow _ => True
  | _, _ => False

def byteEncodingAgrees (actual : core.result.Result (Slice U8) NyxSszRust.bytes.ByteError)
    (expected : Except Ssz.Err Ssz.Bytes) : Prop :=
  match actual, expected with
  | .Ok output, .ok data => bytesToSpec output.val = data
  | .Err error, .error fault => byteFaultAgrees error fault
  | _, _ => False

def byteDecodingAgrees (actual : core.result.Result (Slice U8) NyxSszRust.bytes.ByteError)
    (expected : Except Ssz.Err Ssz.Value) : Prop :=
  match actual, expected with
  | .Ok output, .ok (.bytes data) => bytesToSpec output.val = data
  | .Err error, .error fault => byteFaultAgrees error fault
  | _, _ => False

/-- All vector inputs, including illegal declarations and malformed lengths. -/
theorem byte_vector_refines (input : Slice U8) (length : Usize) :
    ∃ result,
      NyxSszRust.bytes.encode_byte_vector input length = RustM.ok result ∧
      NyxSszRust.bytes.decode_byte_vector input length = RustM.ok result ∧
      byteEncodingAgrees result
        (checkedSerialize (.byteVector length.val) (.bytes (bytesToSpec input.val))) ∧
      byteDecodingAgrees result
        (checkedDeserialize (.byteVector length.val) (bytesToSpec input.val)) := by
  have zeroEq : (length = 0#usize) ↔ length.val = 0 := by scalar_tac
  have sizeEq : (Slice.len input = length) ↔ input.val.length = length.val := by scalar_tac
  refine ⟨if length = 0#usize then .Err .EmptyVector
    else if Slice.len input = length then .Ok input else .Err .InvalidLength, ?_, ?_, ?_, ?_⟩
  all_goals
    by_cases zero : length = 0#usize <;> by_cases same : Slice.len input = length <;>
      simp_all [NyxSszRust.bytes.encode_byte_vector, NyxSszRust.bytes.decode_byte_vector,
        checkedSerialize, checkedDeserialize, Ssz.Desc.wellFormed, Ssz.serialize,
        Ssz.deserialize, bytesToSpec, byteEncodingAgrees, byteDecodingAgrees,
        byteFaultAgrees] <;> trivial

/-- All list bounds, including zero and the machine maximum. -/
theorem byte_list_refines (input : Slice U8) (limit : Usize) :
    ∃ result,
      NyxSszRust.bytes.encode_byte_list input limit = RustM.ok result ∧
      NyxSszRust.bytes.decode_byte_list input limit = RustM.ok result ∧
      byteEncodingAgrees result
        (checkedSerialize (.byteList limit.val) (.bytes (bytesToSpec input.val))) ∧
      byteDecodingAgrees result
        (checkedDeserialize (.byteList limit.val) (bytesToSpec input.val)) := by
  by_cases over : Slice.len input > limit
  · have overVal : input.val.length > limit.val := by scalar_tac
    refine ⟨.Err .OverLimit, ?_, ?_, ?_, ?_⟩ <;>
      simp [NyxSszRust.bytes.encode_byte_list, NyxSszRust.bytes.decode_byte_list,
        over, checkedSerialize, checkedDeserialize, Ssz.Desc.wellFormed,
        Ssz.serialize, Ssz.deserialize, bytesToSpec, overVal, Nat.not_le_of_gt overVal,
        byteEncodingAgrees, byteDecodingAgrees, byteFaultAgrees] <;> trivial
  · have within : input.val.length ≤ limit.val := by scalar_tac
    refine ⟨.Ok input, ?_, ?_, ?_, ?_⟩ <;>
      simp [NyxSszRust.bytes.encode_byte_list, NyxSszRust.bytes.decode_byte_list,
        over, checkedSerialize, checkedDeserialize, Ssz.Desc.wellFormed,
        Ssz.serialize, Ssz.deserialize, bytesToSpec, within, Nat.not_lt_of_ge within,
        byteEncodingAgrees, byteDecodingAgrees]
    trivial

end NyxSszVerification
