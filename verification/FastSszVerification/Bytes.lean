import FastSszVerification.Boolean
import Ssz.Type.Valid

open Aeneas Aeneas.Std

namespace FastSszVerification

/-- Include declaration validation, rather than accepting an illegal zero-length vector. -/
def checkedSerialize (shape : Ssz.Desc) (value : Ssz.Value) : Except Ssz.Err Ssz.Bytes := do
  shape.wellFormed
  Ssz.serialize shape value

/-- The same declaration validation is required before decoding. -/
def checkedDeserialize (shape : Ssz.Desc) (data : Ssz.Bytes) : Except Ssz.Err Ssz.Value := do
  shape.wellFormed
  Ssz.deserialize shape data

/-- Only the three reference faults which the byte-array codecs can produce correspond. -/
def byteFaultAgrees (actual : FastSszRust.bytes.ByteError) (expected : Ssz.Err) : Prop :=
  match actual, expected with
  | .EmptyVector, .vectorEmpty => True
  | .InvalidLength, .scope _ _ => True
  | .OverLimit, .overLimit _ _ => True
  | _, _ => False

/-- Success must carry the exact reference bytes; refusal must carry the corresponding fault. -/
def byteEncodingAgrees (actual : core.result.Result (Slice U8) FastSszRust.bytes.ByteError)
    (expected : Except Ssz.Err Ssz.Bytes) : Prop :=
  match actual, expected with
  | .Ok output, .ok data => bytesToSpec output.val = data
  | .Err error, .error fault => byteFaultAgrees error fault
  | _, _ => False

/-- Decoding must recover a byte value, not merely return any successful reference value. -/
def byteDecodingAgrees (actual : core.result.Result (Slice U8) FastSszRust.bytes.ByteError)
    (expected : Except Ssz.Err Ssz.Value) : Prop :=
  match actual, expected with
  | .Ok output, .ok (.bytes data) => bytesToSpec output.val = data
  | .Err error, .error fault => byteFaultAgrees error fault
  | _, _ => False

/-- Vector encoding and decoding terminate, including illegal declarations and malformed input. -/
theorem byte_vector_refines (input : Slice U8) (length : Usize) :
    ∃ result,
      FastSszRust.bytes.encode_byte_vector input length = RustM.ok result ∧
      FastSszRust.bytes.decode_byte_vector input length = RustM.ok result ∧
      byteEncodingAgrees result
        (checkedSerialize (.byteVector length.val) (.bytes (bytesToSpec input.val))) ∧
      byteDecodingAgrees result
        (checkedDeserialize (.byteVector length.val) (bytesToSpec input.val)) := by
  by_cases zero : length = 0#usize
  · refine ⟨.Err .EmptyVector, ?_, ?_, ?_, ?_⟩ <;>
      simp [FastSszRust.bytes.encode_byte_vector, FastSszRust.bytes.decode_byte_vector,
        zero, checkedSerialize, checkedDeserialize, Ssz.Desc.wellFormed,
        byteEncodingAgrees, byteDecodingAgrees, byteFaultAgrees] <;> trivial
  have nonzero : length.val ≠ 0 := by scalar_tac
  by_cases same : Slice.len input = length
  · have sameVal : input.val.length = length.val := by scalar_tac
    refine ⟨.Ok input, ?_, ?_, ?_, ?_⟩ <;>
      simp [FastSszRust.bytes.encode_byte_vector, FastSszRust.bytes.decode_byte_vector,
        zero, same, checkedSerialize, checkedDeserialize, Ssz.Desc.wellFormed,
        Ssz.serialize, Ssz.deserialize, bytesToSpec, nonzero, sameVal,
        byteEncodingAgrees, byteDecodingAgrees]
    trivial
  · have notSameVal : input.val.length ≠ length.val := by scalar_tac
    refine ⟨.Err .InvalidLength, ?_, ?_, ?_, ?_⟩ <;>
      simp [FastSszRust.bytes.encode_byte_vector, FastSszRust.bytes.decode_byte_vector,
        zero, same, checkedSerialize, checkedDeserialize, Ssz.Desc.wellFormed,
        Ssz.serialize, Ssz.deserialize, bytesToSpec, nonzero, notSameVal,
        byteEncodingAgrees, byteDecodingAgrees, byteFaultAgrees] <;> trivial

/-- All list limits, including zero and the machine maximum, agree with the reference. -/
theorem byte_list_refines (input : Slice U8) (limit : Usize) :
    ∃ result,
      FastSszRust.bytes.encode_byte_list input limit = RustM.ok result ∧
      FastSszRust.bytes.decode_byte_list input limit = RustM.ok result ∧
      byteEncodingAgrees result
        (checkedSerialize (.byteList limit.val) (.bytes (bytesToSpec input.val))) ∧
      byteDecodingAgrees result
        (checkedDeserialize (.byteList limit.val) (bytesToSpec input.val)) := by
  by_cases over : Slice.len input > limit
  · have overVal : input.val.length > limit.val := by scalar_tac
    refine ⟨.Err .OverLimit, ?_, ?_, ?_, ?_⟩ <;>
      simp [FastSszRust.bytes.encode_byte_list, FastSszRust.bytes.decode_byte_list,
        over, checkedSerialize, checkedDeserialize, Ssz.Desc.wellFormed,
        Ssz.serialize, Ssz.deserialize, bytesToSpec, overVal, Nat.not_le_of_gt overVal,
        byteEncodingAgrees, byteDecodingAgrees, byteFaultAgrees] <;> trivial
  · have within : input.val.length ≤ limit.val := by scalar_tac
    refine ⟨.Ok input, ?_, ?_, ?_, ?_⟩ <;>
      simp [FastSszRust.bytes.encode_byte_list, FastSszRust.bytes.decode_byte_list,
        over, checkedSerialize, checkedDeserialize, Ssz.Desc.wellFormed,
        Ssz.serialize, Ssz.deserialize, bytesToSpec, within, Nat.not_lt_of_ge within,
        byteEncodingAgrees, byteDecodingAgrees]
    trivial

end FastSszVerification
