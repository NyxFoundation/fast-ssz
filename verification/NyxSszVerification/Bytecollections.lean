import NyxSszRust.Bytecollections
import NyxSszVerification.Collections
import NyxSszVerification.Collection.Append
import NyxSszVerification.PackedRoots.Bytes

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace NyxSszVerification

/-- Opaque byte observations preserve the entire ordered byte array. -/
def ownedByteVectorValue {count : Usize} (value : NyxSszRust.bytecollections.ByteVector count) :
    Ssz.Value := .bytes (bytesToSpec value.bytes.val)

def ownedByteListValue {capacity : Usize} (value : NyxSszRust.bytecollections.ByteList capacity) :
    Ssz.Value := .bytes (bytesToSpec value.bytes.val)

/-- Every accepted constructor result contains the original vector, not a copy. -/
theorem byte_vector_from_bytes_refines (count : Usize) (input : alloc.vec.Vec U8) :
    ∃ result, NyxSszRust.bytecollections.ByteVector.from_bytes count input = RustM.ok result ∧
      match result with
      | .Ok value => value.bytes = input ∧ count.val > 0 ∧ input.val.length = count.val
      | .Err error => (error = .EmptyVector ∧ count.val = 0) ∨
          (error = .InvalidLength ∧ count.val > 0 ∧ input.val.length ≠ count.val) := by
  have zeroEq : (count = 0#usize) ↔ count.val = 0 := by scalar_tac
  have sizeEq : (Slice.len (alloc.vec.Vec.deref input) = count) ↔
      input.val.length = count.val := by scalar_tac
  refine ⟨if count = 0#usize then .Err .EmptyVector
    else if Slice.len (alloc.vec.Vec.deref input) = count then .Ok ⟨input, Array.repeat count ()⟩
    else .Err .InvalidLength, ?_, ?_⟩
  all_goals
    by_cases zero : count = 0#usize <;>
      by_cases same : Slice.len (alloc.vec.Vec.deref input) = count <;>
      simp_all [NyxSszRust.bytecollections.ByteVector.from_bytes,
        NyxSszRust.bytes.encode_byte_vector, NyxSszRust.bytecollections.byte_error, bne_iff_ne] <;> omega

/-- All machine bounds, including zero and usize::MAX, preserve accepted storage. -/
theorem byte_list_from_bytes_refines (capacity : Usize) (input : alloc.vec.Vec U8) :
    ∃ result, NyxSszRust.bytecollections.ByteList.from_bytes capacity input = RustM.ok result ∧
      match result with
      | .Ok value => value.bytes = input ∧ input.val.length ≤ capacity.val
      | .Err error => error = .OverLimit ∧ input.val.length > capacity.val := by
  by_cases over : Slice.len (alloc.vec.Vec.deref input) > capacity
  · have overVal : input.val.length > capacity.val := by scalar_tac
    refine ⟨.Err .OverLimit, ?_, ?_⟩ <;>
      simp [NyxSszRust.bytecollections.ByteList.from_bytes, NyxSszRust.bytes.encode_byte_list,
        NyxSszRust.bytecollections.byte_error, overVal]
  · have within : input.val.length ≤ capacity.val := by scalar_tac
    refine ⟨.Ok ⟨input, Array.repeat capacity ()⟩, ?_, ?_⟩ <;>
      simp [NyxSszRust.bytecollections.ByteList.from_bytes, NyxSszRust.bytes.encode_byte_list,
        NyxSszRust.bytecollections.byte_error, within, Nat.not_lt_of_ge within]

theorem byte_vector_as_bytes_refines {count : Usize}
    (value : NyxSszRust.bytecollections.ByteVector count) :
    ∃ result, NyxSszRust.bytecollections.ByteVector.as_bytes value = RustM.ok result ∧
      result.val = value.bytes.val := by
  exact ⟨alloc.vec.Vec.deref value.bytes, rfl, rfl⟩

theorem byte_list_as_bytes_refines {capacity : Usize}
    (value : NyxSszRust.bytecollections.ByteList capacity) :
    ∃ result, NyxSszRust.bytecollections.ByteList.as_bytes value = RustM.ok result ∧
      result.val = value.bytes.val := by
  exact ⟨alloc.vec.Vec.deref value.bytes, rfl, rfl⟩

@[step] theorem byte_copy_bytes_refines (input : Slice U8) :
    NyxSszRust.bytecollections.copy_bytes input ⦃ output => output.val = input.val ⦄ := by
  unfold NyxSszRust.bytecollections.copy_bytes
  apply spec_mono (collection_append_refines (alloc.vec.Vec.new U8) input (by simp; scalar_tac))
  intro output same
  simpa using same

/-- The error conversion preserves the same fault classes, including offset overflow. -/
def ownedByteError : NyxSszRust.bytes.ByteError → NyxSszRust.error.CodecError
  | .EmptyVector => .EmptyVector
  | .InvalidLength => .InvalidLength
  | .OverLimit => .OverLimit
  | .OffsetOverflow => .SizeOverflow

@[simp] theorem owned_byte_error_exact (error : NyxSszRust.bytes.ByteError) :
    NyxSszRust.bytecollections.byte_error error = RustM.ok (ownedByteError error) := by
  cases error <;> rfl

@[simp] theorem owned_byte_fault_agrees (error : NyxSszRust.bytes.ByteError) (fault : Ssz.Err) :
    codecFaultAgrees (ownedByteError error) fault = byteFaultAgrees error fault := by
  cases error <;> cases fault <;> rfl

/-- Copying accepted borrowed bytes preserves exact serialization; errors preserve their class. -/
theorem owned_byte_encoding_agrees
    (actual : core.result.Result (Slice U8) NyxSszRust.bytes.ByteError)
    (expected : Except Ssz.Err Ssz.Bytes) (agrees : byteEncodingAgrees actual expected) :
    (do
      match actual with
      | .Ok bytes => do
        let output ← NyxSszRust.bytecollections.copy_bytes bytes
        RustM.ok (core.result.Result.Ok output)
      | .Err error => do
        let fault ← NyxSszRust.bytecollections.byte_error error
        RustM.ok (core.result.Result.Err fault)) ⦃ output =>
        codecEncodingAgrees output expected ⦄ := by
  cases actual with
  | Ok bytes =>
    apply spec_bind (byte_copy_bytes_refines bytes)
    intro output same
    cases expected <;> simp_all [byteEncodingAgrees, codecEncodingAgrees]
  | Err error =>
    cases expected <;> simp_all [byteEncodingAgrees, codecEncodingAgrees]

/-- Decoding preserves opaque bytes and returns exactly unit state on every fault. -/
theorem owned_byte_vector_decoding_agrees (count : Usize)
    (actual : core.result.Result (Slice U8) NyxSszRust.bytes.ByteError)
    (expected : Except Ssz.Err Ssz.Value) (agrees : byteDecodingAgrees actual expected) :
    (do
      match actual with
      | .Ok bytes =>
        let output ← NyxSszRust.bytecollections.copy_bytes bytes
        RustM.ok (core.result.Result.Ok (⟨output, Array.repeat count ()⟩ : NyxSszRust.bytecollections.ByteVector count))
      | .Err error => do
        let fault ← NyxSszRust.bytecollections.byte_error error
        RustM.ok (core.result.Result.Err (⟨fault, ()⟩ : NyxSszRust.error.DecodeFailure Unit))) ⦃ output =>
        codecDecodingAgrees ownedByteVectorValue output expected ⦄ := by
  cases actual with
  | Ok bytes =>
    apply spec_bind (byte_copy_bytes_refines bytes)
    intro output same
    cases expected with
    | error fault => simp [byteDecodingAgrees] at agrees
    | ok value => cases value <;>
        simp_all [byteDecodingAgrees, codecDecodingAgrees, ownedByteVectorValue]
  | Err error =>
    cases expected <;> simp_all [byteDecodingAgrees, codecDecodingAgrees]

theorem owned_byte_list_decoding_agrees (capacity : Usize)
    (actual : core.result.Result (Slice U8) NyxSszRust.bytes.ByteError)
    (expected : Except Ssz.Err Ssz.Value) (agrees : byteDecodingAgrees actual expected) :
    (do
      match actual with
      | .Ok bytes =>
        let output ← NyxSszRust.bytecollections.copy_bytes bytes
        RustM.ok (core.result.Result.Ok (⟨output, Array.repeat capacity ()⟩ : NyxSszRust.bytecollections.ByteList capacity))
      | .Err error => do
        let fault ← NyxSszRust.bytecollections.byte_error error
        RustM.ok (core.result.Result.Err (⟨fault, ()⟩ : NyxSszRust.error.DecodeFailure Unit))) ⦃ output =>
        codecDecodingAgrees ownedByteListValue output expected ⦄ := by
  cases actual with
  | Ok bytes =>
    apply spec_bind (byte_copy_bytes_refines bytes)
    intro output same
    cases expected with
    | error fault => simp [byteDecodingAgrees] at agrees
    | ok value => cases value <;>
        simp_all [byteDecodingAgrees, codecDecodingAgrees, ownedByteListValue]
  | Err error =>
    cases expected <;> simp_all [byteDecodingAgrees, codecDecodingAgrees]

/-- The actual generic dictionary refines the unchanged opaque-byte CodecLaw. -/
theorem byte_vector_codec_refines (count : Usize) :
    CodecLaw (NyxSszRust.bytecollections.ByteVector.Insts.Nyx_sszCodecSszTuple count)
      (.byteVector count.val) ownedByteVectorValue := by
  constructor
  · simp [NyxSszRust.bytecollections.ByteVector.Insts.Nyx_sszCodecSszTuple.TYPE, typeDescriptorToSpec]
  · intro value
    obtain ⟨actual, encoded, _, agrees, _⟩ := byte_vector_refines (alloc.vec.Vec.deref value.bytes) count
    have lifted := owned_byte_encoding_agrees actual _ agrees
    cases actual <;>
      simpa [NyxSszRust.bytecollections.ByteVector.Insts.Nyx_sszCodecSszTuple,
        NyxSszRust.bytecollections.ByteVector.Insts.Nyx_sszCodecSszTuple.encode,
        NyxSszRust.bytecollections.ByteVector.as_bytes, encoded, ownedByteVectorValue] using lifted
  · intro bytes
    obtain ⟨actual, _, decoded, _, agrees⟩ := byte_vector_refines bytes count
    have lifted := owned_byte_vector_decoding_agrees count actual _ agrees
    cases actual <;>
      simpa [NyxSszRust.bytecollections.ByteVector.Insts.Nyx_sszCodecSszTuple,
        NyxSszRust.bytecollections.ByteVector.Insts.Nyx_sszCodecSszTuple.decode, decoded] using lifted
  · intro value
    simpa [NyxSszRust.bytecollections.ByteVector.Insts.Nyx_sszCodecSszTuple,
      NyxSszRust.bytecollections.ByteVector.Insts.Nyx_sszCodecSszTuple.hash_tree_root,
      NyxSszRust.bytecollections.ByteVector.as_bytes, ownedByteVectorValue] using
      hash_tree_root_byte_vector_refines (alloc.vec.Vec.deref value.bytes) count

theorem byte_list_codec_refines (capacity : Usize) :
    CodecLaw (NyxSszRust.bytecollections.ByteList.Insts.Nyx_sszCodecSszTuple capacity)
      (.byteList capacity.val) ownedByteListValue := by
  constructor
  · simp [NyxSszRust.bytecollections.ByteList.Insts.Nyx_sszCodecSszTuple.TYPE, typeDescriptorToSpec]
  · intro value
    obtain ⟨actual, encoded, _, agrees, _⟩ := byte_list_refines (alloc.vec.Vec.deref value.bytes) capacity
    have lifted := owned_byte_encoding_agrees actual _ agrees
    cases actual <;>
      simpa [NyxSszRust.bytecollections.ByteList.Insts.Nyx_sszCodecSszTuple,
        NyxSszRust.bytecollections.ByteList.Insts.Nyx_sszCodecSszTuple.encode,
        NyxSszRust.bytecollections.ByteList.as_bytes, encoded, ownedByteListValue] using lifted
  · intro bytes
    obtain ⟨actual, _, decoded, _, agrees⟩ := byte_list_refines bytes capacity
    have lifted := owned_byte_list_decoding_agrees capacity actual _ agrees
    cases actual <;>
      simpa [NyxSszRust.bytecollections.ByteList.Insts.Nyx_sszCodecSszTuple,
        NyxSszRust.bytecollections.ByteList.Insts.Nyx_sszCodecSszTuple.decode, decoded] using lifted
  · intro value
    simpa [NyxSszRust.bytecollections.ByteList.Insts.Nyx_sszCodecSszTuple,
      NyxSszRust.bytecollections.ByteList.Insts.Nyx_sszCodecSszTuple.hash_tree_root,
      NyxSszRust.bytecollections.ByteList.as_bytes, ownedByteListValue] using
      hash_tree_root_byte_list_refines (alloc.vec.Vec.deref value.bytes) capacity

/-- Every native-slice decode terminates, and faults carry exactly the unit state. -/
theorem byte_vector_decode_state_refines (count : Usize) (bytes : Slice U8) :
    NyxSszRust.bytecollections.ByteVector.Insts.Nyx_sszCodecSszTuple.decode count bytes ⦃ actual =>
      match actual with
      | .Ok _ => True
      | .Err failure => failure.state = () ⦄ := by
  apply spec_mono ((byte_vector_codec_refines count).decode bytes)
  intro actual _
  cases actual with
  | Ok value => trivial
  | Err failure => exact Subsingleton.elim _ _

theorem byte_list_decode_state_refines (capacity : Usize) (bytes : Slice U8) :
    NyxSszRust.bytecollections.ByteList.Insts.Nyx_sszCodecSszTuple.decode capacity bytes ⦃ actual =>
      match actual with
      | .Ok _ => True
      | .Err failure => failure.state = () ⦄ := by
  apply spec_mono ((byte_list_codec_refines capacity).decode bytes)
  intro actual _
  cases actual with
  | Ok value => trivial
  | Err failure => exact Subsingleton.elim _ _

end NyxSszVerification
