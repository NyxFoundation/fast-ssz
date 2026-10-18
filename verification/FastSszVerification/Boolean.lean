import FastSszRust
import Ssz.Codec.Deserialize

open Aeneas Aeneas.Std

namespace FastSszVerification

/-- The same eight bits in the implementation and reference representations. -/
def byteToSpec (byte : U8) : UInt8 := ⟨byte.bv⟩

/-- Representation relation; it preserves order, length, and every bit. -/
def bytesToSpec (bytes : List U8) : Ssz.Bytes :=
  (bytes.map byteToSpec).toArray

/-- The public error categories are a quotient of the reference errors. -/
def booleanResult (result : Except Ssz.Err Ssz.Value) :
    core.result.Result Bool FastSszRust.scalar.ScalarError :=
  match result with
  | .ok (.bool value) => .Ok value
  | .error (.scope _ _) => .Err .InvalidLength
  | _ => .Err .InvalidBoolean

theorem byteToSpec_injective : Function.Injective byteToSpec := by
  intro ⟨left⟩ ⟨right⟩ equal
  cases equal
  rfl

/-- Rust encoding terminates successfully and returns exactly the reference bytes. -/
theorem encode_bool_refines (value : Bool) :
    ∃ encoded, FastSszRust.scalar.encode_bool value = RustM.ok encoded ∧
      Ssz.serialize .bool (.bool value) = .ok (bytesToSpec encoded.val) := by
  cases value <;> simp [FastSszRust.scalar.encode_bool, Ssz.serialize,
    bytesToSpec, byteToSpec, Array.make]

/-- Rust decoding terminates without a panic and agrees on all byte slices. -/
theorem decode_bool_refines (bytes : Slice U8) :
    FastSszRust.scalar.decode_bool bytes =
      RustM.ok (booleanResult (Ssz.deserialize .bool (bytesToSpec bytes.val))) := by
  rcases bytes with ⟨bytes, bound⟩
  cases bytes with
  | nil =>
    simp [FastSszRust.scalar.decode_bool, booleanResult, Ssz.deserialize,
      bytesToSpec, Slice.len]
    rfl
  | cons byte rest =>
    cases rest with
    | nil =>
      by_cases zero : byte = 0#u8
      · subst byte
        simp [FastSszRust.scalar.decode_bool, booleanResult, Ssz.deserialize,
          bytesToSpec, Slice.len, Slice.index_usize, byteToSpec]
        rfl
      by_cases one : byte = 1#u8
      · subst byte
        simp [FastSszRust.scalar.decode_bool, booleanResult, Ssz.deserialize,
          bytesToSpec, Slice.len, Slice.index_usize, byteToSpec]
        rfl
      have notZero : byteToSpec byte ≠ 0 := fun equal =>
        zero (byteToSpec_injective equal)
      have notOne : byteToSpec byte ≠ 1 := fun equal =>
        one (byteToSpec_injective equal)
      simp [FastSszRust.scalar.decode_bool, booleanResult, Ssz.deserialize,
        bytesToSpec, Slice.len, Slice.index_usize]
      split <;> simp_all [UScalar.eq_equiv_bv_eq]
      rfl
    | cons next rest =>
      simp [FastSszRust.scalar.decode_bool, booleanResult, Ssz.deserialize,
        bytesToSpec, Slice.len]
      rfl

end FastSszVerification
