import NyxSszVerification.Representation.Integers
import NyxSszVerification.Bytes

open Aeneas Aeneas.Std

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace NyxSszVerification

/-- A byte list denotes uint8 elements, not the reference's opaque-byte value. -/
def byteValues (bytes : List U8) : List Ssz.Value := bytes.map fun byte => .uint byte.val

def byteParts (bytes : List U8) : List Ssz.Bytes := bytes.map fun byte => #[byteToSpec byte]

theorem byteValues_injective : Function.Injective byteValues := by
  have element : Function.Injective (fun byte : U8 => Ssz.Value.uint byte.val) := by
    intro left right same
    exact UScalar.eq_of_val_eq (Ssz.Value.uint.inj same)
  intro left right same
  exact (List.map_inj_right element).mp same

@[simp] theorem byteValues_length (bytes : List U8) : (byteValues bytes).length = bytes.length := by
  simp [byteValues]

theorem serialize_byte (byte : U8) :
    Ssz.serialize (.uint 1) (.uint byte.val) = .ok #[byteToSpec byte] := by
  simpa [BitVec.toLEBytes, byteToSpec] using serialize_uint_bits 1 byte.bv

theorem serialize_byteValues (bytes : List U8) :
    Ssz.serializeEach (.uint 1) (byteValues bytes) = .ok (byteParts bytes) := by
  induction bytes with
  | nil => simp [byteValues, byteParts, Ssz.serializeEach]
  | cons head tail ih =>
    simp_all [byteValues, byteParts, Ssz.serializeEach, serialize_byte,
      Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem inline_slots (parts : List Ssz.Bytes) :
    (parts.map (fun _ => true)).zip parts = parts.map (fun part => (true, part)) := by
  induction parts <;> simp_all

theorem byte_layout (bytes : List U8) :
    let slots := (byteParts bytes).map (fun part => (true, part))
    Ssz.headWidth slots = bytes.length ∧ Ssz.bodyWidth slots = 0 ∧
      (∀ start, Ssz.headOf start slots = bytesToSpec bytes) ∧ Ssz.bodiesOf slots = #[] := by
  induction bytes with
  | nil => simp [byteParts, bytesToSpec, Ssz.headWidth, Ssz.bodyWidth, Ssz.headOf, Ssz.bodiesOf]
  | cons head tail ih =>
    simp_all [byteParts, bytesToSpec, Ssz.headWidth, Ssz.bodyWidth, Ssz.headOf,
      Ssz.bodiesOf, Nat.add_comm]

theorem assemble_byteParts (bytes : List U8) :
    Ssz.assemble ((byteParts bytes).map (fun _ => true)) (byteParts bytes) =
      if bytes.length ≥ 2 ^ 32 then .error (.offsetOverflow bytes.length)
      else .ok (bytesToSpec bytes) := by
  rcases byte_layout bytes with ⟨leading, bodies, front, back⟩
  unfold Ssz.assemble
  rw [inline_slots]
  simp [leading, bodies, front, back, Ssz.bytesPerOffset,
    Bind.bind, Except.bind, Pure.pure, Except.pure, MonadExcept.throw, throwThe,
    MonadExceptOf.throw]

theorem serialize_byteSequence (bytes : List U8) :
    Ssz.serializeSequence (.uint 1) (byteValues bytes) =
      if bytes.length ≥ 2 ^ 32 then .error (.offsetOverflow bytes.length)
      else .ok (bytesToSpec bytes) := by
  simpa only [Ssz.serializeSequence, serialize_byteValues, Ssz.Desc.isFixed,
    Ssz.Desc.fixedSize, Option.isSome_some, Bind.bind, Except.bind] using assemble_byteParts bytes

end NyxSszVerification
