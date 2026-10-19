import FastSszVerification.Sequence.Bytes

open Aeneas Aeneas.Std

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace FastSszVerification

theorem byte_extract_at (bytes : List U8) (index : Nat) (inside : index < bytes.length) :
    (bytesToSpec bytes).extract index (index + 1) = #[byteToSpec bytes[index]] := by
  apply _root_.Array.ext
  · simp
    omega
  intro position left right
  have zero : position = 0 := by simp at right; omega
  subst position
  simp [bytesToSpec]

theorem byte_slices (bytes : List U8) :
    (List.range bytes.length).map (fun index => (bytesToSpec bytes).extract index (index + 1)) =
      byteParts bytes := by
  apply List.ext_getElem (by simp [byteParts])
  intro index left right
  simp only [byteParts, List.getElem_map, List.getElem_range]
  exact byte_extract_at bytes index (by simpa using left)

theorem deserialize_byte (byte : U8) :
    Ssz.deserialize (.uint 1) #[byteToSpec byte] = .ok (.uint byte.val) := by
  simp [Ssz.deserialize, Ssz.readUint, byteToSpec,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem deserialize_byteParts (bytes : List U8) :
    Ssz.deserializeEach (.uint 1) (byteParts bytes) = .ok (byteValues bytes) := by
  induction bytes with
  | nil => simp [byteParts, byteValues, Ssz.deserializeEach]
  | cons head tail ih =>
    simp_all [byteParts, byteValues, Ssz.deserializeEach, deserialize_byte,
      Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem listSlices_bytes (bytes : List U8) (limit : Option Nat) :
    Ssz.listSlices (.uint 1) limit (bytesToSpec bytes) =
      if bytes.length ≥ 2 ^ 32 then .error (.offsetOverflow bytes.length)
      else (do
        Ssz.boundCheck limit bytes.length
        pure (byteParts bytes)) := by
  cases limit <;> by_cases over : bytes.length ≥ 2 ^ 32 <;> by_cases empty : bytes.length = 0
  all_goals simp_all [Ssz.listSlices, Ssz.boundCheck, Ssz.Desc.fixedSize, Ssz.bytesPerOffset,
    byte_slices, byteParts, Bind.bind, Except.bind, Pure.pure, Except.pure, MonadExcept.throw,
    throwThe, MonadExceptOf.throw]
  all_goals try split_ifs
  all_goals simp_all
  all_goals omega

end FastSszVerification
