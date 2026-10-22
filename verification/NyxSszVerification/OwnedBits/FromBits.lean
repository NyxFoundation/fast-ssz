import NyxSszVerification.OwnedBits.Constructors
import NyxSszVerification.OwnedBits.Packing

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace NyxSszVerification

/-- This builtin adapter retains the stronger exact encoding relation. -/
def ownedMappedEncodingAgrees
    (actual : core.result.Result (alloc.vec.Vec U8) NyxSszRust.error.CodecError)
    (expected : Except Ssz.Err Ssz.Bytes) : Prop :=
  match actual, expected with
  | .Ok bytes, .ok data => bytesToSpec bytes.val = data
  | .Err error, .error fault => codecFaultAgrees error fault
  | _, _ => False

@[step] theorem owned_map_fault_refines
    (result : core.result.Result (alloc.vec.Vec U8) NyxSszRust.bitfield.BitfieldError)
    (expected : Except Ssz.Err Ssz.Bytes) (agrees : bitEncodingAgrees result expected) :
    core.result.Result.map_err NyxSszRust.P.Insts.CoreOpsFunctionFnOnceTupleBitfieldErrorCodecError
      result NyxSszRust.bit_storage.fault ⦃ actual => ownedMappedEncodingAgrees actual expected ⦄ := by
  cases result <;> cases expected <;> simp_all [bitEncodingAgrees]
  all_goals try simp_all [ownedMappedEncodingAgrees]
  all_goals simp only [NyxSszRust.P.Insts.CoreOpsFunctionFnOnceTupleBitfieldErrorCodecError.call_once]
  all_goals step*

@[step] theorem owned_bit_vector_from_bits_refines (N : Usize) (bits : Slice Bool) :
    NyxSszRust.bitcollections.BitVector.from_bits N bits ⦃ actual =>
      match actual with
      | .Ok value => canonicalOwnedVector value.encoded.val N.val ∧
          observeOwnedVector value = .bits (bitsToSpec bits.val) ∧
          checkedSerialize (.bitVector N.val) (.bits (bitsToSpec bits.val)) = .ok (bytesToSpec value.encoded.val)
      | .Err error => ∃ fault,
          checkedSerialize (.bitVector N.val) (.bits (bitsToSpec bits.val)) = .error fault ∧
          codecFaultAgrees error fault ⦄ := by
  unfold NyxSszRust.bitcollections.BitVector.from_bits
  step*
  · cases r1 <;> simp_all
    cases encoded : checkedSerialize (.bitVector N.val) (.bits (bitsToSpec bits.val)) <;>
      simp_all [ownedMappedEncodingAgrees]
    have recovered := owned_vector_roundtrip N.val (bitsToSpec bits.val) _ encoded
    cases actual with
    | Ok value =>
      rcases actual_post with ⟨same, canonical⟩
      have observation := canonical.2.2
      simp_all [observeOwnedVector]
    | Err error =>
      rcases actual_post with ⟨fault, failed, _⟩
      simp_all
  · cases r1 <;> cases encoded : checkedSerialize (.bitVector N.val) (.bits (bitsToSpec bits.val)) <;>
      simp_all [ownedMappedEncodingAgrees]

theorem owned_list_serialize_alias (cap : Nat) (bits : _root_.Array Bool) :
    checkedSerialize (.bitList cap) (.bits bits) = checkedSerialize (.progressiveBitList (some cap)) (.bits bits) := by
  simp [checkedSerialize, Ssz.Desc.wellFormed, Ssz.serialize, Ssz.boundCheck,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  split <;> simp_all

theorem owned_list_deserialize_alias (cap : Nat) (bytes : Ssz.Bytes) :
    checkedDeserialize (.bitList cap) bytes = checkedDeserialize (.progressiveBitList (some cap)) bytes := by
  simp [checkedDeserialize, Ssz.Desc.wellFormed, Ssz.deserialize, Bind.bind, Except.bind]

@[step] theorem owned_bit_list_from_bits_refines (MAX : Usize) (bits : Slice Bool) :
    NyxSszRust.bitcollections.BitList.from_bits MAX bits ⦃ actual =>
      match actual with
      | .Ok value => canonicalOwnedList value.encoded.val (some MAX.val) ∧
          observeOwnedList value = .bits (bitsToSpec bits.val) ∧
          checkedSerialize (.bitList MAX.val) (.bits (bitsToSpec bits.val)) = .ok (bytesToSpec value.encoded.val)
      | .Err error => ∃ fault,
          checkedSerialize (.bitList MAX.val) (.bits (bitsToSpec bits.val)) = .error fault ∧
          codecFaultAgrees error fault ⦄ := by
  unfold NyxSszRust.bitcollections.BitList.from_bits
  step*
  · cases r1 <;> simp_all
    cases encoded : checkedSerialize (.bitList MAX.val) (.bits (bitsToSpec bits.val)) <;>
      simp_all [ownedMappedEncodingAgrees]
    have recovered := owned_list_roundtrip (some MAX.val) (bitsToSpec bits.val) _
      (by simpa only [← owned_list_serialize_alias] using encoded)
    cases actual with
    | Ok value =>
      rcases actual_post with ⟨same, canonical⟩
      have observation := canonical.2
      simp_all [observeOwnedList]
    | Err error =>
      rcases actual_post with ⟨fault, failed, _⟩
      simp_all [owned_list_deserialize_alias]
  · cases r1 <;> cases encoded : checkedSerialize (.bitList MAX.val) (.bits (bitsToSpec bits.val)) <;>
      simp_all [ownedMappedEncodingAgrees]

attribute [local step] encode_progressive_bit_list_refines

@[step] theorem owned_progressive_bit_list_from_bits_refines (bits : Slice Bool) :
    NyxSszRust.bitcollections.ProgressiveBitList.from_bits bits ⦃ actual =>
      match actual with
      | .Ok value => canonicalOwnedList value.encoded.val none ∧
          observeOwnedProgressive value = .bits (bitsToSpec bits.val) ∧
          checkedSerialize (.progressiveBitList none) (.bits (bitsToSpec bits.val)) = .ok (bytesToSpec value.encoded.val)
      | .Err error => ∃ fault,
          checkedSerialize (.progressiveBitList none) (.bits (bitsToSpec bits.val)) = .error fault ∧
          codecFaultAgrees error fault ⦄ := by
  unfold NyxSszRust.bitcollections.ProgressiveBitList.from_bits
  step*
  · cases r1 <;> simp_all
    cases encoded : checkedSerialize (.progressiveBitList none) (.bits (bitsToSpec bits.val)) <;>
      simp_all [ownedMappedEncodingAgrees]
    have recovered := owned_list_roundtrip none (bitsToSpec bits.val) _ encoded
    cases actual with
    | Ok value =>
      rcases actual_post with ⟨same, canonical⟩
      have observation := canonical.2
      simp_all [observeOwnedProgressive]
    | Err error =>
      rcases actual_post with ⟨fault, failed, _⟩
      simp_all
  · cases r1 <;> cases encoded : checkedSerialize (.progressiveBitList none) (.bits (bitsToSpec bits.val)) <;>
      simp_all [ownedMappedEncodingAgrees]

end NyxSszVerification
