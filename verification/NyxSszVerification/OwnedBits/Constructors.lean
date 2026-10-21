import NyxSszVerification.OwnedBits.Read

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace NyxSszVerification

def ownedValidationAgrees (actual : core.result.Result Unit NyxSszRust.error.CodecError)
    (expected : Except Ssz.Err Ssz.Value) (canonical : Prop) : Prop :=
  match actual with
  | .Ok () => canonical
  | .Err error => ∃ fault, expected = .error fault ∧ codecFaultAgrees error fault

@[step] theorem owned_fault_refines (error : NyxSszRust.bitfield.BitfieldError) :
    NyxSszRust.bit_storage.fault error ⦃ actual =>
      ∀ fault, bitFaultAgrees error fault → codecFaultAgrees actual fault ⦄ := by
  cases h : error <;> simp [NyxSszRust.bit_storage.fault]
  all_goals intro fault agrees; cases fault <;> simp_all [bitFaultAgrees, codecFaultAgrees]

@[step] theorem owned_validate_vector_refines (bytes : Slice U8) (n : Usize) :
    NyxSszRust.bit_storage.validate_vector bytes n ⦃ actual =>
      ownedValidationAgrees actual
        (checkedDeserialize (.bitVector n.val) (bytesToSpec bytes.val))
        (canonicalOwnedVector bytes.val n.val) ⦄ := by
  simp only [NyxSszRust.bit_storage.validate_vector, NyxSszRust.bitfield.validate_bit_vector,
    core.result.Result.map_err,
    NyxSszRust.P.Insts.CoreOpsFunctionFnOnceTupleBitfieldErrorCodecError.call_once,
    NyxSszRust.bit_storage.fault]
  split <;> step*
  all_goals try (split <;> step*)
  all_goals try (split <;> step*)
  all_goals try (split <;> step*)
  all_goals simp_all [ownedValidationAgrees, canonicalOwnedVector, checkedDeserialize,
    Ssz.Desc.wellFormed, Ssz.deserialize, codecFaultAgrees,
    Bind.bind, Except.bind, Pure.pure, Except.pure,
    MonadExcept.throw, throwThe, MonadExceptOf.throw,
    bytesToSpec_getElem, byte_shift_zero_nat]
  all_goals
    try
      have count : ownedVectorCount bytes.val n.val = n.val :=
        ownedVectorCount_of_length _ _ (by omega) (by omega)
      simp_all [ownedVectorBits, Nat.one_le_iff_ne_zero]
  all_goals omega

@[step] theorem owned_validate_list_refines (bytes : Slice U8) (limit : Option Usize) :
    NyxSszRust.bit_storage.validate_list bytes limit ⦃ actual =>
      ownedValidationAgrees actual
        (checkedDeserialize (.progressiveBitList (limit.map fun cap => cap.val)) (bytesToSpec bytes.val))
        (canonicalOwnedList bytes.val (limit.map fun cap => cap.val)) ⦄ := by
  unfold NyxSszRust.bit_storage.validate_list NyxSszRust.bitfield.decode_progressive_bit_list
  cases chosen : limit
  all_goals step*
  all_goals try (split <;> step*)
  all_goals try (split <;> step*)
  all_goals try (split <;> step*)
  all_goals have lookup := bytesToSpec_getElem_bang bytes.val (bytes.val.length - 1)
  all_goals simp_all [ownedValidationAgrees, canonicalOwnedList,
    checkedDeserialize, Ssz.Desc.wellFormed, Ssz.deserialize, Ssz.unpackDelimited,
    ownedListBits, delimitedLength, bitFaultAgrees, codecFaultAgrees,
    Bind.bind, Except.bind, Pure.pure, Except.pure,
    MonadExcept.throw, throwThe, MonadExceptOf.throw]
  all_goals
    try
      have inside : bytes.val.length - 1 < bytes.val.length := by omega
      simp_all
  all_goals try split_ifs
  all_goals try simp_all
  all_goals omega

/-- Success retains the entire accepted Vec and establishes the exact decoder invariant. -/
@[step] theorem owned_bit_vector_from_ssz_bytes_refines (N : Usize) (encoded : alloc.vec.Vec U8) :
    NyxSszRust.bitcollections.BitVector.from_ssz_bytes N encoded ⦃ actual =>
      match actual with
      | .Ok value => value.encoded = encoded ∧ canonicalOwnedVector value.encoded.val N.val
      | .Err error => ∃ fault,
          checkedDeserialize (.bitVector N.val) (bytesToSpec encoded.val) = .error fault ∧
          codecFaultAgrees error fault ⦄ := by
  unfold NyxSszRust.bitcollections.BitVector.from_ssz_bytes
  step*
  all_goals cases r <;> simp_all [ownedValidationAgrees]

@[step] theorem owned_bit_list_from_ssz_bytes_refines (MAX : Usize) (encoded : alloc.vec.Vec U8) :
    NyxSszRust.bitcollections.BitList.from_ssz_bytes MAX encoded ⦃ actual =>
      match actual with
      | .Ok value => value.encoded = encoded ∧ canonicalOwnedList value.encoded.val (some MAX.val)
      | .Err error => ∃ fault,
          checkedDeserialize (.bitList MAX.val) (bytesToSpec encoded.val) = .error fault ∧
          codecFaultAgrees error fault ⦄ := by
  unfold NyxSszRust.bitcollections.BitList.from_ssz_bytes
  step*
  all_goals cases r <;> simp_all [ownedValidationAgrees, checkedDeserialize, Ssz.Desc.wellFormed, Ssz.deserialize]

@[step] theorem owned_progressive_bit_list_from_ssz_bytes_refines (encoded : alloc.vec.Vec U8) :
    NyxSszRust.bitcollections.ProgressiveBitList.from_ssz_bytes encoded ⦃ actual =>
      match actual with
      | .Ok value => value.encoded = encoded ∧ canonicalOwnedList value.encoded.val none
      | .Err error => ∃ fault,
          checkedDeserialize (.progressiveBitList none) (bytesToSpec encoded.val) = .error fault ∧
          codecFaultAgrees error fault ⦄ := by
  unfold NyxSszRust.bitcollections.ProgressiveBitList.from_ssz_bytes
  step*
  all_goals cases r <;> simp_all [ownedValidationAgrees]

end NyxSszVerification
