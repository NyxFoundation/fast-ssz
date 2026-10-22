import NyxSszVerification.OwnedBits.Law

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace NyxSszVerification

/-- Preserve all logical bits, their order and the complete widened length. -/
def observeOwnedBoundedProgressive {MAX : Usize}
    (value : NyxSszRust.bitcollections.BoundedProgressiveBitList MAX) : Ssz.Value :=
  .bits (ownedListBits value.encoded.val)

@[step] theorem owned_bounded_progressive_bit_list_as_ssz_bytes_refines {MAX : Usize}
    (value : NyxSszRust.bitcollections.BoundedProgressiveBitList MAX) :
    NyxSszRust.bitcollections.BoundedProgressiveBitList.as_ssz_bytes value ⦃ bytes => bytes.val = value.encoded.val ⦄ := by
  simp [NyxSszRust.bitcollections.BoundedProgressiveBitList.as_ssz_bytes]

@[step] theorem owned_bounded_progressive_bit_list_len_bits_refines {MAX : Usize}
    (value : NyxSszRust.bitcollections.BoundedProgressiveBitList MAX) :
    NyxSszRust.bitcollections.BoundedProgressiveBitList.len_bits value ⦃ count => count.val = (ownedListBits value.encoded.val).size ⦄ := by
  unfold NyxSszRust.bitcollections.BoundedProgressiveBitList.len_bits
  step*
  simp_all

@[step] theorem owned_bounded_progressive_bit_list_get_refines {MAX : Usize}
    (value : NyxSszRust.bitcollections.BoundedProgressiveBitList MAX) (index : U128) :
    NyxSszRust.bitcollections.BoundedProgressiveBitList.get value index ⦃ actual => actual = (ownedListBits value.encoded.val)[index.val]? ⦄ := by
  unfold NyxSszRust.bitcollections.BoundedProgressiveBitList.get
  step*

/-- Byte validation preserves exact delimiter faults and the complete accepted allocation. -/
@[step] theorem owned_bounded_progressive_bit_list_from_ssz_bytes_refines (MAX : Usize) (encoded : alloc.vec.Vec U8) :
    NyxSszRust.bitcollections.BoundedProgressiveBitList.from_ssz_bytes MAX encoded ⦃ actual =>
      match actual with
      | .Ok value => value.encoded = encoded ∧ canonicalOwnedList value.encoded.val (some MAX.val)
      | .Err error => ∃ fault,
          checkedDeserialize (.progressiveBitList (some MAX.val)) (bytesToSpec encoded.val) = .error fault ∧
          codecFaultAgrees error fault ⦄ := by
  unfold NyxSszRust.bitcollections.BoundedProgressiveBitList.from_ssz_bytes
  step*
  all_goals cases r <;> simp_all [ownedValidationAgrees, checkedDeserialize, Ssz.Desc.wellFormed, Ssz.deserialize]

end NyxSszVerification
