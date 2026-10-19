import FastSszVerification.Bitfield.Delimiter

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxRecDepth 4096
set_option maxHeartbeats 200000

namespace FastSszVerification

/-- The bit count determined by the highest set bit of the final encoded byte. -/
def delimitedLength (bytes : List U8) : Nat :=
  8 * (bytes.length - 1) + Ssz.highestBit (bytesToSpec bytes)[bytes.length - 1]!

def viewBits (view : FastSszRust.bitfield.BitListView) : _root_.Array Bool :=
  Ssz.unpackBits (bytesToSpec view.encoded.val) (delimitedLength view.encoded.val)

def canonicalBitListView (view : FastSszRust.bitfield.BitListView) : Prop :=
  0 < view.encoded.val.length ∧
    (bytesToSpec view.encoded.val)[view.encoded.val.length - 1]! ≠ 0

@[step] theorem bit_list_view_as_ssz_bytes_refines (view : FastSszRust.bitfield.BitListView) :
    FastSszRust.bitfield.BitListView.as_ssz_bytes view ⦃ bytes => bytes = view.encoded ⦄ := by
  simp [FastSszRust.bitfield.BitListView.as_ssz_bytes]

theorem usize_max_le_u64 : Usize.max ≤ U64.max := by
  rcases Usize.bounds_eq with width | width
  all_goals rw [width]
  all_goals scalar_tac

@[simp, scalar_tac_simps] theorem usize_cast_u128_val (value : Usize) :
    (UScalar.cast .U128 value).val = value.val := by
  simp only [UScalar.cast_val_eq]
  apply Nat.mod_eq_of_lt
  have maximum := usize_max_le_u64
  scalar_tac

/-- Nonemptiness is an invariant of every view produced by the decoder. -/
@[step] theorem bit_list_view_len_bits_refines (view : FastSszRust.bitfield.BitListView)
    (nonempty : 0 < view.encoded.val.length) :
    FastSszRust.bitfield.BitListView.len_bits view ⦃ count =>
      count.val = delimitedLength view.encoded.val ⦄ := by
  have maximum := usize_max_le_u64
  unfold FastSszRust.bitfield.BitListView.len_bits
  step*
  all_goals have lastLookup := bytesToSpec_getElem_bang view.encoded.val (view.encoded.val.length - 1)
  all_goals have lastInRange : view.encoded.val.length - 1 < view.encoded.val.length := by omega
  all_goals simp_all [delimitedLength, Nat.mul_comm]

end FastSszVerification
