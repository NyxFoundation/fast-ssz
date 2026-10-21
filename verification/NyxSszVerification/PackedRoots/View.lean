import NyxSszVerification.PackedRoots.ViewPacking
import NyxSszVerification.PackedRoots.ProgressiveRoot

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace NyxSszVerification

/-- Payload arithmetic never needs the bit count to fit in `usize`. -/
theorem bitlist_payload_arithmetic_refines (byteCount : Usize) (bitCount : U128)
    (nonempty : 0 < byteCount.val) :
    NyxSszRust.tree_hash.bitlist_payload byteCount bitCount ⦃ output =>
      output.1.val = (if bitCount.val % 8 = 0 then byteCount.val - 1 else byteCount.val) ∧
      (if bitCount.val % 8 = 0 then output.2 = 255#u8
       else output.2.val = 2 ^ (bitCount.val % 8) - 1) ⦄ := by
  unfold NyxSszRust.tree_hash.bitlist_payload
  step*
  all_goals
    have remainderValue : remainder.val = bitCount.val % 8 := by
      rw [remainder_post, UScalar.cast_val_eq]
      change i.val % 4294967296 = bitCount.val % 8
      omega
    have small : bitCount.val % 8 < 8 := Nat.mod_lt _ (by decide)
    generalize equation : bitCount.val % 8 = width at *
    interval_cases width <;> simp_all [UScalar.eq_equiv, Nat.shiftLeft_eq, U8.size, U8.numBits]

/-- Delimiter removal produces all and only the packed view bits. No machine-size
bound is imposed on their widened count. -/
@[step] theorem bitlist_payload_refines (view : NyxSszRust.bitfield.BitListView)
    (count : U128) (nonempty : 0 < view.encoded.val.length)
    (count_eq : count.val = delimitedLength view.encoded.val) :
    NyxSszRust.tree_hash.bitlist_payload (Slice.len view.encoded) count ⦃ output =>
      output.1.val ≤ view.encoded.val.length ∧
      bytesToSpec (packedInput view.encoded.val output.1.val output.2) =
        Ssz.packBits (viewBits view) (((viewBits view).size + 7) / 8) ∧
      (viewBits view).size = delimitedLength view.encoded.val ⦄ := by
  apply spec_mono (bitlist_payload_arithmetic_refines (Slice.len view.encoded) count
    (by simpa using nonempty))
  intro output arithmetic
  have bounds := delimitedLength_bounds view.encoded.val nonempty
  have width : output.1.val = (delimitedLength view.encoded.val + 7) / 8 := by
    have position := arithmetic.1
    change output.1.val = (if count.val % 8 = 0 then
      view.encoded.val.length - 1 else view.encoded.val.length) at position
    rw [count_eq] at position
    split at position <;> omega
  have within : output.1.val ≤ view.encoded.val.length := by omega
  refine ⟨within, ?_, viewBits_size view⟩
  rw [viewBits_size]
  simpa only [viewBits] using
    packedInput_packBits view.encoded.val output.1.val
      (delimitedLength view.encoded.val) output.2 within width
      (by simpa only [count_eq] using arithmetic.2)

/-- The existing decoder invariant suffices for length computation and payload packing. -/
theorem bit_list_view_payload_refines (view : NyxSszRust.bitfield.BitListView)
    (canonical : canonicalBitListView view) :
    (do
      let count ← NyxSszRust.bitfield.BitListView.len_bits view
      let payload ← NyxSszRust.tree_hash.bitlist_payload (Slice.len view.encoded) count
      RustM.ok (count, payload)) ⦃ output =>
      output.1.val = (viewBits view).size ∧
      output.2.1.val ≤ view.encoded.val.length ∧
      bytesToSpec (packedInput view.encoded.val output.2.1.val output.2.2) =
        Ssz.packBits (viewBits view) (((viewBits view).size + 7) / 8) ⦄ := by
  apply spec_bind (bit_list_view_len_bits_refines view canonical.1)
  intro count length
  apply spec_bind (bitlist_payload_refines view count canonical.1 length)
  intro payload correct
  simp only [spec_ok]
  exact ⟨by simpa only [viewBits_size] using length, correct.1, correct.2.1⟩

/-- Once payload arithmetic has run, the view's tree uses the complete bit packing
and mixes in its full bit length, rather than its byte count. -/
theorem bit_list_view_packed_root_refines (view : NyxSszRust.bitfield.BitListView)
    (length : U128) (count : Usize) (mask : U8)
    (length_eq : length.val = (viewBits view).size)
    (within : count.val ≤ view.encoded.val.length)
    (packed : bytesToSpec (packedInput view.encoded.val count.val mask) =
      Ssz.packBits (viewBits view) (((viewBits view).size + 7) / 8)) :
    NyxSszRust.tree_hash.packed_root view.encoded count mask none (some length) ⦃ actual =>
      codecRootAgrees actual
        (checkedHashTreeRoot (.progressiveBitList none) (.bits (viewBits view))) ⦄ := by
  rw [checkedHashTreeRoot_progressiveBitList]
  apply spec_mono (packed_root_progressive_refines view.encoded count mask
    (some length) within)
  intro actual agrees
  simpa only [Option.map_some, packed, length_eq] using agrees

/-- With no optional bound, canonical borrowed views have exactly the pinned tree
root. The bounded API's separate validation/reference mismatch is not assumed away. -/
theorem hash_tree_root_progressive_bit_list_view_unbounded_refines
    (view : NyxSszRust.bitfield.BitListView) (canonical : canonicalBitListView view) :
    NyxSszRust.tree_hash.hash_tree_root_progressive_bit_list_view view none ⦃ actual =>
      codecRootAgrees actual
        (checkedHashTreeRoot (.progressiveBitList none) (.bits (viewBits view))) ⦄ := by
  unfold NyxSszRust.tree_hash.hash_tree_root_progressive_bit_list_view
  apply spec_bind (bit_list_view_len_bits_refines view canonical.1)
  intro length count_eq
  simp only [NyxSszRust.tree_hash.check_bound]
  step*
  subst bytes1
  apply spec_bind (bitlist_payload_refines view length canonical.1 count_eq)
  intro payload correct
  apply bit_list_view_packed_root_refines view length payload.1 payload.2
    (by simpa only [viewBits_size] using count_eq) correct.1 correct.2.1

end NyxSszVerification
