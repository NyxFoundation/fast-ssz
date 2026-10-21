import NyxSszVerification.PackedRoots.Reference
import NyxSszVerification.PackedRoots.View

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace NyxSszVerification

/-!
The pinned reference ignores the optional progressive bound when computing a
root, whereas all three runtime entry points check it. A zero bound and a
positive logical length therefore give an error at runtime and a successful
reference root. These are mismatch witnesses, not weakened refinement laws.
No change to the reference or to `codecRootAgrees` is involved.
-/

/-- Progressive packing without a capacity cannot return a reference error. -/
theorem progressive_packed_error_disagrees (data : Ssz.Bytes) (length : Nat) :
    ¬ codecRootAgrees (.Err .OverLimit) (packedRoot data none (some length)) := by
  simp [packedRoot, codecRootAgrees, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Every nonempty byte slice witnesses the zero-bound root mismatch. -/
theorem progressive_byte_limit_zero_disagrees (bytes : Slice U8)
    (nonempty : 0 < bytes.val.length) :
    NyxSszRust.tree_hash.hash_tree_root_progressive_byte_list bytes (some 0#usize)
      ⦃ actual => ¬ codecRootAgrees actual
        (checkedHashTreeRoot (.progressiveList (.uint 1) (some 0))
          (.seq (byteValues bytes.val))) ⦄ := by
  unfold NyxSszRust.tree_hash.hash_tree_root_progressive_byte_list
    NyxSszRust.tree_hash.check_bound
  step*
  all_goals split <;> step*
  all_goals simp_all [checkedHashTreeRoot_progressiveByteList,
    progressive_packed_error_disagrees]

/-- Raw Boolean slices exhibit the same mismatch, measured in bits. -/
theorem progressive_bit_limit_zero_disagrees (bits : Slice Bool)
    (nonempty : 0 < bits.val.length) :
    NyxSszRust.tree_hash.hash_tree_root_progressive_bit_list bits (some 0#usize)
      ⦃ actual => ¬ codecRootAgrees actual
        (checkedHashTreeRoot (.progressiveBitList (some 0))
          (.bits (bitsToSpec bits.val))) ⦄ := by
  unfold NyxSszRust.tree_hash.hash_tree_root_progressive_bit_list
    NyxSszRust.tree_hash.check_bound
  step*
  all_goals split <;> step*
  all_goals simp_all [checkedHashTreeRoot_progressiveBits,
    progressive_packed_error_disagrees]

/-- Even canonical decoded views disagree: this is not malformed input. -/
theorem progressive_view_limit_zero_disagrees (view : NyxSszRust.bitfield.BitListView)
    (canonical : canonicalBitListView view)
    (positive : 0 < delimitedLength view.encoded.val) :
    NyxSszRust.tree_hash.hash_tree_root_progressive_bit_list_view view (some 0#usize)
      ⦃ actual => ¬ codecRootAgrees actual
        (checkedHashTreeRoot (.progressiveBitList (some 0)) (.bits (viewBits view))) ⦄ := by
  unfold NyxSszRust.tree_hash.hash_tree_root_progressive_bit_list_view
  apply spec_bind (bit_list_view_len_bits_refines view canonical.1)
  intro count length
  unfold NyxSszRust.tree_hash.check_bound
  step*
  all_goals split <;> step*
  all_goals simp_all [checkedHashTreeRoot_progressiveBitList,
    progressive_packed_error_disagrees]

end NyxSszVerification
