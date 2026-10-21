import NyxSszVerification.PackedRoots.ProgressiveRoot
import NyxSszVerification.PackedRoots.View
import NyxSszVerification.Bitfield.Pack

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace NyxSszVerification

/-!
Total implementation contracts underlying the named progressive reference wrappers
and registered theorems in `PackedRoots.Entrypoints`. The pinned `checkedHashTreeRoot`
ignores optional progressive bounds, while the runtime APIs reject over-limit inputs.
These contracts explicitly sequence `Ssz.boundCheck` before that unchanged root,
keeping `codecRootAgrees` unchanged (exact bytes and exact fault categories).
No optional bound or native input is excluded.
-/

/-- Progressive bytes check their byte length before hashing their uint8 sequence. -/
theorem hash_tree_root_progressive_byte_list_with_bound_check
    (bytes : Slice U8) (limit : Option Usize) :
    NyxSszRust.tree_hash.hash_tree_root_progressive_byte_list bytes limit ⦃ actual =>
      codecRootAgrees actual (do
        Ssz.boundCheck (limit.map fun cap => cap.val) bytes.val.length
        checkedHashTreeRoot (.progressiveList (.uint 1) (limit.map fun cap => cap.val))
          (.seq (byteValues bytes.val))) ⦄ := by
  cases chosen : limit
  all_goals unfold NyxSszRust.tree_hash.hash_tree_root_progressive_byte_list NyxSszRust.tree_hash.check_bound
  all_goals step*
  all_goals try (split <;> step*)
  all_goals simp_all [checkedHashTreeRoot_progressiveByteList, Ssz.boundCheck,
    codecRootAgrees, codecFaultAgrees, Bind.bind, Except.bind]
  all_goals split_ifs <;> simp_all
  all_goals omega

/-- Progressive Boolean slices check and mix in their bit length, not byte length. -/
theorem hash_tree_root_progressive_bit_list_with_bound_check
    (bits : Slice Bool) (limit : Option Usize) :
    NyxSszRust.tree_hash.hash_tree_root_progressive_bit_list bits limit ⦃ actual =>
      codecRootAgrees actual (do
        Ssz.boundCheck (limit.map fun cap => cap.val) bits.val.length
        checkedHashTreeRoot (.progressiveBitList (limit.map fun cap => cap.val))
          (.bits (bitsToSpec bits.val))) ⦄ := by
  cases chosen : limit
  all_goals unfold NyxSszRust.tree_hash.hash_tree_root_progressive_bit_list NyxSszRust.tree_hash.check_bound
  all_goals step*
  all_goals try (split <;> step*)
  all_goals simp_all [checkedHashTreeRoot_progressiveBits, Ssz.boundCheck,
    codecRootAgrees, codecFaultAgrees, Bind.bind, Except.bind]
  all_goals split_ifs <;> simp_all
  all_goals omega

/-- Borrowed views need only the existing canonical invariant. Their logical bit
count is widened to u128; no additional usize bound is assumed. -/
theorem hash_tree_root_progressive_bit_list_view_with_bound_check
    (view : NyxSszRust.bitfield.BitListView) (limit : Option Usize)
    (canonical : canonicalBitListView view) :
    NyxSszRust.tree_hash.hash_tree_root_progressive_bit_list_view view limit ⦃ actual =>
      codecRootAgrees actual (do
        Ssz.boundCheck (limit.map fun cap => cap.val) (viewBits view).size
        checkedHashTreeRoot (.progressiveBitList (limit.map fun cap => cap.val))
          (.bits (viewBits view))) ⦄ := by
  have nonempty := canonical.1
  cases chosen : limit
  all_goals unfold NyxSszRust.tree_hash.hash_tree_root_progressive_bit_list_view
  all_goals apply spec_bind (bit_list_view_len_bits_refines view nonempty)
  all_goals intro count count_eq
  all_goals unfold NyxSszRust.tree_hash.check_bound
  all_goals step*
  all_goals try (split <;> step*)
  all_goals try
    subst bytes1
    apply spec_bind (bitlist_payload_refines view count nonempty count_eq)
    intro payload correct
    apply spec_mono (packed_root_progressive_refines view.encoded payload.1 payload.2
      (some count) correct.1)
    intro actual agrees
  all_goals simp_all [checkedHashTreeRoot_progressiveBitList, Ssz.boundCheck,
    viewBits_size, codecRootAgrees, codecFaultAgrees, Bind.bind, Except.bind]
  all_goals split_ifs <;> simp_all
  all_goals omega

end NyxSszVerification
