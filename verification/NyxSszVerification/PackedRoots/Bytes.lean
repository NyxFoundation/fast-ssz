import NyxSszVerification.PackedRoots.Root
import NyxSszVerification.Collection.Capacity

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxHeartbeats 2000000

namespace NyxSszVerification

/-- Every native byte slice either matches the vector declaration or reports its exact fault. -/
theorem hash_tree_root_byte_vector_refines (bytes : Slice U8) (length : Usize) :
    NyxSszRust.tree_hash.hash_tree_root_byte_vector bytes length ⦃ actual =>
      codecRootAgrees actual (checkedHashTreeRoot (.byteVector length.val) (.bytes (bytesToSpec bytes.val))) ⦄ := by
  unfold NyxSszRust.tree_hash.hash_tree_root_byte_vector
  step*
  all_goals simp_all [checkedHashTreeRoot_byteVector, codecRootAgrees, codecFaultAgrees,
    Ssz.chunksForBytes, Ssz.bytesPerChunk]

/-- Empty lists, zero limits and maximal machine limits use the same exact root law. -/
theorem hash_tree_root_byte_list_refines (bytes : Slice U8) (limit : Usize) :
    NyxSszRust.tree_hash.hash_tree_root_byte_list bytes limit ⦃ actual =>
      codecRootAgrees actual (checkedHashTreeRoot (.byteList limit.val) (.bytes (bytesToSpec bytes.val))) ⦄ := by
  unfold NyxSszRust.tree_hash.hash_tree_root_byte_list NyxSszRust.tree_hash.check_bound
  step*
  all_goals split <;> step*
  all_goals simp_all [checkedHashTreeRoot_byteList, codecRootAgrees, codecFaultAgrees,
    Ssz.chunksForBytes, Ssz.bytesPerChunk]
  all_goals split_ifs <;> first | assumption | omega

end NyxSszVerification
