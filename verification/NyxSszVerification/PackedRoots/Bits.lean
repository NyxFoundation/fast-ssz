import NyxSszVerification.PackedRoots.Root
import NyxSszVerification.Bitfield.Pack

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxHeartbeats 2000000

namespace NyxSszVerification

@[step] theorem packed_div_ceil_bits (count : Usize) :
    NyxSszRust.core.num.Usize.div_ceil count 256#usize ⦃ actual =>
      actual.val = (count.val + 255) / 256 ⦄ := by
  unfold NyxSszRust.core.num.Usize.div_ceil
  step*

/-- Packing bits into bytes and then nodes has the same capacity as packing into nodes directly. -/
theorem packed_bits_node_count (count : Nat) :
    ((count + 7) / 8 + 31) / 32 = (count + 255) / 256 := by omega

@[step] theorem packed_bits_root_refines (bits : Slice Bool) (bytes : alloc.vec.Vec U8)
    (capacity : Usize) (length : Option U128)
    (packed : bytesToSpec bytes.val = Ssz.packBits (bitsToSpec bits.val) ((bits.val.length + 7) / 8))
    (room : (bits.val.length + 255) / 256 ≤ capacity.val) :
    NyxSszRust.tree_hash.packed_root (alloc.vec.Vec.deref bytes) (alloc.vec.Vec.len bytes)
      255#u8 (some capacity) length ⦃ actual =>
        codecRootAgrees actual (packedRoot
          (Ssz.packBits (bitsToSpec bits.val) ((bits.val.length + 7) / 8))
          (some capacity.val) (length.map fun value => value.val)) ⦄ := by
  have size : bytes.val.length = (bits.val.length + 7) / 8 := by
    have sizes := congrArg _root_.Array.size packed
    simpa [Ssz.packBits] using sizes
  apply spec_mono (packed_root_full_bounded_refines (alloc.vec.Vec.deref bytes) capacity length
    (by simpa only [alloc.vec.Vec.deref, size, packed_bits_node_count] using room))
  intro actual correct
  simpa only [alloc.vec.Vec.deref, packed] using correct

/-- Raw Boolean vectors observe all low-bit-first data bits without a delimiter. -/
theorem hash_tree_root_bit_vector_refines (bits : Slice Bool) (length : Usize) :
    NyxSszRust.tree_hash.hash_tree_root_bit_vector bits length ⦃ actual =>
      codecRootAgrees actual (checkedHashTreeRoot (.bitVector length.val) (.bits (bitsToSpec bits.val))) ⦄ := by
  unfold NyxSszRust.tree_hash.hash_tree_root_bit_vector
  step*
  all_goals simp_all [checkedHashTreeRoot_bitVector, codecRootAgrees, codecFaultAgrees,
    Ssz.chunksForBits, Ssz.bytesPerChunk]

/-- Bounded bit-list roots mix in the actual bit length rather than encoded byte length. -/
theorem hash_tree_root_bit_list_refines (bits : Slice Bool) (limit : Usize) :
    NyxSszRust.tree_hash.hash_tree_root_bit_list bits limit ⦃ actual =>
      codecRootAgrees actual (checkedHashTreeRoot (.bitList limit.val) (.bits (bitsToSpec bits.val))) ⦄ := by
  unfold NyxSszRust.tree_hash.hash_tree_root_bit_list NyxSszRust.tree_hash.check_bound
  step*
  all_goals split <;> step*
  all_goals simp_all [checkedHashTreeRoot_bitList, codecRootAgrees, codecFaultAgrees,
    Ssz.chunksForBits, Ssz.bytesPerChunk]
  all_goals split_ifs <;> first | assumption | omega

end NyxSszVerification
