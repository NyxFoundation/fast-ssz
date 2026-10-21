import NyxSszVerification.PackedRoots.ProgressiveApi
import NyxSszVerification.PackedRoots.ProgressiveReference

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace NyxSszVerification

/-- Total byte-root conformance uses the explicitly composed bound check and unchanged
upstream root; the latter alone intentionally does not validate progressive bounds. -/
theorem hash_tree_root_progressive_byte_list_refines (bytes : Slice U8) (limit : Option Usize) :
    NyxSszRust.tree_hash.hash_tree_root_progressive_byte_list bytes limit ⦃ actual =>
      codecRootAgrees actual
        (checkedProgressiveByteRoot (limit.map fun cap => cap.val) bytes.val) ⦄ := by
  simpa [checkedProgressiveByteRoot, byteValues] using
    hash_tree_root_progressive_byte_list_with_bound_check bytes limit

/-- The composed bit contract observes every Boolean and checks its full length before
calling the pinned root. It does not change the generic CodecLaw contract. -/
theorem hash_tree_root_progressive_bit_list_refines (bits : Slice Bool) (limit : Option Usize) :
    NyxSszRust.tree_hash.hash_tree_root_progressive_bit_list bits limit ⦃ actual =>
      codecRootAgrees actual
        (checkedProgressiveBitRoot (limit.map fun cap => cap.val) (bitsToSpec bits.val)) ⦄ := by
  simpa [checkedProgressiveBitRoot] using
    hash_tree_root_progressive_bit_list_with_bound_check bits limit

/-- Canonical decoded views satisfy the same composed contract as Boolean slices.
The complete bit observation determines the count, including values beyond usize. -/
theorem hash_tree_root_progressive_bit_list_view_refines
    (view : NyxSszRust.bitfield.BitListView) (limit : Option Usize)
    (canonical : canonicalBitListView view) :
    NyxSszRust.tree_hash.hash_tree_root_progressive_bit_list_view view limit ⦃ actual =>
      codecRootAgrees actual
        (checkedProgressiveBitRoot (limit.map fun cap => cap.val) (viewBits view)) ⦄ := by
  simpa only [checkedProgressiveBitRoot] using
    hash_tree_root_progressive_bit_list_view_with_bound_check view limit canonical

end NyxSszVerification
