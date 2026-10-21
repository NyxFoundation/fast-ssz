import NyxSszVerification.PackedRoots.Root
import NyxSszVerification.PackedRoots.Progressive

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxHeartbeats 2000000

namespace NyxSszVerification

/-- Progressive hashing is total on every masked native byte payload. -/
@[step] theorem packed_root_progressive_refines (bytes : Slice U8) (count : Usize) (mask : U8)
    (length : Option U128) (within : count.val ≤ bytes.val.length) :
    NyxSszRust.tree_hash.packed_root bytes count mask none length ⦃ actual =>
      codecRootAgrees actual (packedRoot (bytesToSpec (packedInput bytes.val count.val mask))
        none (length.map fun value => value.val)) ⦄ := by
  unfold NyxSszRust.tree_hash.packed_root
  apply spec_bind (pack_bytes_refines bytes count mask within)
  intro chunks packed
  apply spec_bind (merkleize_progressive_refines (alloc.vec.Vec.deref chunks))
  intro root correct
  have packedList : proofNodes chunks.val =
      (Ssz.packBytes (bytesToSpec (packedInput bytes.val count.val mask))).toList := by
    simpa only [List.toList_toArray] using congrArg _root_.Array.toList packed
  cases chosen : length
  all_goals step*
  all_goals simp_all [codecRootAgrees, packedRoot, Ssz.mixIn,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

@[step] theorem packed_root_full_progressive_refines (bytes : Slice U8) (length : Option U128) :
    NyxSszRust.tree_hash.packed_root bytes (Slice.len bytes) 255#u8 none length ⦃ actual =>
      codecRootAgrees actual (packedRoot (bytesToSpec bytes.val) none (length.map fun value => value.val)) ⦄ := by
  simpa using packed_root_progressive_refines bytes (Slice.len bytes) 255#u8 length (by simp)

end NyxSszVerification
