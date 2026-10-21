import NyxSszVerification.PackedRoots.Pack
import NyxSszVerification.PackedRoots.Words
import NyxSszVerification.PackedRoots.Reference
import NyxSszVerification.Merkleize

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxHeartbeats 2000000

namespace NyxSszVerification

/-- A checked node capacity prevents the internal MerkleizeError branch. -/
theorem packed_merkleize_refines (chunks : Slice RustNode) (capacity : Usize)
    (within : chunks.val.length ≤ capacity.val) :
    NyxSszRust.merkle.merkleize chunks (some capacity) ⦃ actual =>
      ∃ root, actual = .Ok root ∧ bytesToSpec root.val =
        Ssz.subtreeAt (proofNodes chunks.val).toArray (Ssz.depthFor capacity.val) 0 ⦄ := by
  apply spec_mono (merkleize_refines chunks (some capacity))
  intro actual agrees
  cases actual with
  | Ok root =>
    exact ⟨root, rfl, by simpa [merkleizeAgrees, Ssz.merkleizeBounded, Nat.not_lt.mpr within,
      Bind.bind, Except.bind, Pure.pure, Except.pure] using agrees⟩
  | Err fault =>
    simp [merkleizeAgrees, Ssz.merkleizeBounded, Nat.not_lt.mpr within,
      Bind.bind, Except.bind, Pure.pure, Except.pure] at agrees

/-- The shared bounded root helper preserves every packed byte and the full length word. -/
@[step] theorem packed_root_bounded_refines (bytes : Slice U8) (count : Usize) (mask : U8)
    (capacity : Usize) (length : Option U128)
    (within : count.val ≤ bytes.val.length)
    (room : (count.val + 31) / 32 ≤ capacity.val) :
    NyxSszRust.tree_hash.packed_root bytes count mask (some capacity) length ⦃ actual =>
      codecRootAgrees actual (packedRoot (bytesToSpec (packedInput bytes.val count.val mask))
        (some capacity.val) (length.map fun value => value.val)) ⦄ := by
  unfold NyxSszRust.tree_hash.packed_root
  apply spec_bind (pack_bytes_refines bytes count mask within)
  intro chunks packed
  have size : chunks.val.length = (count.val + 31) / 32 := by
    have sizes := congrArg _root_.Array.size packed
    simpa [Ssz.packBytes, Ssz.bytesPerChunk, within] using sizes
  apply spec_bind (packed_merkleize_refines (alloc.vec.Vec.deref chunks) capacity (by simpa [size] using room))
  intro result correct
  obtain ⟨root, same, correct⟩ := correct
  simp only [same]
  have packedSize : (Ssz.packBytes (bytesToSpec (packedInput bytes.val count.val mask))).size ≤ capacity.val := by
    simp [Ssz.packBytes, Ssz.bytesPerChunk, within]
    exact room
  cases chosen : length
  all_goals step*
  all_goals simp_all [codecRootAgrees, packedRoot, Ssz.merkleizeBounded,
    Nat.not_lt.mpr packedSize, Ssz.mixIn, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- The raw-slice entrypoints use an all-ones mask and the complete slice. -/
@[step] theorem packed_root_full_bounded_refines (bytes : Slice U8)
    (capacity : Usize) (length : Option U128)
    (room : (bytes.val.length + 31) / 32 ≤ capacity.val) :
    NyxSszRust.tree_hash.packed_root bytes (Slice.len bytes) 255#u8 (some capacity) length ⦃ actual =>
      codecRootAgrees actual (packedRoot (bytesToSpec bytes.val)
        (some capacity.val) (length.map fun value => value.val)) ⦄ := by
  simpa using
    packed_root_bounded_refines bytes (Slice.len bytes) 255#u8 capacity length (by simp) (by simpa using room)

end NyxSszVerification
