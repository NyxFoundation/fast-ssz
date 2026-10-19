import Ssz.Codec.Root

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace FastSszVerification

theorem root_single_chunk (budget : Nat) (shape : Ssz.Desc) (value : Ssz.Value)
    (chunk : Ssz.Bytes)
    (layout : Ssz.merkleLayout shape value = .ok (.packing #[chunk] (some 1))) :
    Ssz.hashTreeRootAt (budget + 1) shape value = .ok chunk := by
  simp [Ssz.hashTreeRootAt, layout, Ssz.layoutChunksAt, Ssz.MerkleLayout.packing,
    Ssz.Leaves.count, Ssz.merkleizeBounded, Ssz.depthFor, Ssz.subtreeAt, Ssz.padded,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem packBytes_single_chunk (data : Ssz.Bytes) (positive : 0 < data.size)
    (within : data.size ≤ 32) :
    Ssz.packBytes data = #[data ++ Array.replicate (32 - data.size) 0] := by
  have full : data.extract 0 32 = data := by
    apply Array.ext
    · simp [Nat.min_eq_right within]
    intro index left right
    simp
  have count : (data.size + Ssz.bytesPerChunk - 1) / Ssz.bytesPerChunk = 1 := by
    simp only [Ssz.bytesPerChunk]
    omega
  unfold Ssz.packBytes
  rw [count]
  apply Array.ext
  · simp
  intro index left right
  have zero : index = 0 := by simp at right; omega
  subst index
  simp [Ssz.bytesPerChunk, full]

theorem fixedLeaf_single_chunk (shape : Ssz.Desc) (value : Ssz.Value) (data : Ssz.Bytes)
    (encoded : Ssz.serialize shape value = .ok data)
    (positive : 0 < data.size) (within : data.size ≤ 32) :
    Ssz.fixedLeaf shape value =
      .ok (.packing #[data ++ Array.replicate (32 - data.size) 0] (some 1)) := by
  simp [Ssz.fixedLeaf, encoded, packBytes_single_chunk _ positive within,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem hashTreeRoot_uint_encoded (width value : Nat) (data : Ssz.Bytes)
    (encoded : Ssz.serialize (.uint width) (.uint value) = .ok data)
    (positive : 0 < data.size) (within : data.size ≤ 32) :
    Ssz.hashTreeRoot (.uint width) (.uint value) =
      .ok (data ++ Array.replicate (32 - data.size) 0) := by
  apply root_single_chunk 0
  exact fixedLeaf_single_chunk _ _ data encoded positive within

theorem hashTreeRoot_bool_encoded (value : Bool) (data : Ssz.Bytes)
    (encoded : Ssz.serialize .bool (.bool value) = .ok data)
    (positive : 0 < data.size) (within : data.size ≤ 32) :
    Ssz.hashTreeRoot .bool (.bool value) =
      .ok (data ++ Array.replicate (32 - data.size) 0) := by
  apply root_single_chunk 0
  exact fixedLeaf_single_chunk _ _ data encoded positive within

theorem hashTreeRoot_bool_form (value : Bool) :
    Ssz.hashTreeRoot .bool (.bool value) =
      .ok (#[if value then 1 else 0] ++ Array.replicate 31 0) := by
  apply root_single_chunk 0
  exact fixedLeaf_single_chunk .bool (.bool value) #[if value then 1 else 0]
    (by simp [Ssz.serialize]) (by simp) (by simp)

end FastSszVerification
