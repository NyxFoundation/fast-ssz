import NyxSszVerification.PackedRoots.PackStep
import NyxSszVerification.ProgressiveBits.View

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxHeartbeats 2000000

namespace NyxSszVerification

/-- The borrowed payload, with a mask applied only to its last data byte. -/
def packedInput (bytes : List U8) (count : Nat) (mask : U8) : List U8 :=
  (bytes.take count).mapIdx fun index byte => if index + 1 = count then byte &&& mask else byte

@[simp] theorem packedInput_length (bytes : List U8) (count : Nat) (mask : U8)
    (within : count ≤ bytes.length) :
    (packedInput bytes count mask).length = count := by
  simp [packedInput, Nat.min_eq_left within]

theorem packedInput_get (bytes : List U8) (count index : Nat) (mask : U8)
    (within : count ≤ bytes.length) (active : index < count) :
    (packedInput bytes count mask)[index]'(by simp [within]; omega) =
      if index + 1 = count then bytes[index]'(by omega) &&& mask else bytes[index]'(by omega) := by
  simp [packedInput, List.getElem_mapIdx]

@[simp] theorem packedInput_full (bytes : List U8) :
    packedInput bytes bytes.length 255#u8 = bytes := by
  apply List.ext_getElem
  · simp
  · intro index left right
    rw [packedInput_get _ _ _ _ (by omega) (by simpa using left)]
    split
    · apply UScalar.eq_of_val_eq
      change bytes[index].val &&& (2 ^ 8 - 1) = bytes[index].val
      rw [Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_eq_of_lt bytes[index].hBounds
    · rfl

/-- A final-byte read changes only the masked payload byte. -/
theorem packed_bytes_read_refines (bytes : Slice U8) (count : Usize) (mask : U8)
    (index next : Usize) (within : count.val ≤ bytes.val.length)
    (active : index.val < count.val) (increment : next.val = index.val + 1) :
    (if next = count then do
      let byte ← Slice.index_usize bytes index
      RustM.ok (byte &&& mask)
    else Slice.index_usize bytes index) ⦃ byte =>
      byte = (packedInput bytes.val count.val mask)[index.val]'(by simp [within]; omega) ⦄ := by
  split <;> step*
  all_goals rw [packedInput_get _ _ _ _ within active]
  all_goals split <;> first | rfl | scalar_tac

@[step] theorem packed_bytes_loop_refines (bytes : Slice U8) (count : Usize) (mask : U8)
    (chunks : alloc.vec.Vec RustNode) (pending : RustNode) (filled index : Usize)
    (within : count.val ≤ bytes.val.length) (position : index.val ≤ count.val)
    (initial : collectionPackingState chunks pending filled
      ((packedInput bytes.val count.val mask).drop index.val) (packedInput bytes.val count.val mask)) :
    NyxSszRust.tree_hash.pack_bytes_loop bytes count mask chunks pending filled index
      ⦃ actual => collectionPackingState actual.1 actual.2.1 actual.2.2 []
        (packedInput bytes.val count.val mask) ⦄ := by
  unfold NyxSszRust.tree_hash.pack_bytes_loop
  apply loop_total
    (invariant := fun state : alloc.vec.Vec RustNode × RustNode × Usize × Usize =>
      state.2.2.2.val ≤ count.val ∧ collectionPackingState state.1 state.2.1 state.2.2.1
        ((packedInput bytes.val count.val mask).drop state.2.2.2.val)
        (packedInput bytes.val count.val mask))
    (measure := fun state => count.val - state.2.2.2.val)
  · rintro ⟨nextChunks, nextPending, nextFilled, nextIndex⟩ ⟨inBounds, used, padding, data⟩
    have length := congrArg List.length data
    simp only [List.length_append, collectionChunkBytes_length, List.length_take,
      List.length_drop, Array.length_eq, UScalar.ofNatCore_val_eq,
      Nat.min_eq_left (Nat.le_of_lt used), packedInput_length _ _ _ within] at length
    by_cases active : nextIndex.val < count.val
    · have inputActive : nextIndex.val < (packedInput bytes.val count.val mask).length := by
        simpa [within] using active
      rw [List.drop_eq_getElem_cons inputActive] at data
      unfold NyxSszRust.tree_hash.pack_bytes_loop.body
      step*
      apply spec_bind (packed_bytes_read_refines bytes count mask nextIndex i within active i_post)
      intro byte byteEq
      apply packed_byte_write_then_refines nextChunks nextPending nextFilled byte
        ((packedInput bytes.val count.val mask).drop (nextIndex.val + 1))
        (packedInput bytes.val count.val mask) (by simp [within]; scalar_tac)
        ⟨used, padding, by simpa only [byteEq] using data⟩
      intro result state
      exact ⟨by scalar_tac, by simpa only [i_post] using state, by scalar_tac⟩
    · unfold NyxSszRust.tree_hash.pack_bytes_loop.body
      step*
      have atEnd : nextIndex.val = count.val := by scalar_tac
      exact ⟨used, padding, by simpa [atEnd, List.drop_eq_nil_iff.mpr (by simp [within] :
        (packedInput bytes.val count.val mask).length ≤ count.val)] using data⟩
  · exact ⟨position, initial⟩

/-- Native byte-node packing is exactly the specification's padded leaf array. -/
@[step] theorem pack_bytes_refines (bytes : Slice U8) (count : Usize) (mask : U8)
    (within : count.val ≤ bytes.val.length) :
    NyxSszRust.tree_hash.pack_bytes bytes count mask ⦃ actual =>
      (proofNodes actual.val).toArray = Ssz.packBytes (bytesToSpec (packedInput bytes.val count.val mask)) ⦄ := by
  unfold NyxSszRust.tree_hash.pack_bytes
  apply spec_bind (packed_bytes_loop_refines bytes count mask (alloc.vec.Vec.new _)
    (Array.repeat 32#usize 0#u8) 0#usize 0#usize within (by simp)
    (by simp [collectionPackingState]))
  intro result state
  obtain ⟨chunks, pending, filled⟩ := result
  have packed := collection_pack_final chunks pending filled _ state
  have length := congrArg List.length state.2.2
  simp only [List.length_append, collectionChunkBytes_length, List.length_take,
    List.length_nil, Nat.add_zero, Array.length_eq, UScalar.ofNatCore_val_eq,
    Nat.min_eq_left (Nat.le_of_lt state.1), packedInput_length _ _ _ within] at length
  step*
  · have nonzero : filled.val ≠ 0 := by scalar_tac
    simp [actual_post, proofNodes, packed, nonzero]
  · simp [packed, (show filled.val = 0 by scalar_tac)]

end NyxSszVerification
