import NyxSszVerification.Collection.PackInner

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxHeartbeats 2000000

namespace NyxSszVerification

@[step] theorem collection_pack_outer_refines (parts : Slice (alloc.vec.Vec U8))
    (chunks : alloc.vec.Vec RustNode) (pending : RustNode) (filled part : Usize)
    (data : List U8) (within : part.val ≤ parts.val.length)
    (bound : data.length ≤ Usize.max * 32)
    (initial : collectionPackingState chunks pending filled
      (collectionBodyBytes (parts.val.drop part.val)) data) :
    NyxSszRust.collection_tree.pack_parts_loop0 parts chunks pending filled part
      ⦃ actual => collectionPackingState actual.1 actual.2.1 actual.2.2 [] data ⦄ := by
  unfold NyxSszRust.collection_tree.pack_parts_loop0
  apply loop_total
    (invariant := fun state : alloc.vec.Vec RustNode × RustNode × Usize × Usize =>
      state.2.2.2.val ≤ parts.val.length ∧
      collectionPackingState state.1 state.2.1 state.2.2.1
        (collectionBodyBytes (parts.val.drop state.2.2.2.val)) data)
    (measure := fun state => parts.val.length - state.2.2.2.val)
  · rintro ⟨nextChunks, nextPending, nextFilled, nextPart⟩ ⟨inBounds, state⟩
    by_cases active : nextPart.val < parts.val.length
    · unfold NyxSszRust.collection_tree.pack_parts_loop0.body
      have activeScalar : nextPart < Slice.len parts := by scalar_tac
      simp only [activeScalar, if_true]
      apply spec_bind (collection_pack_inner_refines parts nextChunks nextPending nextFilled
        nextPart 0#usize (collectionBodyBytes (parts.val.drop (nextPart.val + 1))) data active
        (by simp) bound (by
          simp only [UScalar.ofNatCore_val_eq, List.drop_zero]
          rw [List.drop_eq_getElem_cons active, collectionBodyBytes_cons] at state
          exact state))
      intro result resultState
      obtain ⟨chunks1, pending1, filled1⟩ := result
      step*
    · unfold NyxSszRust.collection_tree.pack_parts_loop0.body
      step*
      have atEnd : nextPart.val = parts.val.length := by scalar_tac
      simpa only [atEnd, List.drop_length, collectionBodyBytes_nil] using state
  · exact ⟨within, initial⟩

/-- The final open node is padded once, while an empty open node contributes no leaf. -/
theorem collection_pack_final (chunks : alloc.vec.Vec RustNode) (pending : RustNode)
    (filled : Usize) (data : List U8)
    (state : collectionPackingState chunks pending filled [] data) :
    Ssz.packBytes (bytesToSpec data) = (proofNodes chunks.val).toArray ++
      (if filled.val = 0 then #[] else #[bytesToSpec pending.val]) := by
  obtain ⟨within, padding, bytes⟩ := state
  have openSize : (pending.val.take filled.val).length = filled.val := by simp; omega
  have form : bytesToSpec data = bytesToSpec (collectionChunkBytes chunks.val) ++
      bytesToSpec (pending.val.take filled.val) := by
    rw [← bytes]
    simp [bytesToSpec]
  rw [form]
  change Ssz.packBytes (bytesToSpec (chunks.val.flatMap fun chunk => chunk.val) ++ _) = _
  rw [collection_pack_complete]
  by_cases empty : filled.val = 0
  · simp [empty, bytesToSpec, Ssz.packBytes, Ssz.bytesPerChunk]
  · have packed := packBytes_single_chunk (bytesToSpec (pending.val.take filled.val))
      (by simp only [bytesToSpec_size, openSize]; omega)
      (by simp only [bytesToSpec_size, openSize]; omega)
    rw [packed]
    simp only [empty, if_false, bytesToSpec_size, openSize]
    congr 2
    have same : pending.val = pending.val.take filled.val ++ List.replicate (32 - filled.val) 0#u8 := by
      rw [← padding, List.take_append_drop]
    simpa [bytesToSpec, byteToSpec] using (congrArg bytesToSpec same).symm

@[step] theorem collection_pack_parts_refines (parts : Slice (alloc.vec.Vec U8))
    (bound : collectionBodySize parts.val ≤ Usize.max * 32) :
    NyxSszRust.collection_tree.pack_parts parts ⦃ actual =>
      (proofNodes actual.val).toArray = Ssz.packBytes (bytesToSpec (collectionBodyBytes parts.val)) ⦄ := by
  unfold NyxSszRust.collection_tree.pack_parts
  apply spec_bind (collection_pack_outer_refines parts (alloc.vec.Vec.new _)
    (Array.repeat 32#usize 0#u8) 0#usize 0#usize (collectionBodyBytes parts.val)
    (by simp) (by simpa using bound) (by simp [collectionPackingState]))
  intro result state
  obtain ⟨chunks, pending, filled⟩ := result
  have packed := collection_pack_final chunks pending filled _ state
  have length := congrArg List.length state.2.2
  have pendingSize : pending.val.length = 32 := by simp
  simp only [List.length_append, collectionChunkBytes_length, List.length_take,
    List.length_nil, Nat.add_zero, pendingSize, Nat.min_eq_left (Nat.le_of_lt state.1),
    collectionBodyBytes_length] at length
  step*
  · have nonzero : filled.val ≠ 0 := by scalar_tac
    simp [actual_post, proofNodes, packed, nonzero]
  · simp [packed, (show filled.val = 0 by scalar_tac)]

end NyxSszVerification
