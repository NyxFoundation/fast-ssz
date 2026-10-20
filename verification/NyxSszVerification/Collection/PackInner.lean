import NyxSszVerification.Collection.PackState

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxHeartbeats 2000000

namespace NyxSszVerification

@[step] theorem collection_pack_inner_refines (parts : Slice (alloc.vec.Vec U8))
    (chunks : alloc.vec.Vec RustNode) (pending : RustNode) (filled part byte : Usize)
    (suffix data : List U8) (partBound : part.val < parts.val.length)
    (byteBound : byte.val ≤ (parts.val[part.val]).val.length)
    (bound : data.length ≤ Usize.max * 32)
    (initial : collectionPackingState chunks pending filled
      ((parts.val[part.val]).val.drop byte.val ++ suffix) data) :
    NyxSszRust.collection_tree.pack_parts_loop0_loop0 parts chunks pending filled part byte
      ⦃ actual => collectionPackingState actual.1 actual.2.1 actual.2.2 suffix data ⦄ := by
  unfold NyxSszRust.collection_tree.pack_parts_loop0_loop0
  apply loop_total
    (invariant := fun state : alloc.vec.Vec RustNode × RustNode × Usize × Usize =>
      state.2.2.2.val ≤ (parts.val[part.val]).val.length ∧
      collectionPackingState state.1 state.2.1 state.2.2.1
        ((parts.val[part.val]).val.drop state.2.2.2.val ++ suffix) data)
    (measure := fun state => (parts.val[part.val]).val.length - state.2.2.2.val)
  · rintro ⟨nextChunks, nextPending, nextFilled, nextByte⟩ ⟨inBounds, used, padding, bytes⟩
    have pendingSize : nextPending.val.length = 32 := by simp
    have length := congrArg List.length bytes
    simp only [List.length_append, collectionChunkBytes_length, List.length_take,
      List.length_drop, pendingSize, Nat.min_eq_left (Nat.le_of_lt used)] at length
    by_cases active : nextByte.val < (parts.val[part.val]).val.length
    · have update := collection_pending_update nextPending nextFilled.val
        ((parts.val[part.val]).val[nextByte.val]) used padding
      unfold NyxSszRust.collection_tree.pack_parts_loop0_loop0.body
      step*
      by_cases full : filled1 = 32#usize
      · simp only [full, if_true, bind_assoc_eq]
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        have pendingEq : (index_mut_back i1).val =
            nextPending.val.set nextFilled.val ((parts.val[part.val]).val[nextByte.val]) := by
          simp [__post3, i1_post, v_post2]
        have fullCount : nextFilled.val + 1 = 32 := by scalar_tac
        have closed : (index_mut_back i1).val = nextPending.val.take nextFilled.val ++
            [(parts.val[part.val]).val[nextByte.val]] := by
          have current := update.1
          rw [← pendingEq, fullCount] at current
          have nodeSize : (index_mut_back i1).val.length = 32 := by simp
          simpa only [List.take_of_length_le (by omega : (index_mut_back i1).val.length ≤ 32)] using current
        refine ⟨by simp, by simp, ?_⟩
        rw [List.drop_eq_getElem_cons active] at bytes
        simp only [x_post, collectionChunkBytes_append, collectionChunkBytes_singleton, closed]
        simpa only [byte1_post, UScalar.ofNatCore_val_eq, List.take_zero, List.append_nil,
          List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using bytes
      · simp only [full, if_false, bind_tc_ok]
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        have pendingEq : (index_mut_back i1).val =
            nextPending.val.set nextFilled.val ((parts.val[part.val]).val[nextByte.val]) := by
          simp [__post3, i1_post, v_post2]
        refine ⟨by scalar_tac, ?_, ?_⟩
        · simpa only [pendingEq, filled1_post] using update.2
        · rw [List.drop_eq_getElem_cons active] at bytes
          change collectionChunkBytes nextChunks.val ++
            (index_mut_back i1).val.take filled1.val ++ _ = data
          rw [pendingEq, filled1_post, update.1, byte1_post]
          simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using bytes
    · unfold NyxSszRust.collection_tree.pack_parts_loop0_loop0.body
      step*
      have atEnd : nextByte.val = (parts.val[part.val]).val.length := by scalar_tac
      exact ⟨used, padding, by simpa only [atEnd, List.drop_length, List.nil_append] using bytes⟩
  · exact ⟨byteBound, initial⟩

end NyxSszVerification
