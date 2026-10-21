import NyxSszRust.CollectionWire
import NyxSszVerification.Collections
import NyxSszVerification.Loop

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxHeartbeats 2000000

namespace NyxSszVerification

@[step] theorem collection_append_loop_refines (output : alloc.vec.Vec U8)
    (input : Slice U8) (index : Usize)
    (within : index.val ≤ input.val.length)
    (room : output.val.length + (input.val.length - index.val) ≤ Usize.max) :
    NyxSszRust.collection_wire.append_loop output input index ⦃ actual =>
      actual.val = output.val ++ input.val.drop index.val ⦄ := by
  let expected := output.val ++ input.val.drop index.val
  unfold NyxSszRust.collection_wire.append_loop
  apply loop_total
    (invariant := fun state : alloc.vec.Vec U8 × Usize =>
      state.2.val ≤ input.val.length ∧
      state.1.val.length + (input.val.length - state.2.val) ≤ Usize.max ∧
      state.1.val ++ input.val.drop state.2.val = expected)
    (measure := fun state => input.val.length - state.2.val)
  · rintro ⟨nextOutput, nextIndex⟩ ⟨inBounds, capacity, data⟩
    unfold NyxSszRust.collection_wire.append_loop.body
    step*
    · refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · simp only [output1_post, List.length_append, List.length_singleton, index1_post]
        scalar_tac
      · have active : nextIndex.val < input.val.length := by scalar_tac
        rw [output1_post, index1_post, i1_post2, List.append_assoc,
          List.singleton_append, ← List.drop_eq_getElem_cons active]
        exact data
    · have atEnd : nextIndex.val = input.val.length := by scalar_tac
      simpa only [atEnd, List.drop_length, List.append_nil] using data
  · exact ⟨within, room, rfl⟩

@[step] theorem collection_append_refines (output : alloc.vec.Vec U8) (input : Slice U8)
    (room : output.val.length + input.val.length ≤ Usize.max) :
    NyxSszRust.collection_wire.append output input ⦃ actual =>
      actual.val = output.val ++ input.val ⦄ := by
  simpa [NyxSszRust.collection_wire.append] using
    collection_append_loop_refines output input 0#usize (by simp) room

end NyxSszVerification
