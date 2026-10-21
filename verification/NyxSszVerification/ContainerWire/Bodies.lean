import NyxSszVerification.ContainerWire.Model

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxHeartbeats 2000000

namespace NyxSszVerification

/-- Append only the variable bodies, including zero-length bodies. -/
@[step] theorem container_bodies_loop_refines (slots : Slice (Bool × alloc.vec.Vec U8))
    (output : alloc.vec.Vec U8) (index : Usize) (within : index.val ≤ slots.val.length)
    (room : output.val.length + containerBodySize (slots.val.drop index.val) ≤ Usize.max) :
    NyxSszRust.container_wire.assemble_loop1 slots output index ⦃ actual =>
      actual.val.length = output.val.length + containerBodySize (slots.val.drop index.val) ∧
      bytesToSpec actual.val = bytesToSpec output.val ++
        Ssz.bodiesOf (containerSlots (slots.val.drop index.val)) ⦄ := by
  let expected := bytesToSpec output.val ++ Ssz.bodiesOf (containerSlots (slots.val.drop index.val))
  let finalLength := output.val.length + containerBodySize (slots.val.drop index.val)
  unfold NyxSszRust.container_wire.assemble_loop1
  apply loop_total
    (invariant := fun state : alloc.vec.Vec U8 × Usize =>
      state.2.val ≤ slots.val.length ∧
      state.1.val.length + containerBodySize (slots.val.drop state.2.val) = finalLength ∧
      bytesToSpec state.1.val ++ Ssz.bodiesOf (containerSlots (slots.val.drop state.2.val)) = expected)
    (measure := fun state => slots.val.length - state.2.val)
  · rintro ⟨nextOutput, nextIndex⟩ ⟨inside, size, data⟩
    have capacity := size.trans_le room
    by_cases active : nextIndex.val < slots.val.length
    · have sizeStep := size
      rw [List.drop_eq_getElem_cons active] at sizeStep data capacity
      unfold NyxSszRust.container_wire.assemble_loop1.body
      step*
      rcases v with ⟨fixed, part⟩
      rw [← b_post2] at sizeStep data capacity
      cases fixed
      · change (do
          let output1 ← NyxSszRust.collection_wire.append nextOutput (alloc.vec.Vec.deref part)
          let index1 ← nextIndex + 1#usize
          pure (ControlFlow.cont (output1, index1))) ⦃ _ ⦄
        simp only [containerBodySize_cons, containerSlots_cons, Bool.false_eq_true,
          if_false, Ssz.bodiesOf] at sizeStep data capacity
        step*
        refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
        · simp only [output1_post, List.length_append, index1_post, collection_deref_values]
          omega
        · have appended : bytesToSpec output1.val = bytesToSpec nextOutput.val ++ bytesToSpec part.val := by
            rw [output1_post]
            simp only [collection_deref_values, bytesToSpec, List.map_append, List.append_toArray]
          rw [appended, index1_post, _root_.Array.append_assoc]
          exact data
      · change (do
          let index1 ← nextIndex + 1#usize
          pure (ControlFlow.cont (nextOutput, index1))) ⦃ _ ⦄
        simp only [containerBodySize_cons, containerSlots_cons, if_true,
          Ssz.bodiesOf, Nat.zero_add] at sizeStep data capacity
        step*
    · unfold NyxSszRust.container_wire.assemble_loop1.body
      step*
      have atEnd : nextIndex.val = slots.val.length := by scalar_tac
      constructor
      · simpa only [atEnd, List.drop_length, containerBodySize_nil, Nat.add_zero] using size
      · simpa only [atEnd, List.drop_length, containerSlots_nil, Ssz.bodiesOf,
          _root_.Array.append_empty] using data
  · exact ⟨within, rfl, rfl⟩

end NyxSszVerification
