import NyxSszVerification.ContainerWire.Model

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxHeartbeats 2000000

namespace NyxSszVerification

@[local step] theorem container_encode_offset (value : U32) :
    NyxSszRust.scalar.encode_u32 value ⦃ actual =>
      bytesToSpec actual.val = Ssz.uintBytes 4 value.val ⦄ :=
  collection_encode_offset value

/-- Mixed inline bytes and offsets, with native capacity and offset safety. -/
@[step] theorem container_header_loop_refines (slots : Slice (Bool × alloc.vec.Vec U8))
    (offset : Usize) (output : alloc.vec.Vec U8) (index : Usize)
    (within : index.val ≤ slots.val.length)
    (room : output.val.length + containerHeadSize (slots.val.drop index.val) ≤ Usize.max)
    (endBound : offset.val + containerBodySize (slots.val.drop index.val) < 4294967296) :
    NyxSszRust.container_wire.assemble_loop0 slots offset output index ⦃ actual =>
      actual.val.length = output.val.length + containerHeadSize (slots.val.drop index.val) ∧
      bytesToSpec actual.val = bytesToSpec output.val ++
        Ssz.headOf offset.val (containerSlots (slots.val.drop index.val)) ⦄ := by
  let expected := bytesToSpec output.val ++ Ssz.headOf offset.val (containerSlots (slots.val.drop index.val))
  let finalLength := output.val.length + containerHeadSize (slots.val.drop index.val)
  let ending := offset.val + containerBodySize (slots.val.drop index.val)
  unfold NyxSszRust.container_wire.assemble_loop0
  apply loop_total
    (invariant := fun state : Usize × alloc.vec.Vec U8 × Usize =>
      state.2.2.val ≤ slots.val.length ∧
      state.2.1.val.length + containerHeadSize (slots.val.drop state.2.2.val) = finalLength ∧
      state.1.val + containerBodySize (slots.val.drop state.2.2.val) = ending ∧
      bytesToSpec state.2.1.val ++
        Ssz.headOf state.1.val (containerSlots (slots.val.drop state.2.2.val)) = expected)
    (measure := fun state => slots.val.length - state.2.2.val)
  · rintro ⟨nextOffset, nextOutput, nextIndex⟩ ⟨inside, size, endEq, data⟩
    have nextBound : nextOffset.val < 4294967296 := by dsimp only at endEq; omega
    have castEq : (UScalar.cast .U32 nextOffset).val = nextOffset.val := by
      apply UScalar.cast_val_mod_pow_of_inBounds_eq
      exact nextBound
    have capacity := size.trans_le room
    by_cases active : nextIndex.val < slots.val.length
    · have sizeStep := size
      have endStep := endEq
      rw [List.drop_eq_getElem_cons active] at sizeStep endStep capacity data
      unfold NyxSszRust.container_wire.assemble_loop0.body
      step*
      rcases v with ⟨fixed, part⟩
      rw [← b_post2] at sizeStep endStep capacity data
      cases fixed
      · change (do
          let (offset1, output1) ← (do
            let i1 ← lift (UScalar.cast .U32 nextOffset)
            let a ← NyxSszRust.scalar.encode_u32 i1
            let s ← lift (Array.to_slice a)
            let output2 ← NyxSszRust.collection_wire.append nextOutput s
            let offset2 ← nextOffset + alloc.vec.Vec.len part
            pure (offset2, output2))
          let index1 ← nextIndex + 1#usize
          pure (ControlFlow.cont (offset1, output1, index1))) ⦃ _ ⦄
        simp only [containerHeadSize_cons, containerBodySize_cons, containerSlots_cons,
          Bool.false_eq_true, if_false, Ssz.headOf] at sizeStep endStep capacity data
        step as ⟨i1, i1_post⟩
        step as ⟨a, a_post⟩
        step as ⟨s, s_post⟩
        step as ⟨output2, output2_post⟩
        step as ⟨offset2, offset2_post⟩
        step*
        refine ⟨by scalar_tac, ?_, ?_, ?_, by scalar_tac⟩
        · have arraySize := a.property
          simp only [output2_post, List.length_append, index1_post]
          scalar_tac
        · simp only [offset2_post, index1_post]
          scalar_tac
        · have encoded : bytesToSpec s.val = Ssz.uintBytes 4 nextOffset.val := by
            simpa only [s_post, Array.to_slice, i1_post, castEq] using a_post
          have appended : bytesToSpec output2.val = bytesToSpec nextOutput.val ++ bytesToSpec s.val := by
            rw [output2_post]
            simp only [bytesToSpec, List.map_append, List.append_toArray]
          rw [appended, encoded, index1_post, offset2_post]
          simpa only [bytesToSpec_size, Ssz.bytesPerOffset, alloc.vec.Vec.len_val,
            _root_.Array.append_assoc] using data
      · change (do
          let (offset1, output1) ← (do
            let output2 ← NyxSszRust.collection_wire.append nextOutput (alloc.vec.Vec.deref part)
            pure (nextOffset, output2))
          let index1 ← nextIndex + 1#usize
          pure (ControlFlow.cont (offset1, output1, index1))) ⦃ _ ⦄
        simp only [containerHeadSize_cons, containerBodySize_cons, containerSlots_cons,
          if_true, Ssz.headOf, Nat.zero_add] at sizeStep endStep capacity data
        step as ⟨output2, output2_post⟩
        step*
        refine ⟨by scalar_tac, ?_, ?_, ?_, by scalar_tac⟩
        · simp only [output2_post, List.length_append, collection_deref_values, index1_post]
          omega
        · simpa only [index1_post] using endStep
        · have appended : bytesToSpec output2.val = bytesToSpec nextOutput.val ++ bytesToSpec part.val := by
            rw [output2_post]
            simp only [collection_deref_values, bytesToSpec, List.map_append, List.append_toArray]
          rw [appended, index1_post, _root_.Array.append_assoc]
          exact data
    · unfold NyxSszRust.container_wire.assemble_loop0.body
      step*
      have atEnd : nextIndex.val = slots.val.length := by scalar_tac
      constructor
      · simpa only [atEnd, List.drop_length, containerHeadSize_nil, Nat.add_zero] using size
      · simpa only [atEnd, List.drop_length, containerSlots_nil, Ssz.headOf,
          _root_.Array.append_empty] using data
  · exact ⟨within, rfl, rfl, rfl⟩

end NyxSszVerification
