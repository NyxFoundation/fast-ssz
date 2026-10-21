import NyxSszVerification.Collection.Append
import NyxSszVerification.Collection.Size
import NyxSszVerification.Unsigned

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxHeartbeats 2000000

namespace NyxSszVerification

def collectionSlots (parts : List (alloc.vec.Vec U8)) (fixed : Bool) : List (Bool × Ssz.Bytes) :=
  parts.map fun part => (fixed, bytesToSpec part.val)

@[local step] theorem collection_encode_offset (value : U32) :
    NyxSszRust.scalar.encode_u32 value ⦃ actual =>
      bytesToSpec actual.val = Ssz.uintBytes 4 value.val ⦄ := by
  have bound : value.val < 4294967296 := by scalar_tac
  apply spec_mono (encode_u32_refines value)
  intro actual correct
  simpa [Ssz.serialize, bound] using correct.symm

@[step] theorem collection_offsets_loop_refines (parts : Slice (alloc.vec.Vec U8))
    (output : alloc.vec.Vec U8) (offset index : Usize)
    (within : index.val ≤ parts.val.length)
    (room : output.val.length + (parts.val.length - index.val) * 4 ≤ Usize.max)
    (endBound : offset.val + collectionBodySize (parts.val.drop index.val) < 4294967296) :
    NyxSszRust.collection_wire.assemble_loop1 parts output offset index ⦃ actual =>
      actual.val.length = output.val.length + (parts.val.length - index.val) * 4 ∧
      bytesToSpec actual.val = bytesToSpec output.val ++
        Ssz.headOf offset.val (collectionSlots (parts.val.drop index.val) false) ⦄ := by
  let expected := bytesToSpec output.val ++
    Ssz.headOf offset.val (collectionSlots (parts.val.drop index.val) false)
  let finalLength := output.val.length + (parts.val.length - index.val) * 4
  let ending := offset.val + collectionBodySize (parts.val.drop index.val)
  unfold NyxSszRust.collection_wire.assemble_loop1
  apply loop_total
    (invariant := fun state : alloc.vec.Vec U8 × Usize × Usize =>
      state.2.2.val ≤ parts.val.length ∧
      state.1.val.length + (parts.val.length - state.2.2.val) * 4 = finalLength ∧
      state.2.1.val + collectionBodySize (parts.val.drop state.2.2.val) = ending ∧
      bytesToSpec state.1.val ++
        Ssz.headOf state.2.1.val (collectionSlots (parts.val.drop state.2.2.val) false) = expected)
    (measure := fun state => parts.val.length - state.2.2.val)
  · rintro ⟨nextOutput, nextOffset, nextIndex⟩ ⟨inBounds, size, endEq, data⟩
    have nextBound : nextOffset.val < 4294967296 := by dsimp only at endEq; omega
    have castEq : (UScalar.cast .U32 nextOffset).val = nextOffset.val := by
      apply UScalar.cast_val_mod_pow_of_inBounds_eq
      exact nextBound
    have capacity : nextOutput.val.length + (parts.val.length - nextIndex.val) * 4 ≤ Usize.max := by
      exact size.trans_le room
    by_cases active : nextIndex.val < parts.val.length
    · have splitEnd := endEq
      rw [List.drop_eq_getElem_cons active, collectionBodySize_cons] at splitEnd
      unfold NyxSszRust.collection_wire.assemble_loop1.body
      step*
      refine ⟨by scalar_tac, ?_, ?_, ?_, by scalar_tac⟩
      · have arraySize := a.property
        simp only [output1_post, List.length_append, index1_post]
        scalar_tac
      · simp only [offset1_post, index1_post, v_post2]
        scalar_tac
      · rw [List.drop_eq_getElem_cons active] at data
        simp only [collectionSlots, List.map_cons, Ssz.headOf] at data
        have encoded : bytesToSpec s.val = Ssz.uintBytes 4 nextOffset.val := by
          simpa only [s_post, Array.to_slice, i1_post, castEq] using a_post
        change bytesToSpec output1.val ++
          Ssz.headOf offset1.val (collectionSlots (parts.val.drop index1.val) false) = expected
        have appendBytes : bytesToSpec output1.val = bytesToSpec nextOutput.val ++ bytesToSpec s.val := by
          simp [output1_post, bytesToSpec]
        have offsetEq : offset1.val = nextOffset.val + (parts.val[nextIndex.val]).val.length := by scalar_tac
        rw [appendBytes, encoded, index1_post, offsetEq]
        simpa only [bytesToSpec_size, Ssz.bytesPerOffset, collectionSlots,
          _root_.Array.append_assoc] using data
    · unfold NyxSszRust.collection_wire.assemble_loop1.body
      step*
      have atEnd : nextIndex.val = parts.val.length := by scalar_tac
      constructor
      · simpa only [atEnd, Nat.sub_self, Nat.zero_mul, Nat.add_zero] using size
      · change bytesToSpec nextOutput.val = expected
        simpa only [atEnd, List.drop_length, collectionSlots, List.map_nil, Ssz.headOf,
          _root_.Array.append_empty] using data
  · exact ⟨within, rfl, rfl, rfl⟩

end NyxSszVerification
