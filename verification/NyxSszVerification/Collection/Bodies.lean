import NyxSszVerification.Collection.Append
import NyxSszVerification.Collection.Size
import NyxSszVerification.Bytes

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxHeartbeats 2000000

namespace NyxSszVerification

def collectionBodyBytes (parts : List (alloc.vec.Vec U8)) : List U8 :=
  parts.flatMap fun part => part.val

@[simp] theorem collectionBodyBytes_nil : collectionBodyBytes [] = [] := rfl

@[simp] theorem collectionBodyBytes_cons (part : alloc.vec.Vec U8)
    (rest : List (alloc.vec.Vec U8)) :
    collectionBodyBytes (part :: rest) = part.val ++ collectionBodyBytes rest := rfl

@[simp] theorem collectionBodyBytes_length (parts : List (alloc.vec.Vec U8)) :
    (collectionBodyBytes parts).length = collectionBodySize parts := by
  induction parts with
  | nil => rfl
  | cons part rest ih => simp [ih]

@[step] theorem collection_bodies_loop_refines (parts : Slice (alloc.vec.Vec U8))
    (output : alloc.vec.Vec U8) (index : Usize) (within : index.val ≤ parts.val.length)
    (room : output.val.length + collectionBodySize (parts.val.drop index.val) ≤ Usize.max) :
    NyxSszRust.collection_wire.assemble_loop0 parts output index ⦃ actual =>
      actual.val = output.val ++ collectionBodyBytes (parts.val.drop index.val) ⦄ := by
  let expected := output.val ++ collectionBodyBytes (parts.val.drop index.val)
  unfold NyxSszRust.collection_wire.assemble_loop0
  apply loop_total
    (invariant := fun state : alloc.vec.Vec U8 × Usize =>
      state.2.val ≤ parts.val.length ∧
      state.1.val.length + collectionBodySize (parts.val.drop state.2.val) ≤ Usize.max ∧
      state.1.val ++ collectionBodyBytes (parts.val.drop state.2.val) = expected)
    (measure := fun state => parts.val.length - state.2.val)
  · rintro ⟨nextOutput, nextIndex⟩ ⟨inBounds, capacity, data⟩
    by_cases active : nextIndex.val < parts.val.length
    · have remaining := capacity
      rw [List.drop_eq_getElem_cons active, collectionBodySize_cons] at remaining
      unfold NyxSszRust.collection_wire.assemble_loop0.body
      step*
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · simp only [output1_post, List.length_append, index1_post]
        scalar_tac
      · rw [List.drop_eq_getElem_cons active, collectionBodyBytes_cons] at data
        simpa only [output1_post, index1_post, v_post2, collection_deref_values, List.append_assoc] using data
    · unfold NyxSszRust.collection_wire.assemble_loop0.body
      step*
      have atEnd : nextIndex.val = parts.val.length := by scalar_tac
      simpa only [atEnd, List.drop_length, collectionBodyBytes_nil, List.append_nil] using data
  · exact ⟨within, room, rfl⟩

@[step] theorem collection_bodies_loop2_refines (parts : Slice (alloc.vec.Vec U8))
    (output : alloc.vec.Vec U8) (index : Usize) (within : index.val ≤ parts.val.length)
    (room : output.val.length + collectionBodySize (parts.val.drop index.val) ≤ Usize.max) :
    NyxSszRust.collection_wire.assemble_loop2 parts output index ⦃ actual =>
      actual.val = output.val ++ collectionBodyBytes (parts.val.drop index.val) ⦄ :=
  collection_bodies_loop_refines parts output index within room

end NyxSszVerification
