import NyxSszVerification.OwnedBits.Packing

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace NyxSszVerification

@[step] theorem owned_copy_loop_refines (bytes : Slice U8) (output : alloc.vec.Vec U8) (index : Usize)
    (within : index.val ≤ bytes.val.length) (initialData : output.val = bytes.val.take index.val) :
    NyxSszRust.bit_storage.copy_bytes_loop bytes output index ⦃ actual => actual.val = bytes.val ⦄ := by
  unfold NyxSszRust.bit_storage.copy_bytes_loop
  apply loop_total
    (invariant := fun state : alloc.vec.Vec U8 × Usize =>
      state.2.val ≤ bytes.val.length ∧ state.1.val = bytes.val.take state.2.val)
    (measure := fun state => bytes.val.length - state.2.val)
  · rintro ⟨nextOutput, nextIndex⟩ ⟨position, data⟩
    change nextIndex.val ≤ bytes.val.length at position
    change nextOutput.val = bytes.val.take nextIndex.val at data
    have outputLength : nextOutput.val.length = nextIndex.val := by
      have same := congrArg List.length data
      simpa only [List.length_take, Nat.min_eq_left position] using same
    unfold NyxSszRust.bit_storage.copy_bytes_loop.body
    step*
    · have inside : nextIndex.val < bytes.val.length := by scalar_tac
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [output1_post, data, index1_post, List.take_succ_eq_append_getElem inside, i1_post2]
    · have atEnd : nextIndex.val = bytes.val.length := by scalar_tac
      simpa only [atEnd, List.take_length] using data
  · exact ⟨within, initialData⟩

@[step] theorem owned_copy_bytes_refines (bytes : Slice U8) :
    NyxSszRust.bit_storage.copy_bytes bytes ⦃ actual => actual.val = bytes.val ⦄ := by
  unfold NyxSszRust.bit_storage.copy_bytes
  step*
  all_goals simp_all

/-- The native final-byte write is exactly a full-length packed mask. -/
theorem owned_set_last_mask (bytes : List U8) (mask : U8) (nonempty : 0 < bytes.length) :
    bytes.set (bytes.length - 1) (bytes[bytes.length - 1]! &&& mask) =
      packedInput bytes bytes.length mask := by
  apply List.ext_getElem
  · simp
  intro index left right
  have inside : index < bytes.length := by simpa using left
  rw [packedInput_get _ _ _ _ (by omega) inside]
  by_cases last : index = bytes.length - 1
  · subst index
    have ending : bytes.length - 1 + 1 = bytes.length := by omega
    simp [inside, ending]
  · have notLast : index + 1 ≠ bytes.length := by omega
    simp [Ne.symm last, notLast]

end NyxSszVerification
