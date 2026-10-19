import NyxSszVerification.Sequence.Reference

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace NyxSszVerification

@[step] theorem read_offsets_loop_refines (input : Slice U8) (count : Usize)
    (output : alloc.vec.Vec Usize) (index : Usize)
    (budget : count.val * 4 ≤ input.val.length) (within : index.val ≤ count.val)
    (data : offsetValues output.val = Ssz.readOffsets (bytesToSpec input.val) index.val) :
    NyxSszRust.sequence.read_offsets_loop input count output index ⦃ actual =>
      ∃ offsets, actual = .Ok offsets ∧
        offsetValues offsets.val = Ssz.readOffsets (bytesToSpec input.val) count.val ⦄ := by
  unfold NyxSszRust.sequence.read_offsets_loop
  apply loop_total
    (invariant := fun state : alloc.vec.Vec Usize × Usize =>
      state.2.val ≤ count.val ∧ offsetValues state.1.val =
        Ssz.readOffsets (bytesToSpec input.val) state.2.val)
    (measure := fun state => count.val - state.2.val)
  · rintro ⟨nextOutput, nextIndex⟩ ⟨inBounds, values⟩
    have outputLength : nextOutput.val.length = nextIndex.val := by
      have same := congrArg List.length values
      simpa using same
    unfold NyxSszRust.sequence.read_offsets_loop.body
    step*
    have same : offset = r := by grind
    have converted : offset1.val = r.val := by simp [offset1_post, same]
    have read : r.val = Ssz.readUint (bytesToSpec input.val) (nextIndex.val * 4) 4 := by
      rw [r_post2, s_post1, bytesToSpec_slice,
        sequence_read_uint_extract _ _ _ _ _ (by scalar_tac)
          (by simp only [bytesToSpec_size]; scalar_tac)]
      simp only [Nat.add_zero, start_post]
    refine ⟨by scalar_tac, ?_, by scalar_tac⟩
    rw [offsets1_post, offsetValues_append, offsetValues_singleton, converted, read,
      values, index1_post, read_offsets_succ]
  · exact ⟨within, data⟩

@[step] theorem read_offsets_refines (input : Slice U8) (count : Usize)
    (budget : count.val * 4 ≤ input.val.length) :
    NyxSszRust.sequence.read_offsets input count ⦃ actual =>
      match actual with
      | .Ok offsets => offsetValues offsets.val = Ssz.readOffsets (bytesToSpec input.val) count.val
      | .Err _ => False ⦄ := by
  unfold NyxSszRust.sequence.read_offsets
  step*
  all_goals simp_all [offsetValues, Ssz.readOffsets]

end NyxSszVerification
