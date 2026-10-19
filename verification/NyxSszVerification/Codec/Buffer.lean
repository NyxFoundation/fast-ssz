import NyxSszRust.Codec
import NyxSszVerification.Loop

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace NyxSszVerification

@[step] theorem fixed_bytes_loop_refines {count : Usize} (input : Array U8 count)
    (output : alloc.vec.Vec U8) (index : Usize)
    (within : index.val ≤ count.val) (initial : output.val = input.val.take index.val) :
    NyxSszRust.codec.fixed_bytes_loop input output index ⦃ result => result.val = input.val ⦄ := by
  unfold NyxSszRust.codec.fixed_bytes_loop
  apply loop_total
    (invariant := fun state : alloc.vec.Vec U8 × Usize =>
      state.2.val ≤ count.val ∧ state.1.val = input.val.take state.2.val)
    (measure := fun state => count.val - state.2.val)
  · rintro ⟨nextOutput, nextIndex⟩ ⟨inBounds, data⟩
    change nextIndex.val ≤ count.val at inBounds
    change nextOutput.val = input.val.take nextIndex.val at data
    have size := input.property
    have outputLength : nextOutput.val.length = nextIndex.val := by
      have same := congrArg List.length data
      simpa only [List.length_take, size, Nat.min_eq_left inBounds] using same
    unfold NyxSszRust.codec.fixed_bytes_loop.body
    step*
    · have inside : nextIndex.val < input.val.length := by scalar_tac
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [output1_post, data, index1_post, List.take_succ_eq_append_getElem inside, i_post2]
    · have atEnd : nextIndex.val = count.val := by scalar_tac
      simpa only [atEnd, ← size, List.take_length] using data
  · exact ⟨within, initial⟩

@[step] theorem fixed_bytes_refines {count : Usize} (input : Array U8 count) :
    NyxSszRust.codec.fixed_bytes input ⦃ output => output.val = input.val ⦄ := by
  unfold NyxSszRust.codec.fixed_bytes
  step*
  simp

end NyxSszVerification
