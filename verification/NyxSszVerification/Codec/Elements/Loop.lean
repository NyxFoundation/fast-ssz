import NyxSszVerification.Codec.Elements.Model
import NyxSszVerification.Loop

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace NyxSszVerification

@[step] theorem decode_ranges_loop_retains {T State : Type}
    (codecInst : NyxSszRust.codec.Ssz T State) (shape : Ssz.Desc) (observe : T → Ssz.Value)
    (law : CodecLaw codecInst shape observe) (input : Slice U8)
    (ranges : Slice NyxSszRust.sequence.BodyRange) (valid : rangesValid input ranges.val)
    (output : alloc.vec.Vec T) (index : Usize)
    (within : index.val ≤ ranges.val.length) (length : output.val.length = index.val) :
    NyxSszRust.codec.decode_ranges_loop codecInst input ranges output index ⦃ actual =>
      decodeRangesModel codecInst input (ranges.val.drop index.val) output.val =
        RustM.ok (sequenceResultToLists actual) ⦄ := by
  let expected := decodeRangesModel codecInst input (ranges.val.drop index.val) output.val
  unfold NyxSszRust.codec.decode_ranges_loop
  apply loop_total
    (invariant := fun state : alloc.vec.Vec T × Usize =>
      state.2.val ≤ ranges.val.length ∧ state.1.val.length = state.2.val ∧
      decodeRangesModel codecInst input (ranges.val.drop state.2.val) state.1.val = expected)
    (measure := fun state => ranges.val.length - state.2.val)
  · rintro ⟨nextOutput, nextIndex⟩ ⟨inBounds, outputLength, model⟩
    by_cases active : nextIndex.val < ranges.val.length
    · have safety := valid _ (List.getElem_mem active)
      unfold NyxSszRust.codec.decode_ranges_loop.body
      step*
      · have transition := model
        rw [List.drop_eq_getElem_cons active, decodeRangesModel,
          ← range_post2, r_post1, ‹r = .Ok value›] at transition
        simp at transition
        refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
        · simp only [values1_post, List.length_append, List.length_singleton, outputLength, index1_post]
        · simpa only [values1_post, index1_post] using transition
      · have transition := model
        rw [List.drop_eq_getElem_cons active, decodeRangesModel,
          ← range_post2, r_post1, ‹r = .Err failure›] at transition
        simpa [sequenceResultToLists] using transition.symm
    · unfold NyxSszRust.codec.decode_ranges_loop.body
      step*
      have atEnd : nextIndex.val = ranges.val.length := by scalar_tac
      simpa only [atEnd, List.drop_length, decodeRangesModel, sequenceResultToLists] using model.symm
  · exact ⟨within, length, rfl⟩

@[step] theorem decode_ranges_retains {T State : Type}
    (codecInst : NyxSszRust.codec.Ssz T State) (shape : Ssz.Desc) (observe : T → Ssz.Value)
    (law : CodecLaw codecInst shape observe) (input : Slice U8)
    (ranges : Slice NyxSszRust.sequence.BodyRange) (valid : rangesValid input ranges.val) :
    NyxSszRust.codec.decode_ranges codecInst input ranges ⦃ actual =>
      decodeRangesModel codecInst input ranges.val [] = RustM.ok (sequenceResultToLists actual) ⦄ := by
  unfold NyxSszRust.codec.decode_ranges
  step*
  simpa only [List.drop_zero] using actual_post

@[step] theorem decode_elements_retains {T State : Type}
    (codecInst : NyxSszRust.codec.Ssz T State) (shape : Ssz.Desc) (observe : T → Ssz.Value)
    (law : CodecLaw codecInst shape observe) (view : NyxSszRust.sequence.SequenceView)
    (valid : sequenceViewValid view) :
    NyxSszRust.codec.decode_elements codecInst view ⦃ actual =>
      decodeRangesModel codecInst view.input view.ranges.val [] =
        RustM.ok (sequenceResultToLists actual) ⦄ := by
  unfold NyxSszRust.codec.decode_elements
  step*
  exact valid

end NyxSszVerification
