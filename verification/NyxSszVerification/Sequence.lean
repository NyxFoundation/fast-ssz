import NyxSszVerification.Sequence.Model

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace NyxSszVerification

@[step] theorem offset_spans_loop_refines (offsets : Slice Usize) (scope : Usize)
    (output : alloc.vec.Vec Usize) (index : Usize)
    (within : index.val ≤ offsets.val.length) (length : output.val.length = index.val) :
    NyxSszRust.sequence.offset_spans_loop offsets scope output index ⦃ actual =>
      offsetSpansAgree actual
        (offsetSuffix offsets.val scope.val index.val (offsetValues output.val)) ⦄ := by
  let expected := offsetSuffix offsets.val scope.val index.val (offsetValues output.val)
  unfold NyxSszRust.sequence.offset_spans_loop
  apply loop_total
    (invariant := fun state : alloc.vec.Vec Usize × Usize =>
      state.2.val ≤ offsets.val.length ∧ state.1.val.length = state.2.val ∧
      offsetSuffix offsets.val scope.val state.2.val (offsetValues state.1.val) = expected)
    (measure := fun state => offsets.val.length - state.2.val)
  · rintro ⟨nextOutput, nextIndex⟩ ⟨inBounds, outputLength, model⟩
    unfold NyxSszRust.sequence.offset_spans_loop.body
    step*
    · have pairInside : nextIndex.val + 1 < offsets.val.length := by scalar_tac
      have unordered : offsets.val[nextIndex.val + 1].val < offsets.val[nextIndex.val].val := by
        scalar_tac
      change offsetSpansAgree _ expected
      rw [← model, offset_suffix_unordered _ _ _ _ pairInside unordered]
      trivial
    · have pairInside : nextIndex.val + 1 < offsets.val.length := by scalar_tac
      have ordered : offsets.val[nextIndex.val].val ≤ offsets.val[nextIndex.val + 1].val := by
        scalar_tac
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · simp only [spans1_post, List.length_append, List.length_singleton,
          outputLength, next_index_post]
      · simp only [spans1_post, offsetValues_append, offsetValues_singleton, i2_post1,
          next_post2, start_post2, next_index_post]
        exact (offset_suffix_next _ _ _ _ pairInside ordered).symm.trans model
    · have last : nextIndex.val + 1 = offsets.val.length := by scalar_tac
      have past : scope.val < offsets.val[nextIndex.val].val := by scalar_tac
      change offsetSpansAgree _ expected
      rw [← model, offset_suffix_last _ _ _ _ last, if_pos past]
      trivial
    · have last : nextIndex.val + 1 = offsets.val.length := by scalar_tac
      have notPast : ¬scope.val < offsets.val[nextIndex.val].val := by scalar_tac
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · simp only [spans1_post, List.length_append, List.length_singleton,
          outputLength, next_index_post]
      · rw [next_index_post, last, offset_suffix_done, ← model,
          offset_suffix_last _ _ _ _ last, if_neg notPast]
        simp only [spans1_post, offsetValues_append,
          offsetValues_singleton, i2_post1, start_post2]
    · have atEnd : nextIndex.val = offsets.val.length := by scalar_tac
      change offsetSpansAgree _ expected
      rw [← model, atEnd, offset_suffix_done]
      rfl
  · exact ⟨within, length, rfl⟩

theorem offset_spans_refines (offsets : Slice Usize) (scope : Usize) :
    NyxSszRust.sequence.offset_spans offsets scope ⦃ actual =>
      offsetSpansAgree actual (Ssz.offsetSpans (offsetValues offsets.val) scope.val) ⦄ := by
  unfold NyxSszRust.sequence.offset_spans
  step*
  change offsetSpansAgree actual
    (Except.map id (Ssz.offsetSpans (offsetValues offsets.val) scope.val)) at actual_post
  simpa only [Except.map_id, id_eq] using actual_post

end NyxSszVerification
