import NyxSszVerification.Sequence.Bounds
import NyxSszVerification.Sequence.View

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace NyxSszVerification

def rangeValues (ranges : List NyxSszRust.sequence.BodyRange) : List (Nat × Nat) :=
  ranges.map fun range => (range.start.val, range.end.val)

def bodyBounds (offsets spans : List Nat) : List (Nat × Nat) :=
  (offsets.zip spans).map fun (start, span) => (start, start + span)

@[simp] theorem rangeValues_append (left right : List NyxSszRust.sequence.BodyRange) :
    rangeValues (left ++ right) = rangeValues left ++ rangeValues right := by simp [rangeValues]

@[simp] theorem rangeValues_singleton (range : NyxSszRust.sequence.BodyRange) :
    rangeValues [range] = [(range.start.val, range.end.val)] := rfl

@[simp] theorem rangeValues_length (ranges : List NyxSszRust.sequence.BodyRange) :
    (rangeValues ranges).length = ranges.length := by simp [rangeValues]

@[simp] theorem bodyBounds_length (offsets spans : List Nat)
    (sized : spans.length = offsets.length) :
    (bodyBounds offsets spans).length = offsets.length := by simp [bodyBounds, sized]

theorem bodyBounds_at (offsets spans : List Usize) (index : Nat)
    (left : index < offsets.length) (right : index < spans.length) :
    (bodyBounds (offsetValues offsets) (offsetValues spans))[index]'(by
      simp [bodyBounds]; omega) = (offsets[index].val, offsets[index].val + spans[index].val) := by
  simp [bodyBounds, offsetValues]

@[step] theorem body_ranges_loop_refines (offsets spans : Slice Usize)
    (output : alloc.vec.Vec NyxSszRust.sequence.BodyRange) (index : Usize)
    (sized : spans.val.length = offsets.val.length)
    (safe : ∀ position (left : position < offsets.val.length) (right : position < spans.val.length),
      offsets.val[position].val + spans.val[position].val ≤ Usize.max)
    (within : index.val ≤ offsets.val.length)
    (data : rangeValues output.val =
      (bodyBounds (offsetValues offsets.val) (offsetValues spans.val)).take index.val) :
    NyxSszRust.sequence.body_ranges_loop offsets spans output index ⦃ result =>
      rangeValues result.val = bodyBounds (offsetValues offsets.val) (offsetValues spans.val) ⦄ := by
  let expected := bodyBounds (offsetValues offsets.val) (offsetValues spans.val)
  have fullLength : expected.length = offsets.val.length := by simp [expected, sized]
  unfold NyxSszRust.sequence.body_ranges_loop
  apply loop_total
    (invariant := fun state : alloc.vec.Vec NyxSszRust.sequence.BodyRange × Usize =>
      state.2.val ≤ offsets.val.length ∧ rangeValues state.1.val = expected.take state.2.val)
    (measure := fun state => offsets.val.length - state.2.val)
  · rintro ⟨nextOutput, nextIndex⟩ ⟨inBounds, values⟩
    have outputLength : nextOutput.val.length = nextIndex.val := by
      have same := congrArg List.length values
      simpa [fullLength, Nat.min_eq_left inBounds] using same
    by_cases active : nextIndex.val < offsets.val.length
    · have spanActive : nextIndex.val < spans.val.length := by omega
      have sum := safe nextIndex.val active spanActive
      unfold NyxSszRust.sequence.body_ranges_loop.body
      step*
      have inside : nextIndex.val < expected.length := by omega
      have atIndex : expected[nextIndex.val] =
          (offsets.val[nextIndex.val].val,
            offsets.val[nextIndex.val].val + spans.val[nextIndex.val].val) :=
        bodyBounds_at _ _ _ active spanActive
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [ranges1_post, rangeValues_append, rangeValues_singleton,
        values, index1_post, List.take_succ_eq_append_getElem inside, atIndex]
      simp only [end_post, start_post2, i1_post2]
    · unfold NyxSszRust.sequence.body_ranges_loop.body
      step*
      have atEnd : nextIndex.val = offsets.val.length := by scalar_tac
      simpa only [atEnd, ← fullLength, List.take_length] using values
  · exact ⟨within, data⟩

@[step] theorem body_ranges_refines (offsets spans : Slice Usize)
    (sized : spans.val.length = offsets.val.length)
    (safe : ∀ position (left : position < offsets.val.length) (right : position < spans.val.length),
      offsets.val[position].val + spans.val[position].val ≤ Usize.max) :
    NyxSszRust.sequence.body_ranges offsets spans ⦃ result =>
      rangeValues result.val = bodyBounds (offsetValues offsets.val) (offsetValues spans.val) ⦄ := by
  unfold NyxSszRust.sequence.body_ranges
  step*
  simp [rangeValues]

theorem sequence_view_from_ranges (input : Slice U8)
    (offsets spans : alloc.vec.Vec Usize) (ranges : alloc.vec.Vec NyxSszRust.sequence.BodyRange)
    (read : Ssz.offsetSpans (offsetValues offsets.val) input.val.length = .ok (offsetValues spans.val))
    (data : rangeValues ranges.val = bodyBounds (offsetValues offsets.val) (offsetValues spans.val)) :
    sequenceViewValid ⟨input, ranges⟩ ∧
      (sequenceElements ⟨input, ranges⟩).map bytesToSpec =
        ((offsetValues offsets.val).zip (offsetValues spans.val)).map
          (fun (start, span) => (bytesToSpec input.val).extract start (start + span)) := by
  obtain ⟨sized, safe⟩ := offset_spans_bounds read
  constructor
  · intro range member
    change range.start.val ≤ range.end.val ∧ range.end.val ≤ input.val.length
    have mapped : (range.start.val, range.end.val) ∈
        bodyBounds (offsetValues offsets.val) (offsetValues spans.val) := by
      rw [← data]
      exact List.mem_map.mpr ⟨range, member, rfl⟩
    obtain ⟨position, inside, same⟩ := List.mem_iff_getElem.mp mapped
    have left : position < offsets.val.length := by
      simpa only [bodyBounds_length _ _ sized, offsetValues_length] using inside
    have lengths : spans.val.length = offsets.val.length := by simpa using sized
    have right : position < spans.val.length := by omega
    rw [bodyBounds_at _ _ _ left right] at same
    have bound : offsets.val[position].val + spans.val[position].val ≤ input.val.length := by
      simpa [offsetValues, left, right] using safe position (by simpa using left)
    have first := congrArg Prod.fst same
    have last := congrArg Prod.snd same
    exact ⟨by omega, by omega⟩
  · have mapped := congrArg
      (List.map fun (start, stop) => (bytesToSpec input.val).extract start stop) data
    simpa [sequenceElements, rangeValues, bodyBounds, List.map_map,
      Function.comp_def, bytesToSpec_slice] using mapped

end NyxSszVerification
