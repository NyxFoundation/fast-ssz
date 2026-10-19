import NyxSszVerification.Sequence.Model

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace NyxSszVerification

def sequenceViewValid (view : NyxSszRust.sequence.SequenceView) : Prop :=
  ∀ range ∈ view.ranges.val,
    range.start.val ≤ range.end.val ∧ range.end.val ≤ view.input.val.length

def sequenceElements (view : NyxSszRust.sequence.SequenceView) : List (List U8) :=
  view.ranges.val.map fun range => view.input.val.slice range.start.val range.end.val

@[step] theorem sequence_view_len_refines (view : NyxSszRust.sequence.SequenceView) :
    NyxSszRust.sequence.SequenceView.len view ⦃ count =>
      count.val = (sequenceElements view).length ⦄ := by
  simp [NyxSszRust.sequence.SequenceView.len, sequenceElements]

@[step] theorem sequence_view_is_empty_refines (view : NyxSszRust.sequence.SequenceView) :
    NyxSszRust.sequence.SequenceView.is_empty view ⦃ empty =>
      empty = decide ((sequenceElements view).length = 0) ⦄ := by
  unfold NyxSszRust.sequence.SequenceView.is_empty
  step*

/-- Every successful projection preserves the original borrowed bytes and order. -/
@[step] theorem sequence_view_get_refines (view : NyxSszRust.sequence.SequenceView)
    (index : Usize) (valid : sequenceViewValid view) :
    NyxSszRust.sequence.SequenceView.get view index ⦃ actual =>
      actual.map (fun bytes => bytes.val) = (sequenceElements view)[index.val]? ⦄ := by
  by_cases inside : index.val < view.ranges.val.length
  · have safety := valid _ (List.getElem_mem inside)
    unfold NyxSszRust.sequence.SequenceView.get
    step*
    all_goals simp_all [sequenceElements]
  · unfold NyxSszRust.sequence.SequenceView.get
    step*
    all_goals simp_all [sequenceElements]

end NyxSszVerification
