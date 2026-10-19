import NyxSszVerification.Sequence
import NyxSszVerification.Sequence.Ranges

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace NyxSszVerification

def spanOutcome (offsets : Slice Usize) (scope : Usize)
    (actual : core.result.Result (alloc.vec.Vec Usize) NyxSszRust.error.CodecError) : Prop :=
  match actual with
  | .Ok spans =>
    Ssz.offsetSpans (offsetValues offsets.val) scope.val = .ok (offsetValues spans.val) ∧
    spans.val.length = offsets.val.length ∧
    ∀ position (left : position < offsets.val.length) (right : position < spans.val.length),
      offsets.val[position].val + spans.val[position].val ≤ Usize.max
  | .Err error => ∃ fault,
    Ssz.offsetSpans (offsetValues offsets.val) scope.val = .error fault ∧ codecFaultAgrees error fault

@[step] theorem offset_spans_checked (offsets : Slice Usize) (scope : Usize) :
    NyxSszRust.sequence.offset_spans offsets scope ⦃ actual => spanOutcome offsets scope actual ⦄ := by
  apply spec_mono (offset_spans_refines offsets scope)
  intro actual agrees
  cases actual with
  | Ok spans =>
    have equation : Ssz.offsetSpans (offsetValues offsets.val) scope.val =
        .ok (offsetValues spans.val) := by
      cases model : Ssz.offsetSpans (offsetValues offsets.val) scope.val <;>
        simp_all [offsetSpansAgree]
    obtain ⟨sized, safe⟩ := offset_spans_bounds equation
    refine ⟨equation, by simpa using sized, ?_⟩
    intro position left right
    have bound : offsets.val[position].val + spans.val[position].val ≤ scope.val := by
      simpa [offsetValues, left, right] using safe position (by simpa using left)
    scalar_tac
  | Err error =>
    cases model : Ssz.offsetSpans (offsetValues offsets.val) scope.val with
    | ok values => simp [offsetSpansAgree, model] at agrees
    | error fault => exact ⟨fault, model, by simpa [offsetSpansAgree, model] using agrees⟩

end NyxSszVerification
