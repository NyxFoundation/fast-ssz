import NyxSszVerification.Sequence.Read
import NyxSszVerification.Sequence.Validated
import NyxSszVerification.ProgressiveBits.View

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace NyxSszVerification

def sequenceViewAgrees
    (actual : core.result.Result NyxSszRust.sequence.SequenceView NyxSszRust.error.CodecError)
    (expected : Except Ssz.Err (List Ssz.Bytes)) : Prop :=
  match actual, expected with
  | .Ok view, .ok parts => sequenceViewValid view ∧ (sequenceElements view).map bytesToSpec = parts
  | .Err error, .error fault => codecFaultAgrees error fault
  | _, _ => False

theorem variable_vector_view_refines (input : Slice U8) (count : Usize)
    (element : Ssz.Desc) (isVariable : element.fixedSize = none) :
    NyxSszRust.sequence.variable_vector_view input count ⦃ actual =>
      sequenceViewAgrees actual (Ssz.vectorSlices element count.val (bytesToSpec input.val)) ⦄ := by
  have inputBound := input.property
  unfold NyxSszRust.sequence.variable_vector_view
  step*
  all_goals simp_all [spanOutcome]
  · have huge : 4294967296 ≤ input.val.length := by scalar_tac
    simp [Ssz.vectorSlices, Ssz.bytesPerOffset, huge, sequenceViewAgrees, codecFaultAgrees,
      Bind.bind, Except.bind]
  · have notHuge : ¬4294967296 ≤ input.val.length := by scalar_tac
    have short : input.val.length < count.val * 4 := by scalar_tac
    simp [Ssz.vectorSlices, Ssz.bytesPerOffset, isVariable, notHuge, short,
      sequenceViewAgrees, codecFaultAgrees, Bind.bind, Except.bind, pure, Except.pure]
  · have notHuge : ¬4294967296 ≤ input.val.length := by scalar_tac
    simp [Ssz.vectorSlices, Ssz.bytesPerOffset, isVariable, notHuge,
      sequenceViewAgrees, sequenceViewValid, sequenceElements,
      Bind.bind, Except.bind, pure, Except.pure]
  · have parsed : offsetValues offsets.val = Ssz.readOffsets (bytesToSpec input.val) count.val := by
      simpa only [‹r = .Ok offsets›] using r_post
    have size := parsed_offsets_length parsed
    scalar_tac
  · have parsed : offsetValues offsets.val = Ssz.readOffsets (bytesToSpec input.val) count.val := by
      simpa only [‹r = .Ok offsets›] using r_post
    have size := parsed_offsets_length parsed
    have positive : 0 < offsets.val.length := by scalar_tac
    have different : (offsetValues offsets.val)[0]! ≠ count.val * 4 := by
      rw [offsetValues_first _ positive]
      scalar_tac
    rw [variable_vector_slices_form element isVariable _ _ _
      (by simp only [bytesToSpec_size]; scalar_tac)
      (by simp only [bytesToSpec_size]; scalar_tac) (by scalar_tac) parsed, if_pos different]
    trivial
  · have parsed : offsetValues offsets.val = Ssz.readOffsets (bytesToSpec input.val) count.val := by
      simpa only [‹r = .Ok offsets›] using r_post
    have size := parsed_offsets_length parsed
    have positive : 0 < offsets.val.length := by scalar_tac
    have first : (offsetValues offsets.val)[0]! = count.val * 4 := by
      rw [offsetValues_first _ positive]
      scalar_tac
    have bridge := sequence_view_from_ranges input offsets spans v r1_post.1 v_post
    rw [variable_vector_slices_form element isVariable _ _ _
      (by simp only [bytesToSpec_size]; scalar_tac)
      (by simp only [bytesToSpec_size]; scalar_tac) (by scalar_tac) parsed,
      if_neg (fun different => different first), bytesToSpec_size, r1_post.1]
    simpa only [Except.map, sequenceViewAgrees] using bridge
  · have parsed : offsetValues offsets.val = Ssz.readOffsets (bytesToSpec input.val) count.val := by
      simpa only [‹r = .Ok offsets›] using r_post
    have size := parsed_offsets_length parsed
    have positive : 0 < offsets.val.length := by scalar_tac
    have first : (offsetValues offsets.val)[0]! = count.val * 4 := by
      rw [offsetValues_first _ positive]
      scalar_tac
    obtain ⟨fault, read, agrees⟩ := r1_post
    rw [variable_vector_slices_form element isVariable _ _ _
      (by simp only [bytesToSpec_size]; scalar_tac)
      (by simp only [bytesToSpec_size]; scalar_tac) (by scalar_tac) parsed,
      if_neg (fun different => different first), bytesToSpec_size, read]
    simpa only [Except.map, sequenceViewAgrees] using agrees

end NyxSszVerification
