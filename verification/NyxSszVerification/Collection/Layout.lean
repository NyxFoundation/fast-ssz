import NyxSszVerification.Collection.Metadata
import NyxSszVerification.Sequence.Vector
import NyxSszVerification.Sequence.List
import NyxSszVerification.Sequence.FixedList

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxHeartbeats 2000000

namespace NyxSszVerification

/-- Even metadata wider than a machine word is compared against the natural-number budget. -/
@[step] theorem collection_vector_layout_refines {T State : Type}
    (child : NyxSszRust.codec.Ssz T State) (shape : Ssz.Desc)
    (declared : child.TYPE ⦃ actual => typeDescriptorToSpec actual = shape ⦄)
    (input : Slice U8) (count : Usize) (positive : 0 < count.val) :
    NyxSszRust.collection_codec.vector_layout child input count ⦃ actual =>
      sequenceViewAgrees actual (Ssz.vectorSlices shape count.val (bytesToSpec input.val)) ⦄ := by
  unfold NyxSszRust.collection_codec.vector_layout
  apply spec_bind (codec_fixed_size_refines child shape declared)
  intro actual agrees
  cases expected : shape.fixedSize with
  | none =>
    have same := codec_width_none actual (by simpa only [expected] using agrees)
    rw [same]
    exact variable_vector_view_refines input count shape expected
  | some width =>
    cases actual with
    | Ok childWidth =>
      cases childWidth with
      | none => simp [expected, codecWidthAgrees] at agrees
      | some held =>
        have same : held.val = width := by simpa [expected, codecWidthAgrees] using agrees
        exact fixed_vector_view_refines input held count shape (by simpa only [same] using expected)
    | Err kind =>
      cases kind <;> simp only [expected, codecWidthAgrees] at agrees
      have scopeBound := input.property
      have product : Usize.max < width * count.val := by
        have growth := Nat.mul_le_mul_left width positive
        simp only [Nat.mul_one] at growth
        omega
      step*
      · have huge : 4294967296 ≤ input.val.length := by scalar_tac
        simp [Ssz.vectorSlices, Ssz.bytesPerOffset, huge, sequenceViewAgrees,
          codecFaultAgrees, Bind.bind, Except.bind, MonadExcept.throw, throwThe,
          MonadExceptOf.throw]
      · have notHuge : ¬4294967296 ≤ input.val.length := by scalar_tac
        have mismatch : input.val.length ≠ width * count.val := by omega
        simp [Ssz.vectorSlices, Ssz.bytesPerOffset, expected, notHuge, mismatch,
          sequenceViewAgrees, codecFaultAgrees, Bind.bind, Except.bind, Pure.pure, Except.pure,
          MonadExcept.throw, throwThe, MonadExceptOf.throw]

@[step] theorem collection_list_layout_refines {T State : Type}
    (child : NyxSszRust.codec.Ssz T State) (shape : Ssz.Desc)
    (declared : child.TYPE ⦃ actual => typeDescriptorToSpec actual = shape ⦄)
    (input : Slice U8) (limit : Usize) :
    NyxSszRust.collection_codec.list_layout child input limit ⦃ actual =>
      sequenceViewAgrees actual (Ssz.listSlices shape (some limit.val) (bytesToSpec input.val)) ⦄ := by
  unfold NyxSszRust.collection_codec.list_layout
  apply spec_bind (codec_fixed_size_refines child shape declared)
  intro actual agrees
  cases expected : shape.fixedSize with
  | none =>
    have same := codec_width_none actual (by simpa only [expected] using agrees)
    rw [same]
    exact variable_list_view_refines input (some limit) shape expected
  | some width =>
    cases actual with
    | Ok childWidth =>
      cases childWidth with
      | none => simp [expected, codecWidthAgrees] at agrees
      | some held =>
        have same : held.val = width := by simpa [expected, codecWidthAgrees] using agrees
        exact fixed_list_view_refines input held (some limit) shape (by simpa only [same] using expected)
    | Err kind =>
      cases kind <;> simp only [expected, codecWidthAgrees] at agrees
      have scopeBound := input.property
      have less : input.val.length < width := by omega
      have positive : width ≠ 0 := by omega
      have remainder : input.val.length % width = input.val.length := Nat.mod_eq_of_lt less
      step*
      · have huge : 4294967296 ≤ input.val.length := by scalar_tac
        simp [Ssz.listSlices, Ssz.bytesPerOffset, huge, sequenceViewAgrees,
          codecFaultAgrees, Bind.bind, Except.bind, MonadExcept.throw, throwThe,
          MonadExceptOf.throw]
      · have empty : input.val.length = 0 := by scalar_tac
        simp [Ssz.listSlices, Ssz.bytesPerOffset, empty, sequenceViewAgrees,
          sequenceViewValid, sequenceElements, Bind.bind, Except.bind, Pure.pure, Except.pure]
      · have notHuge : ¬4294967296 ≤ input.val.length := by scalar_tac
        have nonempty : input.val.length ≠ 0 := by scalar_tac
        simp [Ssz.listSlices, Ssz.bytesPerOffset, expected, notHuge, nonempty, positive,
          remainder, sequenceViewAgrees, codecFaultAgrees, Bind.bind, Except.bind,
          Pure.pure, Except.pure, MonadExcept.throw, throwThe, MonadExceptOf.throw]

end NyxSszVerification
