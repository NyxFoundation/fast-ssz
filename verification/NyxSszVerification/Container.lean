import NyxSszVerification.Container.Checked

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace NyxSszVerification

/-- Layout only: truthful metadata does not assert parent declaration or child value validity. -/
theorem container_view_refines (input : Slice U8) (widths : Slice WidthMetadata)
    (fields : List Ssz.Desc) (truth : containerMetadata widths.val fields) :
    NyxSszRust.container.container_view input widths ⦃ actual =>
      sequenceViewAgrees actual (Ssz.structSlices fields (bytesToSpec input.val)) ⦄ := by
  have inputBound := input.property
  unfold NyxSszRust.container.container_view
  step*
  · have huge : 4294967296 ≤ input.val.length := by scalar_tac
    simp [Ssz.structSlices, Ssz.bytesPerOffset, huge, sequenceViewAgrees, codecFaultAgrees,
      Bind.bind, Except.bind]
  all_goals subst_vars
  all_goals simp_all [containerHeaderOutcome]
  · rcases slots with ⟨ranges, offsets⟩
    dsimp only at r1_post ⊢
    have ready := struct_slices_ready fields (bytesToSpec input.val)
      (by simp only [bytesToSpec_size]; scalar_tac)
      (by simpa using r_post.2.2) (by simpa using r_post.2.1)
    step*
    · have empty : frontOffsets fields (bytesToSpec input.val) 0 = [] := by
        rw [← r1_post.2]
        simp_all [offsetValues]
      have bridge := inline_container_view input fields ranges r_post.2.2 r_post.2.1 r1_post.1 empty
      rw [ready, empty]
      simpa [sequenceViewAgrees, bridge.2.2] using And.intro bridge.1 bridge.2.1
    · have nonempty : 0 < offsets.val.length := List.length_pos_iff.mpr (by assumption)
      scalar_tac
    · have success : spanOutcome offsets.deref input.len (.Ok spans) := by
        simpa only [‹r2 = .Ok spans›] using r2_post
      have read : Ssz.offsetSpans (frontOffsets fields (bytesToSpec input.val) 0)
          input.val.length = .ok (offsetValues spans.val) := by
        rw [← r1_post.2]
        exact success.1
      apply spec_bind (finish_ranges_refines widths fields truth ranges.deref spans.deref
        (bytesToSpec input.val) input.len r1_post.1 read)
      intro output outputPost
      have bridge := container_view_from_bounds input fields (offsetValues spans.val) output
        r_post.2.1 read outputPost
      have nonempty : 0 < offsets.val.length := List.length_pos_iff.mpr (by assumption)
      have form := struct_slices_with_offsets fields (bytesToSpec input.val) offsets.val
        (by simp only [bytesToSpec_size]; scalar_tac) (by simpa using r_post.2.2)
        (by simpa using r_post.2.1) nonempty r1_post.2
      have first : offsets.val[0].val = Ssz.Desc.leadingWidth fields := by
        simpa only [i3_post] using ‹i3.val = Ssz.Desc.leadingWidth fields›
      have spanRead : Ssz.offsetSpans (offsetValues offsets.val) input.val.length =
          .ok (offsetValues spans.val) := success.1
      rw [form, if_neg (by omega), bytesToSpec_size, spanRead]
      simp only [Except.bind, takeSlots_bounds fields (bytesToSpec input.val) 0 _ (by simpa using read)]
      simpa only [spec_ok, sequenceViewAgrees] using bridge
    · have refused : spanOutcome offsets.deref input.len (.Err error1) := by
        simpa only [‹r2 = .Err error1›] using r2_post
      obtain ⟨fault, read, agrees⟩ := refused
      have nonempty : 0 < offsets.val.length := List.length_pos_iff.mpr (by assumption)
      have form := struct_slices_with_offsets fields (bytesToSpec input.val) offsets.val
        (by simp only [bytesToSpec_size]; scalar_tac) (by simpa using r_post.2.2)
        (by simpa using r_post.2.1) nonempty r1_post.2
      have first : offsets.val[0].val = Ssz.Desc.leadingWidth fields := by
        simpa only [i3_post] using ‹i3.val = Ssz.Desc.leadingWidth fields›
      change Ssz.offsetSpans (offsetValues offsets.val) input.val.length = .error fault at read
      rw [form, if_neg (by omega), bytesToSpec_size, read]
      exact agrees
    · have nonempty : 0 < offsets.val.length := List.length_pos_iff.mpr (by assumption)
      have form := struct_slices_with_offsets fields (bytesToSpec input.val) offsets.val
        (by simp only [bytesToSpec_size]; scalar_tac) (by simpa using r_post.2.2)
        (by simpa using r_post.2.1) nonempty r1_post.2
      have different : offsets.val[0].val ≠ Ssz.Desc.leadingWidth fields := by scalar_tac
      rw [form, if_pos different]
      trivial
  · obtain ⟨fault, budget, agrees⟩ := r_post
    have small : ¬4294967296 ≤ input.val.length := by scalar_tac
    simpa [Ssz.structSlices, Ssz.bytesPerOffset, small, budget,
      Bind.bind, Except.bind, Pure.pure, Except.pure, sequenceViewAgrees] using agrees

end NyxSszVerification
