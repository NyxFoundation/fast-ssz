import NyxSszVerification.Sequence.ListReference

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace NyxSszVerification

theorem variable_list_view_refines (input : Slice U8) (limit : Option Usize)
    (element : Ssz.Desc) (isVariable : element.fixedSize = none) :
    NyxSszRust.sequence.variable_list_view input limit ⦃ actual =>
      sequenceViewAgrees actual
        (Ssz.listSlices element (limit.map fun cap => cap.val) (bytesToSpec input.val)) ⦄ := by
  have inputBound := input.property
  unfold NyxSszRust.sequence.variable_list_view
  step*
  all_goals try
    have same : first = r := by grind
    have firstRead : first1.val = Ssz.readUint (bytesToSpec input.val) 0 4 := by
      rw [first1_post, U32.cast_Usize_val_eq, same, r_post2, s_post1, bytesToSpec_slice,
        sequence_read_uint_extract _ _ _ _ _ (by decide)
          (by simp only [bytesToSpec_size]; scalar_tac)]
  all_goals try have notHuge : ¬4294967296 ≤ input.val.length := by scalar_tac
  all_goals try have nonempty : input.val.length ≠ 0 := by scalar_tac
  all_goals try have notShort : ¬input.val.length < 4 := by scalar_tac
  all_goals try have notBelow : ¬Ssz.readUint (bytesToSpec input.val) 0 4 < 4 := by scalar_tac
  all_goals try have notPast : ¬Ssz.readUint (bytesToSpec input.val) 0 4 > input.val.length := by scalar_tac
  all_goals try
    have aligned : Ssz.readUint (bytesToSpec input.val) 0 4 % 4 = 0 := by
      rw [← firstRead]
      exact b1_post.mp ‹b1 = true›
  · have huge : 4294967296 ≤ input.val.length := by scalar_tac
    simp [Ssz.listSlices, Ssz.bytesPerOffset, huge, sequenceViewAgrees, codecFaultAgrees,
      Bind.bind, Except.bind]
  · have empty : input.val.length = 0 := by scalar_tac
    simp [Ssz.listSlices, Ssz.bytesPerOffset, empty,
      sequenceViewAgrees, sequenceViewValid, sequenceElements,
      Bind.bind, Except.bind, pure, Except.pure]
  · have short : input.val.length < 4 := by scalar_tac
    simp [Ssz.listSlices, Ssz.bytesPerOffset, isVariable, notHuge, nonempty, short,
      sequenceViewAgrees, codecFaultAgrees, Bind.bind, Except.bind, pure, Except.pure]
  · have below : Ssz.readUint (bytesToSpec input.val) 0 4 < 4 := by scalar_tac
    simp [Ssz.listSlices, Ssz.bytesPerOffset, isVariable, notHuge, nonempty, notShort, below,
      sequenceViewAgrees, codecFaultAgrees, Bind.bind, Except.bind, pure, Except.pure]
  · have past : Ssz.readUint (bytesToSpec input.val) 0 4 > input.val.length := by scalar_tac
    simp [Ssz.listSlices, Ssz.bytesPerOffset, isVariable, notHuge, nonempty, notShort, notBelow,
      aligned, past, sequenceViewAgrees, codecFaultAgrees, Bind.bind, Except.bind, pure, Except.pure]
  · apply spec_mono (variable_vector_view_refines input count element isVariable)
    intro actual agrees
    have countEq : count.val = Ssz.readUint (bytesToSpec input.val) 0 4 / 4 := by scalar_tac
    change sequenceViewAgrees actual (Ssz.listSlices element none (bytesToSpec input.val))
    rw [variable_list_vector_slices element isVariable _ _
      (by simp only [bytesToSpec_size]; scalar_tac) (by scalar_tac) aligned
      (by simp only [bytesToSpec_size]; scalar_tac) (by intro cap impossible; cases impossible),
      ← countEq]
    exact agrees
  · have over : capacity.val < Ssz.readUint (bytesToSpec input.val) 0 4 / 4 := by scalar_tac
    simp [Ssz.listSlices, Ssz.bytesPerOffset, isVariable, notHuge, nonempty, notShort, notBelow,
      aligned, notPast, over, sequenceViewAgrees, codecFaultAgrees,
      Bind.bind, Except.bind, pure, Except.pure]
  · apply spec_mono (variable_vector_view_refines input count element isVariable)
    intro actual agrees
    have countEq : count.val = Ssz.readUint (bytesToSpec input.val) 0 4 / 4 := by scalar_tac
    change sequenceViewAgrees actual (Ssz.listSlices element (some capacity.val) (bytesToSpec input.val))
    rw [variable_list_vector_slices element isVariable _ _
      (by simp only [bytesToSpec_size]; scalar_tac) (by scalar_tac) aligned
      (by simp only [bytesToSpec_size]; scalar_tac)
      (by intro cap same; cases same; scalar_tac), ← countEq]
    exact agrees
  · have unaligned : Ssz.readUint (bytesToSpec input.val) 0 4 % 4 ≠ 0 := by
      intro bad
      have native : first1.val % 4 = 0 := by simpa only [firstRead] using bad
      exact ‹¬b1 = true› (b1_post.mpr native)
    simp [Ssz.listSlices, Ssz.bytesPerOffset, isVariable, notHuge, nonempty, notShort, notBelow,
      unaligned, sequenceViewAgrees, codecFaultAgrees, Bind.bind, Except.bind, pure, Except.pure]

end NyxSszVerification
