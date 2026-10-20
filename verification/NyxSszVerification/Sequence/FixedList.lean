import NyxSszVerification.Sequence.FixedView

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace NyxSszVerification

theorem fixed_list_vector_slices (element : Ssz.Desc) (width : Nat)
    (isFixed : element.fixedSize = some width) (data : Ssz.Bytes) (limit : Option Nat)
    (nonempty : data.size ≠ 0) (positive : width ≠ 0) (divides : data.size % width = 0)
    (within : ∀ cap, limit = some cap → data.size / width ≤ cap) :
    Ssz.listSlices element limit data = Ssz.vectorSlices element (data.size / width) data := by
  have budget : width * (data.size / width) = data.size := by
    simpa only [Nat.mul_comm] using Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero divides)
  cases limit with
  | none =>
    simp [Ssz.listSlices, Ssz.vectorSlices, isFixed, nonempty, positive, divides, budget,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  | some capacity =>
    have bound := within capacity rfl
    simp [Ssz.listSlices, Ssz.vectorSlices, isFixed, nonempty, positive, divides, budget,
      Nat.not_lt.mpr bound, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem fixed_list_view_refines (input : Slice U8) (width : Usize) (limit : Option Usize)
    (element : Ssz.Desc) (isFixed : element.fixedSize = some width.val) :
    NyxSszRust.sequence.fixed_list_view input width limit ⦃ actual =>
      sequenceViewAgrees actual
        (Ssz.listSlices element (limit.map fun cap => cap.val) (bytesToSpec input.val)) ⦄ := by
  have inputBound := input.property
  unfold NyxSszRust.sequence.fixed_list_view
  step*
  all_goals try have notHuge : ¬4294967296 ≤ input.val.length := by scalar_tac
  all_goals try have nonempty : input.val.length ≠ 0 := by scalar_tac
  all_goals try have positive : width.val ≠ 0 := by scalar_tac
  all_goals try have divides : input.val.length % width.val = 0 := b1_post.mp ‹b1 = true›
  · have huge : 4294967296 ≤ input.val.length := by scalar_tac
    simp [Ssz.listSlices, Ssz.bytesPerOffset, huge, sequenceViewAgrees, codecFaultAgrees,
      Bind.bind, Except.bind]
  · have empty : input.val.length = 0 := by scalar_tac
    simp [Ssz.listSlices, Ssz.bytesPerOffset, empty, sequenceViewAgrees,
      sequenceViewValid, sequenceElements, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · have zero : width.val = 0 := by scalar_tac
    simp [Ssz.listSlices, Ssz.bytesPerOffset, isFixed, notHuge, nonempty, zero,
      sequenceViewAgrees, codecFaultAgrees, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · have countEq : count.val = input.val.length / width.val := by scalar_tac
    change sequenceViewAgrees actual (Ssz.listSlices element none (bytesToSpec input.val))
    rw [fixed_list_vector_slices element width.val isFixed _ _
      (by simpa only [bytesToSpec_size] using nonempty) positive
      (by simpa only [bytesToSpec_size] using divides)
      (by intro cap impossible; cases impossible), bytesToSpec_size, ← countEq]
    exact actual_post
  · have over : capacity.val < input.val.length / width.val := by scalar_tac
    simp [Ssz.listSlices, Ssz.bytesPerOffset, isFixed, notHuge, nonempty, positive, divides,
      over, sequenceViewAgrees, codecFaultAgrees, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · have countEq : count.val = input.val.length / width.val := by scalar_tac
    change sequenceViewAgrees actual (Ssz.listSlices element (some capacity.val) (bytesToSpec input.val))
    rw [fixed_list_vector_slices element width.val isFixed _ _
      (by simpa only [bytesToSpec_size] using nonempty) positive
      (by simpa only [bytesToSpec_size] using divides)
      (by intro cap same; cases same; simp only [bytesToSpec_size]; scalar_tac),
      bytesToSpec_size, ← countEq]
    exact actual_post
  · have undivided : input.val.length % width.val ≠ 0 := by
      intro bad
      exact ‹¬b1 = true› (b1_post.mpr bad)
    simp [Ssz.listSlices, Ssz.bytesPerOffset, isFixed, notHuge, nonempty, positive, undivided,
      sequenceViewAgrees, codecFaultAgrees, Bind.bind, Except.bind, Pure.pure, Except.pure]

end NyxSszVerification
