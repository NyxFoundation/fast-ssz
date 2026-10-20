import NyxSszVerification.Sequence.FixedRanges
import NyxSszVerification.Sequence.Vector

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace NyxSszVerification

theorem fixed_view_from_ranges (input : Slice U8) (width count : Nat)
    (ranges : alloc.vec.Vec NyxSszRust.sequence.BodyRange)
    (budget : input.val.length = width * count)
    (data : rangeValues ranges.val = fixedBounds width count) :
    sequenceViewValid ⟨input, ranges⟩ ∧
      (sequenceElements ⟨input, ranges⟩).map bytesToSpec =
        (List.range count).map (fun index =>
          (bytesToSpec input.val).extract (index * width) ((index + 1) * width)) := by
  constructor
  · intro range member
    have mapped : (range.start.val, range.end.val) ∈ fixedBounds width count := by
      rw [← data]
      exact List.mem_map.mpr ⟨range, member, rfl⟩
    obtain ⟨index, included, same⟩ := List.mem_map.mp mapped
    have inside : index < count := List.mem_range.mp included
    have startEq := congrArg Prod.fst same
    have endEq := congrArg Prod.snd same
    change index * width = range.start.val at startEq
    change (index + 1) * width = range.end.val at endEq
    change range.start.val ≤ range.end.val ∧ range.end.val ≤ input.val.length
    constructor
    · rw [← startEq, ← endEq]
      exact Nat.mul_le_mul_right width (Nat.le_succ index)
    · rw [← endEq, budget, Nat.mul_comm width count]
      exact Nat.mul_le_mul_right width (Nat.succ_le_iff.mpr inside)
  · have mapped := congrArg
      (List.map fun (start, stop) => (bytesToSpec input.val).extract start stop) data
    simpa [sequenceElements, rangeValues, fixedBounds, List.map_map,
      Function.comp_def, bytesToSpec_slice] using mapped

@[step] theorem fixed_vector_view_refines (input : Slice U8) (width count : Usize)
    (element : Ssz.Desc) (isFixed : element.fixedSize = some width.val) :
    NyxSszRust.sequence.fixed_vector_view input width count ⦃ actual =>
      sequenceViewAgrees actual (Ssz.vectorSlices element count.val (bytesToSpec input.val)) ⦄ := by
  have inputBound := input.property
  unfold NyxSszRust.sequence.fixed_vector_view
  step*
  · have huge : 4294967296 ≤ input.val.length := by scalar_tac
    simp [Ssz.vectorSlices, Ssz.bytesPerOffset, huge, sequenceViewAgrees, codecFaultAgrees,
      Bind.bind, Except.bind]
  · have notHuge : ¬4294967296 ≤ input.val.length := by scalar_tac
    have overflow : Usize.max < width.val * count.val := by simpa only [‹o = none›] using o_post
    have different : input.val.length ≠ width.val * count.val := by omega
    simp [Ssz.vectorSlices, Ssz.bytesPerOffset, isFixed, notHuge, different,
      sequenceViewAgrees, codecFaultAgrees, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · have notHuge : ¬4294967296 ≤ input.val.length := by scalar_tac
    have product := o_post
    simp only [‹o = some expected›] at product
    have different : input.val.length ≠ width.val * count.val := by scalar_tac
    simp [Ssz.vectorSlices, Ssz.bytesPerOffset, isFixed, notHuge, different,
      sequenceViewAgrees, codecFaultAgrees, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · have notHuge : ¬4294967296 ≤ input.val.length := by scalar_tac
    have product := o_post
    simp only [‹o = some expected›] at product
    have same : input.val.length = width.val * count.val := by scalar_tac
    have notHugeProduct : ¬4294967296 ≤ width.val * count.val := by omega
    have bridge := fixed_view_from_ranges input width.val count.val v same v_post
    simpa [Ssz.vectorSlices, Ssz.bytesPerOffset, isFixed, notHugeProduct, same,
      sequenceViewAgrees, Bind.bind, Except.bind, Pure.pure, Except.pure] using bridge

end NyxSszVerification
