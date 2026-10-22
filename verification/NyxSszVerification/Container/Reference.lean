import NyxSszVerification.Container.Finish

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace NyxSszVerification

theorem fields_fixed_form (fields : List Ssz.Desc) :
    Ssz.Desc.fieldsFixedSize fields =
      if variableFields fields then none else some (Ssz.Desc.leadingWidth fields) := by
  induction fields with
  | nil => rfl
  | cons field fields ih =>
    cases fixed : field.fixedSize <;> cases tailFixed : variableFields fields <;>
      simp [Ssz.Desc.fieldsFixedSize, Ssz.Desc.leadingWidth, fixed, ih, tailFixed]

theorem struct_budget_form (fields : List Ssz.Desc) (scope : Nat) :
    Ssz.structBudget fields scope =
      if variableFields fields then
        if scope < Ssz.Desc.leadingWidth fields then
          .error (.scopeTooSmall (Ssz.Desc.leadingWidth fields) scope) else .ok ()
      else if scope ≠ Ssz.Desc.leadingWidth fields then
        .error (.scope (Ssz.Desc.leadingWidth fields) scope) else .ok () := by
  cases chosen : variableFields fields <;> simp [Ssz.structBudget, fields_fixed_form, chosen]

/-- The pinned specification calls the Container layout helper `structSlices`. -/
theorem struct_slices_ready (fields : List Ssz.Desc) (data : Ssz.Bytes)
    (envelope : data.size < 4294967296)
    (budget : Ssz.structBudget fields data.size = .ok ())
    (room : Ssz.Desc.leadingWidth fields ≤ data.size) :
    Ssz.structSlices fields data =
      if (frontOffsets fields data 0).isEmpty then
        if data.size ≠ Ssz.Desc.leadingWidth fields then
          .error (.scope (Ssz.Desc.leadingWidth fields) data.size)
        else .ok ((frontSlots fields data 0).map Ssz.Slot.held)
      else if (frontOffsets fields data 0)[0]! ≠ Ssz.Desc.leadingWidth fields then
        .error (.firstOffset (Ssz.Desc.leadingWidth fields) (frontOffsets fields data 0)[0]!)
      else (Ssz.offsetSpans (frontOffsets fields data 0) data.size).bind fun spans =>
        Ssz.takeSlots data (frontSlots fields data 0) spans := by
  simp [Ssz.structSlices, Ssz.bytesPerOffset, show ¬data.size ≥ 4294967296 by omega,
    budget, readSlots_front fields data 0 (by simpa using room),
    Bind.bind, Except.bind, Pure.pure, Except.pure, ne_eq]

theorem frontOffsets_empty (fields : List Ssz.Desc) (data : Ssz.Bytes) (position : Nat) :
    (frontOffsets fields data position).isEmpty = !variableFields fields := by
  induction fields generalizing position with
  | nil => rfl
  | cons field fields ih =>
    cases fixed : field.fixedSize <;> simp [frontOffsets, fixed, ih]

theorem inline_front_bounds (fields : List Ssz.Desc) (data : Ssz.Bytes) (position : Nat)
    (fixed : variableFields fields = false) :
    containerBounds fields data position [] = frontRanges fields data position ∧
      (frontSlots fields data position).map Ssz.Slot.held =
        (frontRanges fields data position).map fun (start, stop) => data.extract start stop := by
  induction fields generalizing position with
  | nil => simp [containerBounds, frontRanges, frontSlots]
  | cons field fields ih =>
    cases width : field.fixedSize <;> simp_all [containerBounds, frontRanges, frontSlots, Ssz.Slot.held]

theorem container_view_from_bounds (input : Slice U8) (fields : List Ssz.Desc)
    (spans : List Nat) (ranges : alloc.vec.Vec NyxSszRust.sequence.BodyRange)
    (room : Ssz.Desc.leadingWidth fields ≤ input.val.length)
    (read : Ssz.offsetSpans (frontOffsets fields (bytesToSpec input.val) 0) input.val.length = .ok spans)
    (data : rangeValues ranges.val = containerBounds fields (bytesToSpec input.val) 0 spans) :
    sequenceViewValid ⟨input, ranges⟩ ∧
      (sequenceElements ⟨input, ranges⟩).map bytesToSpec =
        (containerBounds fields (bytesToSpec input.val) 0 spans).map fun (start, stop) =>
          (bytesToSpec input.val).extract start stop := by
  constructor
  · intro range member
    have mapped : (range.start.val, range.end.val) ∈
        containerBounds fields (bytesToSpec input.val) 0 spans := by
      rw [← data]
      exact List.mem_map.mpr ⟨range, member, rfl⟩
    simpa using container_bounds_valid fields (bytesToSpec input.val) 0 spans
      (by simpa using room) (by simpa using read) _ mapped
  · have mapped := congrArg
      (List.map fun (start, stop) => (bytesToSpec input.val).extract start stop) data
    simpa [sequenceElements, rangeValues, List.map_map, Function.comp_def, bytesToSpec_slice] using mapped

theorem inline_container_view (input : Slice U8) (fields : List Ssz.Desc)
    (ranges : alloc.vec.Vec NyxSszRust.sequence.BodyRange)
    (budget : Ssz.structBudget fields input.val.length = .ok ())
    (room : Ssz.Desc.leadingWidth fields ≤ input.val.length)
    (raw : rangeValues ranges.val = frontRanges fields (bytesToSpec input.val) 0)
    (empty : frontOffsets fields (bytesToSpec input.val) 0 = []) :
    sequenceViewValid ⟨input, ranges⟩ ∧
      (sequenceElements ⟨input, ranges⟩).map bytesToSpec =
        (frontSlots fields (bytesToSpec input.val) 0).map Ssz.Slot.held ∧
      input.val.length = Ssz.Desc.leadingWidth fields := by
  have fixed : variableFields fields = false := by
    have equation := frontOffsets_empty fields (bytesToSpec input.val) 0
    rw [empty] at equation
    simpa using equation.symm
  have exactScope : input.val.length = Ssz.Desc.leadingWidth fields := by
    by_contra different
    simp [struct_budget_form, fixed, different] at budget
  have inlineBounds := inline_front_bounds fields (bytesToSpec input.val) 0 fixed
  have bridge := container_view_from_bounds input fields [] ranges room
    (by simp [empty, Ssz.offsetSpans]) (raw.trans inlineBounds.1.symm)
  exact ⟨bridge.1, bridge.2.trans (by rw [inlineBounds.1, inlineBounds.2]), exactScope⟩

theorem struct_slices_with_offsets (fields : List Ssz.Desc) (data : Ssz.Bytes)
    (offsets : List Usize) (envelope : data.size < 4294967296)
    (budget : Ssz.structBudget fields data.size = .ok ())
    (room : Ssz.Desc.leadingWidth fields ≤ data.size) (nonempty : 0 < offsets.length)
    (parsed : offsetValues offsets = frontOffsets fields data 0) :
    Ssz.structSlices fields data =
      if offsets[0].val ≠ Ssz.Desc.leadingWidth fields then
        .error (.firstOffset (Ssz.Desc.leadingWidth fields) offsets[0].val)
      else (Ssz.offsetSpans (offsetValues offsets) data.size).bind fun spans =>
        Ssz.takeSlots data (frontSlots fields data 0) spans := by
  rw [struct_slices_ready fields data envelope budget room, ← parsed]
  have notEmpty : (offsetValues offsets).isEmpty = false := by
    simp only [List.isEmpty_eq_false_iff, ← List.length_pos_iff, offsetValues_length]
    exact nonempty
  simp only [notEmpty, Bool.false_eq_true, if_false, offsetValues_first offsets nonempty]

end NyxSszVerification
