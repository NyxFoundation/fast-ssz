import NyxSszVerification.Container.Slots

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace NyxSszVerification

def containerBounds : List Ssz.Desc → Ssz.Bytes → Nat → List Nat → List (Nat × Nat)
  | [], _, _, _ => []
  | field :: fields, data, position, spans =>
    match field.fixedSize with
    | some width => (position, position + width) ::
      containerBounds fields data (position + width) spans
    | none =>
      let start := Ssz.readUint data position 4
      (start, start + spans.headD 0) :: containerBounds fields data (position + 4) spans.tail

theorem offset_spans_cons {start width : Nat} {offsets widths : List Nat} {scope : Nat}
    (read : Ssz.offsetSpans (start :: offsets) scope = .ok (width :: widths)) :
    Ssz.offsetSpans offsets scope = .ok widths ∧ start + width ≤ scope := by
  have safety := (offset_spans_bounds read).2 0 (by simp)
  constructor
  · cases offsets with
    | nil =>
      simp only [Ssz.offsetSpans] at read ⊢
      split at read <;> simp_all
    | cons next rest =>
      simp only [Ssz.offsetSpans] at read
      split at read
      · contradiction
      · cases result : Ssz.offsetSpans (next :: rest) scope <;>
          simp_all [Bind.bind, Except.bind, Pure.pure, Except.pure]
  · simpa using safety

theorem container_bounds_valid (fields : List Ssz.Desc) (data : Ssz.Bytes) (position : Nat)
    (spans : List Nat) (budget : position + Ssz.Desc.leadingWidth fields ≤ data.size)
    (read : Ssz.offsetSpans (frontOffsets fields data position) data.size = .ok spans) :
    ∀ range ∈ containerBounds fields data position spans,
      range.1 ≤ range.2 ∧ range.2 ≤ data.size := by
  induction fields generalizing position spans with
  | nil => simp [containerBounds]
  | cons field fields ih =>
    cases fixed : field.fixedSize with
    | some width =>
      simp only [frontOffsets, fixed] at read
      simp only [Ssz.Desc.leadingWidth, fixed, Option.getD_some] at budget
      simp only [containerBounds, fixed, List.mem_cons]
      intro range member
      rcases member with rfl | member
      · exact ⟨by omega, by omega⟩
      · exact ih _ _ (by omega) read range member
    | none =>
      simp only [frontOffsets, fixed] at read
      have sized := (offset_spans_bounds read).1
      cases spans with
      | nil => simp at sized
      | cons width spans =>
        obtain ⟨tailRead, safe⟩ := offset_spans_cons read
        simp only [Ssz.Desc.leadingWidth, fixed, Option.getD_none, Ssz.bytesPerOffset] at budget
        simp only [containerBounds, fixed, List.headD_cons, List.tail_cons, List.mem_cons]
        intro range member
        rcases member with rfl | member
        · exact ⟨by omega, safe⟩
        · exact ih _ _ (by omega) tailRead range member

theorem takeSlots_bounds (fields : List Ssz.Desc) (data : Ssz.Bytes) (position : Nat)
    (spans : List Nat)
    (read : Ssz.offsetSpans (frontOffsets fields data position) data.size = .ok spans) :
    Ssz.takeSlots data (frontSlots fields data position) spans =
      .ok ((containerBounds fields data position spans).map fun (start, stop) => data.extract start stop) := by
  induction fields generalizing position spans with
  | nil => simp [frontSlots, Ssz.takeSlots, containerBounds]
  | cons field fields ih =>
    cases fixed : field.fixedSize with
    | some width =>
      simp only [frontOffsets, fixed] at read
      simp [frontSlots, containerBounds, fixed, Ssz.takeSlots, ih _ _ read,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
    | none =>
      simp only [frontOffsets, fixed] at read
      have sized := (offset_spans_bounds read).1
      cases spans with
      | nil => simp at sized
      | cons width spans =>
        have tailRead := (offset_spans_cons read).1
        simp [frontSlots, containerBounds, fixed, Ssz.takeSlots, ih _ _ tailRead,
          Bind.bind, Except.bind, Pure.pure, Except.pure]

@[simp] theorem rangeValues_drop (ranges : List NyxSszRust.sequence.BodyRange) (index : Nat) :
    rangeValues (ranges.drop index) = (rangeValues ranges).drop index := by
  simp [rangeValues, List.map_drop]

end NyxSszVerification
