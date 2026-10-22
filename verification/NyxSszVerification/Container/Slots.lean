import NyxSszVerification.Container.Budget
import NyxSszVerification.Sequence.Read

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace NyxSszVerification

def frontRanges : List Ssz.Desc → Ssz.Bytes → Nat → List (Nat × Nat)
  | [], _, _ => []
  | field :: fields, data, position =>
    match field.fixedSize with
    | some width => (position, position + width) :: frontRanges fields data (position + width)
    | none =>
      let start := Ssz.readUint data position 4
      (start, start) :: frontRanges fields data (position + 4)

def frontOffsets : List Ssz.Desc → Ssz.Bytes → Nat → List Nat
  | [], _, _ => []
  | field :: fields, data, position =>
    match field.fixedSize with
    | some width => frontOffsets fields data (position + width)
    | none => Ssz.readUint data position 4 :: frontOffsets fields data (position + 4)

def frontSlots : List Ssz.Desc → Ssz.Bytes → Nat → List Ssz.Slot
  | [], _, _ => []
  | field :: fields, data, position =>
    match field.fixedSize with
    | some width => .inline (data.extract position (position + width)) ::
      frontSlots fields data (position + width)
    | none => .body (Ssz.readUint data position 4) :: frontSlots fields data (position + 4)

@[simp] theorem frontRanges_length (fields : List Ssz.Desc) (data : Ssz.Bytes) (position : Nat) :
    (frontRanges fields data position).length = fields.length := by
  induction fields generalizing position with
  | nil => rfl
  | cons field fields ih => cases fixed : field.fixedSize <;> simp [frontRanges, fixed, ih]

theorem readSlots_front (fields : List Ssz.Desc) (data : Ssz.Bytes) (position : Nat)
    (budget : position + Ssz.Desc.leadingWidth fields ≤ data.size) :
    Ssz.readSlots fields data position =
      .ok (frontSlots fields data position, position + Ssz.Desc.leadingWidth fields) := by
  induction fields generalizing position with
  | nil => simp [Ssz.readSlots, frontSlots, Ssz.Desc.leadingWidth]
  | cons field fields ih =>
    cases fixed : field.fixedSize with
    | none =>
      simp only [Ssz.Desc.leadingWidth, fixed, Option.getD_none, Ssz.bytesPerOffset] at budget ⊢
      simp [Ssz.readSlots, frontSlots, fixed, Ssz.bytesPerOffset,
        show ¬position + 4 > data.size by omega,
        ih (position + 4) (by omega), Bind.bind, Except.bind, Pure.pure, Except.pure, Nat.add_assoc]
    | some width =>
      simp only [Ssz.Desc.leadingWidth, fixed, Option.getD_some] at budget ⊢
      simp [Ssz.readSlots, frontSlots, fixed, show ¬position + width > data.size by omega,
        ih (position + width) (by omega), Bind.bind, Except.bind, Pure.pure, Except.pure, Nat.add_assoc]

@[simp] theorem bodyStarts_front (fields : List Ssz.Desc) (data : Ssz.Bytes) (position : Nat) :
    Ssz.bodyStarts (frontSlots fields data position) = frontOffsets fields data position := by
  induction fields generalizing position with
  | nil => rfl
  | cons field fields ih =>
    cases fixed : field.fixedSize <;> simp [frontSlots, frontOffsets, fixed, Ssz.bodyStarts, ih]

@[step] theorem read_slots_loop_refines
    (input : Slice U8) (widths : Slice WidthMetadata) (fields : List Ssz.Desc)
    (truth : containerMetadata widths.val fields)
    (budget : Ssz.Desc.leadingWidth fields ≤ input.val.length)
    (output : alloc.vec.Vec NyxSszRust.sequence.BodyRange) (held : alloc.vec.Vec Usize)
    (position index : Usize) (within : index.val ≤ widths.val.length)
    (offsetLength : held.val.length ≤ index.val)
    (positionData : position.val + Ssz.Desc.leadingWidth (fields.drop index.val) =
      Ssz.Desc.leadingWidth fields)
    (rangesData : rangeValues output.val ++
      frontRanges (fields.drop index.val) (bytesToSpec input.val) position.val =
        frontRanges fields (bytesToSpec input.val) 0)
    (offsetData : offsetValues held.val ++
      frontOffsets (fields.drop index.val) (bytesToSpec input.val) position.val =
        frontOffsets fields (bytesToSpec input.val) 0) :
    NyxSszRust.container.read_slots_loop input widths output held position index ⦃ actual =>
      match actual with
      | .Ok (ranges, offsets) =>
        rangeValues ranges.val = frontRanges fields (bytesToSpec input.val) 0 ∧
        offsetValues offsets.val = frontOffsets fields (bytesToSpec input.val) 0
      | .Err _ => False ⦄ := by
  have inputBound := input.property
  unfold NyxSszRust.container.read_slots_loop
  apply loop_total
    (invariant := fun state : alloc.vec.Vec NyxSszRust.sequence.BodyRange ×
        alloc.vec.Vec Usize × Usize × Usize =>
      state.2.2.2.val ≤ widths.val.length ∧ state.2.1.val.length ≤ state.2.2.2.val ∧
      state.2.2.1.val + Ssz.Desc.leadingWidth (fields.drop state.2.2.2.val) =
        Ssz.Desc.leadingWidth fields ∧
      rangeValues state.1.val ++ frontRanges (fields.drop state.2.2.2.val)
        (bytesToSpec input.val) state.2.2.1.val = frontRanges fields (bytesToSpec input.val) 0 ∧
      offsetValues state.2.1.val ++ frontOffsets (fields.drop state.2.2.2.val)
        (bytesToSpec input.val) state.2.2.1.val = frontOffsets fields (bytesToSpec input.val) 0)
    (measure := fun state => widths.val.length - state.2.2.2.val)
  · rintro ⟨ranges, offsets, nextPosition, nextIndex⟩ ⟨inside, heldLength, front, rangesEq, offsetsEq⟩
    dsimp only at inside heldLength front rangesEq offsetsEq ⊢
    have outputLength : ranges.val.length = nextIndex.val := by
      have sized := congrArg List.length rangesEq
      simp only [List.length_append, rangeValues_length, frontRanges_length,
        List.length_drop] at sized
      have := truth.1
      omega
    by_cases active : nextIndex.val < widths.val.length
    · have fieldInside : nextIndex.val < fields.length := by rw [← truth.1]; exact active
      have agrees := metadata_at widths.val fields truth nextIndex.val active
      rw [List.drop_eq_getElem_cons fieldInside] at front rangesEq offsetsEq
      cases fixed : fields[nextIndex.val].fixedSize
      all_goals simp only [Ssz.Desc.leadingWidth, frontRanges, frontOffsets, fixed,
        Option.getD_none, Option.getD_some, Ssz.bytesPerOffset] at front rangesEq offsetsEq
      all_goals unfold NyxSszRust.container.read_slots_loop.body
      all_goals step*
      all_goals subst_vars
      all_goals simp_all [codecWidthAgrees]
      all_goals try (cases error1 <;> simp_all <;> scalar_tac)
      all_goals try scalar_tac
      all_goals
        have read : Ssz.readUint
            (bytesToSpec (input.val.slice nextPosition.val (nextPosition.val + 4))) 0 4 =
              Ssz.readUint (bytesToSpec input.val) nextPosition.val 4 := by
          rw [bytesToSpec_slice, sequence_read_uint_extract _ _ _ 0 4
            (by omega) (by simp only [bytesToSpec_size]; omega), Nat.add_zero]
        simp only [read]
        exact ⟨by omega, rangesEq, offsetsEq, by omega⟩
    · have ending : nextIndex.val = fields.length := by have := truth.1; omega
      unfold NyxSszRust.container.read_slots_loop.body
      step*
      simpa [ending, frontRanges, frontOffsets] using And.intro rangesEq offsetsEq
  · exact ⟨within, offsetLength, positionData, rangesData, offsetData⟩

@[step] theorem read_slots_refines
    (input : Slice U8) (widths : Slice WidthMetadata) (fields : List Ssz.Desc)
    (truth : containerMetadata widths.val fields)
    (budget : Ssz.Desc.leadingWidth fields ≤ input.val.length) :
    NyxSszRust.container.read_slots input widths ⦃ actual =>
      match actual with
      | .Ok (ranges, offsets) =>
        rangeValues ranges.val = frontRanges fields (bytesToSpec input.val) 0 ∧
        offsetValues offsets.val = frontOffsets fields (bytesToSpec input.val) 0
      | .Err _ => False ⦄ := by
  unfold NyxSszRust.container.read_slots
  apply read_slots_loop_refines input widths fields truth budget
  all_goals simp [rangeValues, offsetValues]

end NyxSszVerification
