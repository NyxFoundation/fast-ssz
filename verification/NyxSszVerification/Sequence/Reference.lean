import NyxSszVerification.Sequence.Model
import NyxSszVerification.Collections
import NyxSszVerification.Codec.Adapter

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace NyxSszVerification

@[simp] theorem offsetValues_length (values : List Usize) :
    (offsetValues values).length = values.length := by simp [offsetValues]

theorem bytesToSpec_slice (values : List U8) (start stop : Nat) :
    bytesToSpec (values.slice start stop) = (bytesToSpec values).extract start stop := by
  apply _root_.Array.toList_inj.mp
  simp [bytesToSpec, List.slice, List.extract_eq_take_drop, List.map_take, List.map_drop]

/-- The upstream CanonicalTable proof, isolated from incompatible proof-module imports. -/
theorem sequence_read_uint_extract (data : Ssz.Bytes) (start stop : Nat) :
    ∀ offset width, offset + width ≤ stop - start → stop ≤ data.size →
      Ssz.readUint (data.extract start stop) offset width =
        Ssz.readUint data (start + offset) width := by
  intro offset width
  induction width generalizing offset with
  | zero => intros; rfl
  | succ width ih =>
    intro room bounded
    have inside : offset < (data.extract start stop).size := by simp; omega
    have source : start + offset < data.size := by omega
    simp only [Ssz.readUint, _root_.Array.getElem?_eq_getElem inside,
      _root_.Array.getElem?_eq_getElem source, Option.getD_some, _root_.Array.getElem_extract]
    rw [ih (offset + 1) (by omega) bounded]
    congr 2

@[simp] theorem read_offsets_length (data : Ssz.Bytes) (count : Nat) :
    (Ssz.readOffsets data count).length = count := by simp [Ssz.readOffsets]

theorem read_offsets_succ (data : Ssz.Bytes) (count : Nat) :
    Ssz.readOffsets data (count + 1) = Ssz.readOffsets data count ++
      [Ssz.readUint data (count * 4) 4] := by
  simp [Ssz.readOffsets, List.range_succ, Ssz.bytesPerOffset]

@[step] theorem decode_offset_refines (input : Slice U8) (width : input.val.length = 4) :
    NyxSszRust.scalar.decode_u32 input ⦃ actual =>
      ∃ value, actual = .Ok value ∧ value.val = Ssz.readUint (bytesToSpec input.val) 0 4 ⦄ := by
  apply spec_mono (decode_u32_refines input)
  intro actual agrees
  have model : Ssz.deserialize (.uint 4) (bytesToSpec input.val) =
      .ok (.uint (Ssz.readUint (bytesToSpec input.val) 0 4)) := by
    simp [deserialize_uint_form, width]
  rw [model] at agrees
  cases actual with
  | Ok value => exact ⟨value, rfl, agrees⟩
  | Err error => cases error <;> simp [uintResultAgrees] at agrees

theorem parsed_offsets_length {values : alloc.vec.Vec Usize} {data : Ssz.Bytes} {count : Nat}
    (parsed : offsetValues values.val = Ssz.readOffsets data count) : values.val.length = count := by
  have same := congrArg List.length parsed
  simpa using same

theorem offsetValues_first (values : List Usize) (nonempty : 0 < values.length) :
    (offsetValues values)[0]! = values[0].val := by simp [offsetValues, nonempty]

theorem variable_vector_slices_form (element : Ssz.Desc) (isVariable : element.fixedSize = none)
    (data : Ssz.Bytes) (count : Nat) (offsets : List Nat)
    (envelope : data.size < 4294967296) (budget : count * 4 ≤ data.size)
    (nonzero : count ≠ 0) (parsed : offsets = Ssz.readOffsets data count) :
    Ssz.vectorSlices element count data =
      if offsets[0]! ≠ count * 4 then .error (.firstOffset (count * 4) offsets[0]!)
      else (Ssz.offsetSpans offsets data.size).map fun spans =>
        (offsets.zip spans).map fun (start, span) => data.extract start (start + span) := by
  have notHuge : ¬4294967296 ≤ data.size := by omega
  have notShort : ¬data.size < count * 4 := by omega
  subst offsets
  cases read : Ssz.offsetSpans (Ssz.readOffsets data count) data.size <;>
    simp [Ssz.vectorSlices, isVariable, Ssz.bytesPerOffset, notHuge, notShort,
      nonzero, read, Except.map, Bind.bind, Except.bind, pure, Except.pure]

end NyxSszVerification
