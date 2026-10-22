import NyxSszVerification.Collections

open Aeneas Aeneas.Std

namespace NyxSszVerification

/-- Every bound, including zero and the maximum machine value, preserves storage. -/
theorem bounded_progressive_list_storage_refines {T : Type} (capacity : Usize) (input : alloc.vec.Vec T) :
    ∃ result,
      NyxSszRust.collections.bounded_progressive_list capacity input = RustM.ok result ∧
      match result with
      | .Ok value => value.values = input ∧ input.val.length ≤ capacity.val
      | .Err error => error.values = input ∧ error.kind = .OverLimit ∧
          input.val.length > capacity.val := by
  by_cases over : Slice.len (alloc.vec.Vec.deref input) > capacity
  · have overVal : input.val.length > capacity.val := by scalar_tac
    refine ⟨.Err ⟨.OverLimit, input⟩, ?_, ?_⟩ <;>
      simp [NyxSszRust.collections.bounded_progressive_list, NyxSszRust.collections.BoundedProgressiveList.as_slice, overVal]
  · have within : input.val.length ≤ capacity.val := by scalar_tac
    refine ⟨.Ok ⟨input, Array.repeat capacity ()⟩, ?_, ?_⟩ <;>
      simp [NyxSszRust.collections.bounded_progressive_list, NyxSszRust.collections.BoundedProgressiveList.as_slice, within]

/-- Immutable storage exposes every owner in its original order. -/
theorem bounded_progressive_list_as_slice_refines {T : Type} {capacity : Usize}
    (value : NyxSszRust.collections.BoundedProgressiveList T capacity) :
    ∃ result, NyxSszRust.collections.BoundedProgressiveList.as_slice value = RustM.ok result ∧
      result.val = value.values.val := by
  exact ⟨alloc.vec.Vec.deref value.values, rfl, rfl⟩

end NyxSszVerification
