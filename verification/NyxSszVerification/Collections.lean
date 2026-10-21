import NyxSszRust.Collections

open Aeneas Aeneas.Std

namespace NyxSszVerification

@[simp, scalar_tac_simps] theorem collection_deref_len {T : Type} (input : alloc.vec.Vec T) :
    Slice.len (alloc.vec.Vec.deref input) = alloc.vec.Vec.len input := rfl

@[simp, scalar_tac_simps] theorem collection_deref_values {T : Type} (input : alloc.vec.Vec T) :
    (alloc.vec.Vec.deref input).val = input.val := rfl

/-- Storage only: every generic element is returned unchanged on both outcomes. -/
theorem vector_storage_refines {T : Type} (count : Usize) (input : alloc.vec.Vec T) :
    ∃ result,
      NyxSszRust.collections.vector count input = RustM.ok result ∧
      match result with
      | .Ok value => count.val > 0 ∧ value.values = input ∧ input.val.length = count.val
      | .Err error => error.values = input ∧
          ((error.kind = .EmptyVector ∧ count.val = 0) ∨
           (error.kind = .InvalidLength ∧ count.val > 0 ∧ input.val.length ≠ count.val)) := by
  have zeroEq : (count = 0#usize) ↔ count.val = 0 := by scalar_tac
  have sizeEq : (Slice.len (alloc.vec.Vec.deref input) = count) ↔
      input.val.length = count.val := by scalar_tac
  refine ⟨if count = 0#usize then .Err ⟨.EmptyVector, input⟩
    else if Slice.len (alloc.vec.Vec.deref input) = count then .Ok ⟨input, Array.repeat count ()⟩
    else .Err ⟨.InvalidLength, input⟩, ?_, ?_⟩
  all_goals
    by_cases zero : count = 0#usize <;>
      by_cases same : Slice.len (alloc.vec.Vec.deref input) = count <;>
      simp_all [NyxSszRust.collections.vector, NyxSszRust.collections.Vector.as_slice,
        bne_iff_ne] <;> omega

/-- Every bound, including zero and the maximum machine value, preserves storage. -/
theorem list_storage_refines {T : Type} (capacity : Usize) (input : alloc.vec.Vec T) :
    ∃ result,
      NyxSszRust.collections.list capacity input = RustM.ok result ∧
      match result with
      | .Ok value => value.values = input ∧ input.val.length ≤ capacity.val
      | .Err error => error.values = input ∧ error.kind = .OverLimit ∧
          input.val.length > capacity.val := by
  by_cases over : Slice.len (alloc.vec.Vec.deref input) > capacity
  · have overVal : input.val.length > capacity.val := by scalar_tac
    refine ⟨.Err ⟨.OverLimit, input⟩, ?_, ?_⟩ <;>
      simp [NyxSszRust.collections.list, NyxSszRust.collections.List.as_slice, overVal]
  · have within : input.val.length ≤ capacity.val := by scalar_tac
    refine ⟨.Ok ⟨input, Array.repeat capacity ()⟩, ?_, ?_⟩ <;>
      simp [NyxSszRust.collections.list, NyxSszRust.collections.List.as_slice, within]

/-- The immutable projection exposes every element in its original order. -/
theorem vector_as_slice_refines {T : Type} {count : Usize}
    (value : NyxSszRust.collections.Vector T count) :
    ∃ result, NyxSszRust.collections.Vector.as_slice value = RustM.ok result ∧
      result.val = value.values.val := by
  exact ⟨alloc.vec.Vec.deref value.values, rfl, rfl⟩

/-- The immutable projection exposes every element in its original order. -/
theorem list_as_slice_refines {T : Type} {capacity : Usize}
    (value : NyxSszRust.collections.List T capacity) :
    ∃ result, NyxSszRust.collections.List.as_slice value = RustM.ok result ∧
      result.val = value.values.val := by
  exact ⟨alloc.vec.Vec.deref value.values, rfl, rfl⟩

/-- Unbounded storage preserves the entire owned native vector, at every element type. -/
theorem progressive_list_refines {T : Type} (input : alloc.vec.Vec T) :
    ∃ value, NyxSszRust.collections.progressive_list input = RustM.ok value ∧
      value.values = input := by
  exact ⟨⟨input⟩, rfl, rfl⟩

/-- The immutable progressive-list projection exposes the original elements in order. -/
theorem progressive_list_as_slice_refines {T : Type}
    (value : NyxSszRust.collections.ProgressiveList T) :
    ∃ result, NyxSszRust.collections.ProgressiveList.as_slice value = RustM.ok result ∧
      result.val = value.values.val := by
  exact ⟨alloc.vec.Vec.deref value.values, rfl, rfl⟩

end NyxSszVerification
