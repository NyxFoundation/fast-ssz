import NyxSszRust.CollectionTree
import NyxSszVerification.Codec.Metadata

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxHeartbeats 1000000

namespace NyxSszVerification

@[step] theorem collection_div_ceil_refines (value divisor : Usize)
    (allowed : divisor.val ∈ [1, 2, 4, 8, 16, 32]) :
    NyxSszRust.core.num.Usize.div_ceil value divisor ⦃ actual =>
      actual.val = (value.val + divisor.val - 1) / divisor.val ⦄ := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at allowed
  rcases allowed with h | h | h | h | h | h
  all_goals unfold NyxSszRust.core.num.Usize.div_ceil
  all_goals step*
  all_goals scalar_tac

/-- Basic packing capacities are computed without multiplying in a machine word. -/
@[step] theorem collection_basic_capacity_refines {T State : Type}
    (child : NyxSszRust.codec.Ssz T State) (shape : Ssz.Desc)
    (declared : child.TYPE ⦃ actual => typeDescriptorToSpec actual = shape ⦄)
    (valid : shape.wellFormed = .ok ()) (basic : shape.isBasic = true) (positions : Usize) :
    NyxSszRust.collection_tree.basic_capacity child positions ⦃ actual =>
      ∃ capacity, actual = .Ok capacity ∧
        capacity.val = Ssz.chunksForBytes (positions.val * shape.itemLength) ⦄ := by
  unfold NyxSszRust.collection_tree.basic_capacity
  apply spec_bind (codec_fixed_size_refines child shape declared)
  intro actual correct
  have result (width : Nat) (fixed : shape.fixedSize = some width) (small : width ≤ Usize.max) :
      ∃ held, actual = .Ok (some held) ∧ held.val = width := by
    cases actual with
    | Ok held => cases held <;> simp_all [codecWidthAgrees]
    | Err kind => cases kind <;> simp_all [codecWidthAgrees]; omega
  have platform := Usize.bounds_eq
  cases shape <;> simp only [Ssz.Desc.isBasic, Bool.false_eq_true] at basic
  · obtain ⟨width, same, widthEq⟩ := result 1 rfl (by scalar_tac)
    clear result
    rw [same]
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok, widthEq]
    step*
    · simp [i1_post]
    refine ⟨i2, rfl, ?_⟩
    simp only [Ssz.chunksForBytes, Ssz.Desc.itemLength, Ssz.bytesPerChunk]
    scalar_tac
  · rename_i size
    have widths : size ∈ [1, 2, 4, 8, 16, 32] := by
      simp [Ssz.Desc.wellFormed] at valid
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      grind
    have small : size ≤ Usize.max := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at widths
      rcases widths with h | h | h | h | h | h <;> scalar_tac
    obtain ⟨width, same, widthEq⟩ := result size rfl small
    clear result
    rw [same]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at widths
    rcases widths with h | h | h | h | h | h
    all_goals have numericWidth := widthEq.trans h
    all_goals simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok, numericWidth]
    all_goals step*
    all_goals try (solve | simp [i1_post])
    all_goals refine ⟨i2, rfl, ?_⟩
    all_goals simp only [Ssz.chunksForBytes, Ssz.Desc.itemLength, Ssz.bytesPerChunk, h]
    all_goals scalar_tac

end NyxSszVerification
