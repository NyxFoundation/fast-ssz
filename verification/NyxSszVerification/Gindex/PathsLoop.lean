import NyxSszVerification.Gindex.Arithmetic
import NyxSszVerification.Loop

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace NyxSszVerification

@[step] theorem gindex_path_loop_refines (index : U128) (count : U32)
    (output : alloc.vec.Vec U128) (level : U32) (small : count.val < 128)
    (within : level.val ≤ count.val)
    (data : output.val.map UScalar.val = gindexPath index.val level.val) :
    NyxSszRust.gindex.path_indices_loop index count output level ⦃ result =>
      result.val.map UScalar.val = gindexPath index.val count.val ⦄ := by
  have slots : count.val ≤ Usize.max := by scalar_tac
  unfold NyxSszRust.gindex.path_indices_loop
  apply loop_total
    (invariant := fun state : alloc.vec.Vec U128 × U32 =>
      state.2.val ≤ count.val ∧ state.1.val.map UScalar.val = gindexPath index.val state.2.val)
    (measure := fun state => count.val - state.2.val)
  · rintro ⟨nextOutput, nextLevel⟩ ⟨inBounds, values⟩
    have outputLength : nextOutput.val.length = nextLevel.val := by
      have same := congrArg List.length values
      simpa [gindexPath] using same
    unfold NyxSszRust.gindex.path_indices_loop.body
    by_cases active : nextLevel.val < count.val
    · step*
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [path1_post, List.map_append, List.map_singleton, values, level1_post]
      simp [gindexPath, List.range_succ, i_post1]
    · step*
  · exact ⟨within, data⟩

@[step] theorem gindex_branch_loop_refines (index : U128) (count : U32)
    (output : alloc.vec.Vec U128) (level : U32) (small : count.val < 128)
    (within : level.val ≤ count.val)
    (data : output.val.map UScalar.val = gindexBranch index.val level.val) :
    NyxSszRust.gindex.branch_indices_loop index count output level ⦃ result =>
      result.val.map UScalar.val = gindexBranch index.val count.val ⦄ := by
  have slots : count.val ≤ Usize.max := by scalar_tac
  unfold NyxSszRust.gindex.branch_indices_loop
  apply loop_total
    (invariant := fun state : alloc.vec.Vec U128 × U32 =>
      state.2.val ≤ count.val ∧ state.1.val.map UScalar.val = gindexBranch index.val state.2.val)
    (measure := fun state => count.val - state.2.val)
  · rintro ⟨nextOutput, nextLevel⟩ ⟨inBounds, values⟩
    have outputLength : nextOutput.val.length = nextLevel.val := by
      have same := congrArg List.length values
      simpa [gindexBranch, gindexPath] using same
    unfold NyxSszRust.gindex.branch_indices_loop.body
    by_cases active : nextLevel.val < count.val
    · step*
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [siblings1_post, List.map_append, List.map_singleton, values, level1_post]
      simp [gindexBranch, gindexPath, List.range_succ, i_post1, i1_post1]
    · step*
  · exact ⟨within, data⟩

end NyxSszVerification
