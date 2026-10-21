import NyxSszVerification.Merkleize

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace NyxSszVerification

theorem progressive_width (level : Nat) : 4 ^ level = 2 ^ (2 * level) := by
  rw [Nat.pow_mul]

theorem progressive_depth (level : Nat) : Ssz.depthFor (4 ^ level) = 2 * level := by
  rw [progressive_width, Ssz.depthFor_pow]

/-- A nonterminal level leaves room for the next even depth on either native platform. -/
theorem progressive_next_bound (level : Nat) (chunks : Slice RustNode)
    (more : 4 ^ level < chunks.val.length) :
    2 * (level + 1) ≤ UScalarTy.Usize.numBits := by
  have fits : chunks.val.length < 2 ^ UScalarTy.Usize.numBits := by scalar_tac
  have small : 2 * level < UScalarTy.Usize.numBits := by
    apply (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
    rw [← progressive_width]
    omega
  simp only [UScalarTy.Usize_numBits_eq] at *
  cases System.Platform.numBits_eq <;> omega

theorem progressive_width_fits (level : Nat)
    (within : 2 * level ≤ UScalarTy.Usize.numBits) :
    4 ^ level < 2 ^ 128 := by
  rw [progressive_width]
  apply Nat.pow_lt_pow_right (by decide)
  simp only [UScalarTy.Usize_numBits_eq] at within
  cases System.Platform.numBits_eq <;> omega

theorem progressive_empty (level : Nat) :
    Ssz.merkleizeProgressive [] level = Ssz.zeroChunk := by
  rw [Ssz.merkleizeProgressive]
  rfl

theorem progressive_unfold (nodes : List RustNode) (level : Nat) (nonempty : nodes ≠ []) :
    Ssz.merkleizeProgressive (proofNodes nodes) level =
      Ssz.combine (nodeTree (nodes.take (4 ^ level)) (2 * level))
        (Ssz.merkleizeProgressive (proofNodes (nodes.drop (4 ^ level))) (level + 1)) := by
  rw [Ssz.merkleizeProgressive]
  simp only [proofNodes, List.isEmpty_map, List.isEmpty_iff, nonempty, ↓reduceIte]
  rw [progressive_depth, ← List.map_take, ← List.map_drop]
  rw [← proofNodes, ← proofNodes, subtreeAt_nodeTree]

theorem progressive_zero_bytes :
    bytesToSpec (Array.repeat 32#usize 0#u8).val = Ssz.zeroChunk := by
  simp [bytesToSpec, byteToSpec, Ssz.zeroChunk, Ssz.bytesPerChunk]
  rfl

theorem progressive_length_cast (chunks : Slice RustNode) :
    (UScalar.cast .U128 chunks.len).val = chunks.val.length := by
  have bound := chunks.length_ineq
  simp only [UScalar.cast_val_eq, Slice.len_val]
  apply Nat.mod_eq_of_lt
  simp only [Usize.max, Usize.numBits, UScalarTy.Usize_numBits_eq] at bound
  cases System.Platform.numBits_eq <;> simp_all <;> omega

theorem progressive_width_cast (chunks : Slice RustNode) (width : U128)
    (more : width.val < chunks.val.length) :
    (UScalar.cast .Usize width).val = width.val := by
  simp only [UScalar.cast_val_eq]
  apply Nat.mod_eq_of_lt
  have bound := chunks.length_ineq
  scalar_tac

theorem progressive_next_safe (chunks : Slice RustNode) (depth : Usize) (width : U128)
    (level : Nat) (depth_eq : depth.val = 2 * level) (width_eq : width.val = 4 ^ level)
    (more : 4 ^ level < chunks.val.length) :
    depth.val + 2 ≤ Usize.max ∧ width.val * 4 ≤ U128.max ∧
      2 * (level + 1) ≤ UScalarTy.Usize.numBits := by
  have next := progressive_next_bound level chunks more
  have fits := progressive_width_fits (level + 1) next
  rw [Nat.pow_succ] at fits
  have depthFits : depth.val + 2 ≤ Usize.max := by
    simp only [UScalarTy.Usize_numBits_eq] at next
    cases System.Platform.numBits_eq <;> scalar_tac
  exact ⟨depthFits, by scalar_tac, next⟩

theorem progressive_short (nodes : List RustNode) (level : Nat)
    (short : nodes.length ≤ 4 ^ level) :
    Ssz.merkleizeProgressive (proofNodes (nodes.drop (4 ^ level))) (level + 1) =
      Ssz.zeroChunk := by
  rw [List.drop_eq_nil_iff.mpr short]
  exact progressive_empty _

/-- Total safety and refinement of the actual recursive Rust computation.
The induction decreases the remaining native slice length, not a bounded test domain. -/
@[step] theorem progressive_subtree_root_refines (chunks : Slice RustNode)
    (depth : Usize) (width : U128) (level : Nat)
    (depth_eq : depth.val = 2 * level) (width_eq : width.val = 4 ^ level)
    (within : 2 * level ≤ UScalarTy.Usize.numBits) :
    NyxSszRust.merkle.progressive_subtree_root chunks depth width ⦃ actual =>
      bytesToSpec actual.val = Ssz.merkleizeProgressive (proofNodes chunks.val) level ⦄ := by
  generalize equation : chunks.val.length = number
  induction number using Nat.strong_induction_on generalizing chunks depth width level with
  | h number ih =>
    rw [NyxSszRust.merkle.progressive_subtree_root.eq_def]
    step*
    · have empty : chunks.val = [] := by
        apply List.length_eq_zero_iff.mp
        scalar_tac
      rw [empty]
      exact progressive_zero_bytes.trans (progressive_empty level).symm
    have depthWithin : depth.val ≤ UScalarTy.Usize.numBits := by omega
    have castLength : i1.val = chunks.val.length := by
      rw [i1_post, progressive_length_cast]
    have nonempty : chunks.val ≠ [] := by
      intro empty
      simp_all [Slice.length]
    rw [progressive_unfold chunks.val level nonempty]
    split
    · have short : chunks.val.length ≤ 4 ^ level := by scalar_tac
      step*
      simp only [↓reduceIte]
      step*
      rw [actual_post, progressive_zero_bytes, left_post, s_post1]
      simp only [Slice.len_val, Slice.length, List.slice_zero_j, List.take_length,
        List.take_of_length_le short, depth_eq, progressive_short _ _ short]
    · have more : 4 ^ level < chunks.val.length := by scalar_tac
      have castWidth : (UScalar.cast .Usize width).val = 4 ^ level :=
        (progressive_width_cast chunks width (by omega)).trans width_eq
      have safe := progressive_next_safe chunks depth width level depth_eq width_eq more
      have next := fun (rest : Slice RustNode) (d : Usize) (w : U128)
        (de : d.val = 2 * (level + 1)) (we : w.val = 4 ^ (level + 1))
        (smaller : rest.val.length < number) =>
          ih rest.val.length smaller rest d w (level + 1) de we safe.2.2 rfl
      clear ih
      step*
      split <;> step*
      all_goals simp_all only [Nat.pow_succ, List.slice_zero_j]
      all_goals (simp_all; omega)

theorem merkleize_progressive_refines (chunks : Slice RustNode) :
    NyxSszRust.merkle.merkleize_progressive chunks ⦃ actual =>
      bytesToSpec actual.val = Ssz.merkleizeProgressive (proofNodes chunks.val) ⦄ := by
  unfold NyxSszRust.merkle.merkleize_progressive
  apply progressive_subtree_root_refines (level := 0) <;> scalar_tac

end NyxSszVerification
