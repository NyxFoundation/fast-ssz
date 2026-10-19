import NyxSszVerification.Merkleize.Nodes
import NyxSszVerification.Merkleize.Zero

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxRecDepth 4096
set_option maxHeartbeats 200000

namespace NyxSszVerification

@[step] theorem subtree_root_refines (chunks : Slice RustNode) (depth : Usize)
    (within : depth.val ≤ UScalarTy.Usize.numBits) :
    NyxSszRust.merkle.subtree_root chunks depth ⦃ root =>
      bytesToSpec root.val = nodeTree chunks.val depth.val ⦄ := by
  generalize equation : depth.val = height
  induction height generalizing chunks depth with
  | zero =>
    rw [NyxSszRust.merkle.subtree_root.eq_def]
    step*
    all_goals simp_all [nodeTree, Ssz.subtreeRoot, Ssz.padded, proofNodes, Ssz.zeroRoot]
  | succ height ih =>
    rw [NyxSszRust.merkle.subtree_root.eq_def]
    step*
    all_goals simp_all
    have powerFits : 2 ^ height < Usize.size := by
      simp only [Usize.size, Usize.numBits]
      exact Nat.pow_lt_pow_right (by decide) within
    have actualHalf : half.val = 2 ^ height := by
      simp [half_post1, Nat.shiftLeft_eq, Nat.mod_eq_of_lt powerFits]
    split <;> step*
    all_goals simp_all [nodeTree_short, nodeTree_split]

end NyxSszVerification
