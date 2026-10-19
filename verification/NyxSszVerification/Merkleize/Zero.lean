import NyxSszVerification.Sha256
import NyxSszRust.Merkle
import Ssz.Merkle.Tree

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxRecDepth 4096
set_option maxHeartbeats 200000

namespace NyxSszVerification

@[step] theorem zero_root_refines (depth : Usize) :
    NyxSszRust.merkle.zero_root depth ⦃ root =>
      bytesToSpec root.val = Ssz.zeroRoot Ssz.combine Ssz.zeroChunk depth.val ⦄ := by
  generalize equation : depth.val = number
  induction number generalizing depth with
  | zero =>
    have zero : depth = 0#usize := by scalar_tac
    rw [NyxSszRust.merkle.zero_root.eq_def]
    simp [zero, bytesToSpec, byteToSpec, Ssz.zeroRoot, Ssz.zeroChunk, Ssz.bytesPerChunk]
    rfl
  | succ number ih =>
    rw [NyxSszRust.merkle.zero_root.eq_def]
    step*
    all_goals simp_all [Ssz.zeroRoot]

end NyxSszVerification
