import FastSszVerification.Sha256
import FastSszRust.Merkle
import Ssz.Merkle.Tree

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxRecDepth 4096
set_option maxHeartbeats 200000

namespace FastSszVerification

@[step] theorem zero_root_refines (depth : Usize) :
    FastSszRust.merkle.zero_root depth ⦃ root =>
      bytesToSpec root.val = Ssz.zeroRoot Ssz.combine Ssz.zeroChunk depth.val ⦄ := by
  generalize equation : depth.val = number
  induction number generalizing depth with
  | zero =>
    have zero : depth = 0#usize := by scalar_tac
    rw [FastSszRust.merkle.zero_root.eq_def]
    simp [zero, bytesToSpec, byteToSpec, Ssz.zeroRoot, Ssz.zeroChunk, Ssz.bytesPerChunk]
    rfl
  | succ number ih =>
    rw [FastSszRust.merkle.zero_root.eq_def]
    step*
    all_goals simp_all [Ssz.zeroRoot]

end FastSszVerification
