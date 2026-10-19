import FastSszRust.Merkle
import FastSszVerification.Sha256
import FastSszVerification.Merkle.Nodes

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace FastSszVerification

@[step] theorem climb_refines (current : RustNode) (proof : Slice RustNode) (index : U128) :
    FastSszRust.merkle.climb current proof index ⦃ result =>
      bytesToSpec result.val =
        Ssz.climbBranch index.val 0 (bytesToSpec current.val) (proofNodes proof.val) ⦄ := by
  generalize equation : proof.val = data
  induction data generalizing current proof index with
  | nil =>
    rw [FastSszRust.merkle.climb.eq_def]
    simp [core.slice.Slice.is_empty, equation, proofNodes, Ssz.climbBranch]
  | cons sibling rest ih =>
    rw [FastSszRust.merkle.climb.eq_def]
    simp [core.slice.Slice.is_empty, equation]
    step*
    split <;> step*
    all_goals
      have bit : (i = 1#u128) ↔ index.val % 2 = 1 := by scalar_tac
      simp_all [proofNodes, Ssz.climbBranch, Ssz.gindexBit, Nat.testBit_zero,
        climbBranch_shift]

end FastSszVerification
