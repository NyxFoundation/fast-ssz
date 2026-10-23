import NyxSszRust.HistoricalMerkle
import Ssz.Proofs.Merkle.Merkleize

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxRecDepth 4096
set_option maxHeartbeats 200000

namespace NyxSszVerification

@[step] theorem depth_for_refines (count : Usize) :
    NyxSszRust.merkle.depth_for count ⦃ depth =>
      depth.val = Ssz.depthFor count.val ∧ depth.val ≤ count.val ⦄ := by
  generalize equation : count.val = number
  induction number using Nat.strong_induction_on generalizing count with
  | h number ih =>
    rw [NyxSszRust.merkle.depth_for.eq_def]
    step*
    all_goals simp_all
    all_goals rw [Ssz.depthFor.eq_def number]
    all_goals have half : number / 2 + number % 2 = (number + 1) / 2 := by omega
    all_goals simp_all [Nat.add_comm]
    all_goals omega

theorem depthFor_machine_bound (count : Usize) :
    Ssz.depthFor count.val ≤ UScalarTy.Usize.numBits := by
  apply Ssz.depthFor_le_of_le_two_pow
  scalar_tac

end NyxSszVerification
