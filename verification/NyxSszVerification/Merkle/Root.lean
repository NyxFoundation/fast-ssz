import NyxSszVerification.Merkle.Climb

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace NyxSszVerification

def proofFaultAgrees : NyxSszRust.merkle.ProofError → Ssz.Err → Prop
  | .InvalidIndex, .notAGindex _ => True
  | .RootHasNoBranch, .rootHasNoBranch => True
  | .InvalidBranchLength, .branchLength _ _ => True
  | _, _ => False

def rootResultAgrees : core.result.Result RustNode NyxSszRust.merkle.ProofError →
    Except Ssz.Err Ssz.Bytes → Prop
  | .Ok node, .ok bytes => bytesToSpec node.val = bytes
  | .Err actual, .error expected => proofFaultAgrees actual expected
  | _, _ => False

@[step] theorem calculate_merkle_root_refines
    (leaf : RustNode) (proof : Slice RustNode) (index : U128) :
    NyxSszRust.merkle.calculate_merkle_root leaf proof index ⦃ actual =>
      rootResultAgrees actual
        (Ssz.calculateMerkleRoot (bytesToSpec leaf.val) (proofNodes proof.val) index.val) ⦄ := by
  unfold NyxSszRust.merkle.calculate_merkle_root
  by_cases zero : index = 0#u128
  · have value : index.val = 0 := by scalar_tac
    simp only [if_pos zero]
    simp [value, rootResultAgrees, proofFaultAgrees, Ssz.calculateMerkleRoot,
      Ssz.gindexLength, Ssz.gindexDepth, Bind.bind, Except.bind]
  by_cases one : index = 1#u128
  · have value : index.val = 1 := by scalar_tac
    simp only [if_neg zero, if_pos one]
    simp [value, rootResultAgrees, proofFaultAgrees, Ssz.calculateMerkleRoot,
      Ssz.gindexLength, Ssz.gindexDepth, Bind.bind, Except.bind]
  have lower : 2 ≤ index.val := by scalar_tac
  have nonzero : index.val ≠ 0 := by omega
  have bounded := index_depth_bound index nonzero
  rw [calculate_root_form _ _ index.val lower]
  have lengths : (proofNodes proof.val).length = proof.val.length := by simp [proofNodes]
  rw [lengths]
  simp only [zero, one, if_false]
  by_cases long : Slice.len proof >= 128#usize
  · have different : proof.val.length ≠ index.val.log2 := by scalar_tac
    simp [long, different, rootResultAgrees, proofFaultAgrees]
  · simp only [long, if_false]
    step*
    all_goals simp_all [rootResultAgrees, proofFaultAgrees, shift_one_iff_log2]

end NyxSszVerification
