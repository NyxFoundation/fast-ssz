import FastSszVerification.Merkle.Root

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace FastSszVerification

def proofResultAgrees : core.result.Result Bool FastSszRust.merkle.ProofError →
    Except Ssz.Err Bool → Prop
  | .Ok actual, .ok expected => actual = expected
  | .Err actual, .error expected => proofFaultAgrees actual expected
  | _, _ => False

@[step] theorem verify_merkle_proof_refines
    (leaf : RustNode) (proof : Slice RustNode) (index : U128) (root : RustNode) :
    FastSszRust.merkle.verify_merkle_proof leaf proof index root ⦃ actual =>
      proofResultAgrees actual
        (Ssz.verifyMerkleProof (bytesToSpec leaf.val) (proofNodes proof.val) index.val
          (bytesToSpec root.val)) ⦄ := by
  unfold FastSszRust.merkle.verify_merkle_proof
  step as ⟨calculated, agreement⟩
  generalize expectedEq :
    Ssz.calculateMerkleRoot (bytesToSpec leaf.val) (proofNodes proof.val) index.val =
      expected at agreement
  cases calculated with
  | Ok actual =>
    cases expected with
    | error fault => simp [rootResultAgrees] at agreement
    | ok expectedRoot =>
      simp only [rootResultAgrees] at agreement
      step*
      simp [proofResultAgrees, Ssz.verifyMerkleProof, node_check, proof_nodes_check,
        Bind.bind, Except.bind, expectedEq]
      apply Bool.eq_iff_iff.mpr
      simpa only [beq_iff_eq, ← agreement] using b_post
  | Err fault =>
    cases expected with
    | ok expectedRoot => simp [rootResultAgrees] at agreement
    | error expectedFault =>
      simp only [rootResultAgrees] at agreement
      simp [proofResultAgrees, Ssz.verifyMerkleProof, node_check, proof_nodes_check,
        Bind.bind, Except.bind, expectedEq, agreement]

end FastSszVerification
