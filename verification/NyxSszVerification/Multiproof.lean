import NyxSszVerification.Multiproof.Collect
import NyxSszVerification.Multiproof.Rebuild

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace NyxSszVerification

theorem multiproof_word_depth (index : U128) : Ssz.levelOf index.val ≤ 127 := by
  by_cases zero : index.val = 0
  · simp [Ssz.levelOf, zero]
  · have bounded := index_depth_bound index zero
    exact Nat.le_of_lt_succ bounded

theorem multiproof_frontier_depth (indices helpers : List U128) :
    ∀ index ∈ indices.map UScalar.val ++ helpers.map UScalar.val, Ssz.levelOf index ≤ 127 := by
  intro index member
  rcases List.mem_append.mp member with member | member
  all_goals
    obtain ⟨word, _, rfl⟩ := List.mem_map.mp member
    exact multiproof_word_depth word

@[step] theorem multiproof_calculate_merkle_root_refines
    (leaves proof : Slice RustNode) (indices : Slice U128) :
    NyxSszRust.multiproof.calculate_merkle_root leaves proof indices ⦃ actual =>
      rootResultAgrees actual (Ssz.calculateMultiMerkleRoot
        (proofNodes leaves.val) (proofNodes proof.val) (indices.val.map UScalar.val)) ⦄ := by
  unfold NyxSszRust.multiproof.calculate_merkle_root
  by_cases leafCount : leaves.val.length = indices.val.length
  · have nativeCounts : Slice.len leaves = Slice.len indices := by scalar_tac
    simp only [nativeCounts, bne_self_eq_false, Bool.false_eq_true, if_false]
    apply spec_bind (multiproof_collect_refines indices (Slice.len proof) .InvalidProofLength)
    intro collected agreement
    generalize expectedEq : Ssz.getHelperIndices (indices.val.map UScalar.val) = expected
      at agreement
    cases expected with
    | error fault =>
      cases collected with
      | Ok values => simp [boundedHelpersAgrees] at agreement
      | Err error =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
        step*
        simpa [boundedHelpersAgrees, rootResultAgrees, Ssz.calculateMultiMerkleRoot, proofNodes, leafCount,
          expectedEq, Bind.bind, Except.bind, Pure.pure, Except.pure] using agreement
    | ok helpers =>
      simp only [boundedHelpersAgrees, helperCollectionAgrees] at agreement
      cases collected with
      | Err error =>
        obtain ⟨errorEq, tooMany⟩ := agreement
        have different : proof.val.length ≠ helpers.length := by scalar_tac
        simp [errorEq, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          rootResultAgrees, Ssz.calculateMultiMerkleRoot, leafCount, expectedEq,
          proofNodes, different, Bind.bind, Except.bind, Pure.pure, Except.pure,
          proofFaultAgrees, throw, throwThe, MonadExceptOf.throw]
      | Ok values =>
        obtain ⟨valuesEq, _⟩ := agreement
        have helperLength : values.val.length = helpers.length := by
          have same := congrArg List.length valuesEq
          simpa only [List.length_map] using same
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]
        by_cases proofCount : proof.val.length = values.val.length
        · have nativeProofCount : Slice.len proof = alloc.vec.Vec.len values := by scalar_tac
          simp only [nativeProofCount, bne_self_eq_false, Bool.false_eq_true, if_false]
          have expectedRoot := Ssz.calculateMultiMerkleRoot_cut
            (leaves := proofNodes leaves.val) (proof := proofNodes proof.val) expectedEq
            (by simp [proofNodes, leafCount])
            (by simp [proofNodes, proofCount, helperLength]) 127
            (by rw [← valuesEq]; exact multiproof_frontier_depth indices.val values.val)
          rw [expectedRoot]
          apply spec_mono (multiproof_rebuild_refines leaves proof indices
            (alloc.vec.Vec.deref values) 1#u128 127#u32 leafCount proofCount (by scalar_tac)
            (by scalar_tac))
          intro actual agrees
          simpa [frontierNodes, alloc.vec.Vec.deref, valuesEq] using agrees
        · have nativeDifferent : Slice.len proof ≠ alloc.vec.Vec.len values := by scalar_tac
          have different : proof.val.length ≠ helpers.length := by omega
          simp [nativeDifferent, rootResultAgrees, proofFaultAgrees,
            Ssz.calculateMultiMerkleRoot, proofNodes, leafCount, expectedEq, different,
            Bind.bind, Except.bind, Pure.pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  · have nativeDifferent : Slice.len leaves ≠ Slice.len indices := by scalar_tac
    simp [nativeDifferent, rootResultAgrees, proofFaultAgrees, Ssz.calculateMultiMerkleRoot,
      proofNodes, leafCount, Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

@[step] theorem multiproof_verify_merkle_proof_refines
    (leaves proof : Slice RustNode) (indices : Slice U128) (root : RustNode) :
    NyxSszRust.multiproof.verify_merkle_proof leaves proof indices root ⦃ actual =>
      proofResultAgrees actual (Ssz.verifyMerkleMultiproof
        (proofNodes leaves.val) (proofNodes proof.val) (indices.val.map UScalar.val)
        (bytesToSpec root.val)) ⦄ := by
  unfold NyxSszRust.multiproof.verify_merkle_proof
  apply spec_bind (multiproof_calculate_merkle_root_refines leaves proof indices)
  intro calculated agreement
  generalize expectedEq : Ssz.calculateMultiMerkleRoot (proofNodes leaves.val)
    (proofNodes proof.val) (indices.val.map UScalar.val) = expected at agreement
  cases calculated with
  | Ok actual =>
    cases expected with
    | error fault => simp [rootResultAgrees] at agreement
    | ok expectedRoot =>
      simp only [rootResultAgrees] at agreement
      step*
      simp [proofResultAgrees, Ssz.verifyMerkleMultiproof, node_check, proof_nodes_check,
        Bind.bind, Except.bind, expectedEq]
      apply Bool.eq_iff_iff.mpr
      simpa only [beq_iff_eq, ← agreement] using b_post
  | Err fault =>
    cases expected with
    | ok expectedRoot => simp [rootResultAgrees] at agreement
    | error expectedFault =>
      simp only [rootResultAgrees] at agreement
      simp [proofResultAgrees, Ssz.verifyMerkleMultiproof, node_check, proof_nodes_check,
        Bind.bind, Except.bind, expectedEq, agreement]

end NyxSszVerification
