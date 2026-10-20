import NyxSszVerification.Gindex.PathsLoop

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace NyxSszVerification

@[step] theorem gindex_path_indices_refines (index : U128) :
    NyxSszRust.gindex.path_indices index ⦃ actual =>
      gindexListAgrees actual (Ssz.getPathIndices index.val) ⦄ := by
  by_cases zero : index = 0#u128
  · simp [zero, NyxSszRust.gindex.path_indices, NyxSszRust.gindex.length, NyxSszRust.gindex.depth,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      gindexListAgrees, proofFaultAgrees, Ssz.getPathIndices, Ssz.gindexLength,
      Ssz.gindexDepth, Bind.bind, Except.bind]
  by_cases root : index = 1#u128
  · simp [root, NyxSszRust.gindex.path_indices, NyxSszRust.gindex.length,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      gindexListAgrees, proofFaultAgrees, Ssz.getPathIndices, Ssz.gindexLength,
      Ssz.gindexDepth, Bind.bind, Except.bind]
  have lower : 2 ≤ index.val := by scalar_tac
  unfold NyxSszRust.gindex.path_indices
  apply spec_bind (gindex_length_success index lower)
  intro result success
  obtain ⟨count, same, countValue⟩ := success
  simp only [same, core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]
  have depthBound := index_depth_bound index (by omega)
  have small : count.val < 128 := by omega
  step*
  all_goals simp_all [gindexListAgrees, gindexPath, Ssz.getPathIndices,
    gindex_length_positive index.val lower, Bind.bind, Except.bind, Pure.pure, Except.pure]

@[step] theorem gindex_branch_indices_refines (index : U128) :
    NyxSszRust.gindex.branch_indices index ⦃ actual =>
      gindexListAgrees actual (Ssz.getBranchIndices index.val) ⦄ := by
  by_cases zero : index = 0#u128
  · simp [zero, NyxSszRust.gindex.branch_indices, NyxSszRust.gindex.length, NyxSszRust.gindex.depth,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      gindexListAgrees, proofFaultAgrees, Ssz.getBranchIndices, Ssz.getPathIndices, Ssz.gindexLength,
      Ssz.gindexDepth, Bind.bind, Except.bind]
  by_cases root : index = 1#u128
  · simp [root, NyxSszRust.gindex.branch_indices, NyxSszRust.gindex.length,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      gindexListAgrees, proofFaultAgrees, Ssz.getBranchIndices, Ssz.getPathIndices, Ssz.gindexLength,
      Ssz.gindexDepth, Bind.bind, Except.bind]
  have lower : 2 ≤ index.val := by scalar_tac
  unfold NyxSszRust.gindex.branch_indices
  apply spec_bind (gindex_length_success index lower)
  intro result success
  obtain ⟨count, same, countValue⟩ := success
  simp only [same, core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]
  have depthBound := index_depth_bound index (by omega)
  have small : count.val < 128 := by omega
  step*
  all_goals simp_all [gindexListAgrees, gindexBranch, gindexPath, Ssz.getBranchIndices,
    Ssz.getPathIndices, Ssz.gindexSibling, gindex_length_positive index.val lower,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

end NyxSszVerification
