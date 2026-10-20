import NyxSszVerification.Gindex.Arithmetic

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace NyxSszVerification

theorem reference_concat_nonzero (outer inner : Nat) (outerNonzero : outer ≠ 0)
    (innerNonzero : inner ≠ 0) :
    Ssz.gindexConcat outer inner = .ok (outer * 2 ^ inner.log2 + (inner - 2 ^ inner.log2)) := by
  have outerPositive : ¬outer < 1 := by omega
  have innerPositive : ¬inner < 1 := by omega
  simp [Ssz.gindexConcat, Ssz.gindexDepth, outerPositive, innerPositive,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

@[step] theorem gindex_concat_refines (outer inner : U128) :
    NyxSszRust.gindex.concat outer inner ⦃ actual =>
      gindexResultAgrees UScalar.val U128.max actual (Ssz.gindexConcat outer.val inner.val) ⦄ := by
  by_cases outerZero : outer = 0#u128
  · simp [outerZero, NyxSszRust.gindex.concat, NyxSszRust.gindex.depth,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      Ssz.gindexConcat, Ssz.gindexDepth,
      gindexResultAgrees, proofFaultAgrees, Bind.bind, Except.bind]
  have outerNonzero : outer.val ≠ 0 := by scalar_tac
  unfold NyxSszRust.gindex.concat
  apply spec_bind (gindex_depth_nonzero outer outerNonzero)
  intro result success
  obtain ⟨outerDepth, same, outerDepthValue⟩ := success
  simp only [same, core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]
  by_cases innerZero : inner = 0#u128
  · simp [innerZero, NyxSszRust.gindex.depth,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      Ssz.gindexConcat, Ssz.gindexDepth, outerNonzero,
      gindexResultAgrees, proofFaultAgrees, Bind.bind, Except.bind]
  have innerNonzero : inner.val ≠ 0 := by scalar_tac
  apply spec_bind (gindex_depth_nonzero inner innerNonzero)
  intro result success
  obtain ⟨innerDepth, same, innerDepthValue⟩ := success
  simp only [same, bind_tc_ok]
  have depthBound := index_depth_bound inner innerNonzero
  have small : innerDepth.val < 128 := by omega
  have bounded : 2 ^ inner.val.log2 < U128.size := by
    simpa only [innerDepthValue] using gindex_power_small innerDepth small
  have fits : 2 ^ inner.val.log2 ≤ inner.val := (Nat.le_log2 innerNonzero).mp (by rfl)
  rw [reference_concat_nonzero outer.val inner.val outerNonzero innerNonzero]
  step*
  all_goals simp_all [gindexResultAgrees, Nat.shiftLeft_eq, Nat.mod_eq_of_lt bounded]
  all_goals scalar_tac

end NyxSszVerification
