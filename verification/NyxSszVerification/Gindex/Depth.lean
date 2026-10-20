import NyxSszVerification.Gindex.Model

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace NyxSszVerification

theorem gindex_leading_zeros (index : U128) (nonzero : index.val ≠ 0) :
    (core.num.U128.leading_zeros index).val = 127 - index.val.log2 := by
  have bounded := index_depth_bound index nonzero
  have bitsNonzero : index.bv ≠ 0 := by
    intro same
    apply nonzero
    change index.bv.toNat = 0
    rw [same]
    rfl
  simp only [core.num.U128.leading_zeros, BitVec.leadingZeros, if_neg bitsNonzero,
    ← Nat.log2_eq_log_two]
  change (128 - index.val.log2 - 1) % 2 ^ 32 = 127 - index.val.log2
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

@[step] theorem gindex_depth_refines (index : U128) :
    NyxSszRust.gindex.depth index ⦃ actual =>
      gindexResultAgrees UScalar.val U32.max actual (Ssz.gindexDepth index.val) ⦄ := by
  unfold NyxSszRust.gindex.depth
  by_cases zero : index = 0#u128
  · simp [zero, gindexResultAgrees, proofFaultAgrees, Ssz.gindexDepth]
  · have nonzero : index.val ≠ 0 := by scalar_tac
    have bounded := index_depth_bound index nonzero
    have leading := gindex_leading_zeros index nonzero
    have positive : ¬index.val < 1 := by omega
    simp only [zero, if_false]
    step*
    simp only [gindexResultAgrees, Ssz.gindexDepth, if_neg positive]
    scalar_tac

theorem gindex_depth_nonzero (index : U128) (nonzero : index.val ≠ 0) :
    NyxSszRust.gindex.depth index ⦃ actual =>
      ∃ value : U32, actual = .Ok value ∧ value.val = index.val.log2 ⦄ := by
  apply spec_mono (gindex_depth_refines index)
  intro actual agrees
  have positive : ¬index.val < 1 := by omega
  have bounded := index_depth_bound index nonzero
  cases actual with
  | Ok value =>
    exact ⟨value, rfl, by simpa [gindexResultAgrees, Ssz.gindexDepth, positive] using agrees⟩
  | Err error =>
    cases error <;> simp_all [gindexResultAgrees, Ssz.gindexDepth]
    scalar_tac

theorem reference_length_nonroot (index : Nat) (nonroot : index ≠ 1) :
    Ssz.gindexLength index = Ssz.gindexDepth index := by
  by_cases zero : index = 0
  · simp [zero, Ssz.gindexLength, Ssz.gindexDepth, Bind.bind, Except.bind]
  · have lower : 2 ≤ index := by omega
    rw [gindex_length_positive index lower]
    simp [Ssz.gindexDepth, show ¬index < 1 by omega]

@[step] theorem gindex_length_refines (index : U128) :
    NyxSszRust.gindex.length index ⦃ actual =>
      gindexResultAgrees UScalar.val U32.max actual (Ssz.gindexLength index.val) ⦄ := by
  unfold NyxSszRust.gindex.length
  by_cases root : index = 1#u128
  · simp [root, gindexResultAgrees, proofFaultAgrees, Ssz.gindexLength,
      Ssz.gindexDepth, Bind.bind, Except.bind]
  · have nonroot : index.val ≠ 1 := by scalar_tac
    simpa only [if_neg root, reference_length_nonroot index.val nonroot] using gindex_depth_refines index

theorem gindex_length_success (index : U128) (lower : 2 ≤ index.val) :
    NyxSszRust.gindex.length index ⦃ actual =>
      ∃ count : U32, actual = .Ok count ∧ count.val = index.val.log2 ⦄ := by
  apply spec_mono (gindex_length_refines index)
  intro actual agrees
  rw [gindex_length_positive index.val lower] at agrees
  have bounded := index_depth_bound index (by omega)
  cases actual with
  | Ok count => exact ⟨count, rfl, by simpa [gindexResultAgrees] using agrees⟩
  | Err error =>
    cases error <;> simp_all [gindexResultAgrees]
    scalar_tac

end NyxSszVerification
