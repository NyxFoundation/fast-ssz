import NyxSszVerification.Multiproof.Selection
import Ssz.Proofs.Merkle.Gindex

open Aeneas Aeneas.Std

namespace NyxSszVerification

def canonicalHelpers (indices : List U128) : List Nat :=
  let paths := pathsOf indices
  (((paths.map Ssz.gindexSibling).eraseDups).filter fun node => !paths.contains node).mergeSort
    (fun left right => right ≤ left)

theorem canonicalHelpers_mem (indices : List U128) (node : Nat) :
    node ∈ canonicalHelpers indices ↔
      node ∈ (pathsOf indices).map Ssz.gindexSibling ∧ node ∉ pathsOf indices := by
  simp [canonicalHelpers, List.mem_mergeSort]

theorem canonicalHelpers_nodup (indices : List U128) : (canonicalHelpers indices).Nodup := by
  apply List.Perm.nodup (List.mergeSort_perm _ _).symm
  exact (multiproof_dedup_info _).2.filter _

theorem canonicalHelpers_sorted (indices : List U128) :
    (canonicalHelpers indices).Pairwise (fun left right => right < left) := by
  have ordered : (canonicalHelpers indices).Pairwise (fun left right => right ≤ left) := by
    unfold canonicalHelpers
    have sorted := List.pairwise_mergeSort
      (le := fun left right : Nat => decide (right ≤ left))
      (by intro a b c; simp only [decide_eq_true_eq]; omega)
      (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
      (((pathsOf indices).map Ssz.gindexSibling).eraseDups.filter
        fun node => !(pathsOf indices).contains node)
    simpa only [decide_eq_true_eq] using sorted
  have unique := canonicalHelpers_nodup indices
  exact (ordered.and unique).imp (by intro a b pair; omega)

theorem claimPath_bounds (index node : Nat) (member : node ∈ claimPath index) :
    2 ≤ node ∧ node ≤ index := by
  induction index using Nat.strong_induction_on with
  | h index ih =>
    by_cases large : 2 ≤ index
    · rw [claimPath_step _ large] at member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨large, le_rfl⟩
      · obtain ⟨lower, upper⟩ := ih (index / 2) (by omega) member
        exact ⟨lower, by omega⟩
    · rw [claimPath_small _ (by omega)] at member
      contradiction

theorem pathsOf_bounds (indices : List U128) (node : Nat) (member : node ∈ pathsOf indices) :
    2 ≤ node ∧ node ≤ U128.max := by
  obtain ⟨index, _, path⟩ := List.mem_flatMap.mp member
  obtain ⟨lower, upper⟩ := claimPath_bounds index.val node path
  exact ⟨lower, by scalar_tac⟩

theorem canonicalHelpers_bounds (indices : List U128) (node : Nat)
    (member : node ∈ canonicalHelpers indices) : 2 ≤ node ∧ node ≤ U128.max := by
  obtain ⟨sibling, _⟩ := (canonicalHelpers_mem indices node).mp member
  obtain ⟨path, pathMember, rfl⟩ := List.mem_map.mp sibling
  obtain ⟨lower, upper⟩ := pathsOf_bounds indices path pathMember
  have half := Ssz.gindexSibling_half path
  constructor
  · omega
  · have word : U128.max + 1 = 2 ^ 128 := by scalar_tac
    have small : Ssz.gindexSibling path < 2 ^ 128 :=
      Nat.xor_lt_two_pow (by scalar_tac) (by decide)
    omega

theorem rejectClaims_valid (indices pending : List Nat)
    (accepted : Ssz.rejectClaimPaths indices pending = .ok ()) :
    ∀ index ∈ pending, 2 ≤ index := by
  induction pending with
  | nil => simp
  | cons claim rest ih =>
    rw [checkClaim_cons] at accepted
    cases checked : checkClaim indices claim with
    | error fault => simp [checked, Bind.bind, Except.bind] at accepted
    | ok checkedUnit =>
      have validClaim : 2 ≤ claim := by
        unfold checkClaim Ssz.getPathIndices at checked
        cases measured : Ssz.gindexLength claim with
        | error fault => simp [measured, Bind.bind, Except.bind] at checked
        | ok depth =>
          by_cases zero : claim = 0
          · simp [zero, Ssz.gindexLength, Ssz.gindexDepth, Bind.bind, Except.bind] at measured
          by_cases root : claim = 1
          · simp [root, Ssz.gindexLength, Ssz.gindexDepth, Bind.bind, Except.bind] at measured
          omega
      have tail : Ssz.rejectClaimPaths indices rest = .ok () := by
        simpa [checked, Bind.bind, Except.bind] using accepted
      intro index member
      rcases List.mem_cons.mp member with rfl | member
      · exact validClaim
      · exact ih tail index member

theorem rejectRelated_valid (indices : List Nat) (accepted : Ssz.rejectRelated indices = .ok ()) :
    ∀ index ∈ indices, 2 ≤ index := by
  simp only [Ssz.rejectRelated, Bind.bind, Except.bind, Pure.pure, Except.pure] at accepted
  split at accepted
  · simp [throw, throwThe, MonadExceptOf.throw] at accepted
  · split at accepted
    · simp [throw, throwThe, MonadExceptOf.throw] at accepted
    · apply rejectClaims_valid indices indices
      simpa [Bind.bind, Except.bind, Pure.pure, Except.pure] using accepted

theorem collectPaths_exact (indices : List U128) (valid : ∀ index ∈ indices, 2 ≤ index.val) :
    Ssz.collectPathIndices (indices.map UScalar.val) = .ok (pathsOf indices) := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
    simp only [List.map_cons]
    rw [Ssz.collectPathIndices]
    simp only [Ssz.getPathIndices, gindex_length_positive _ (valid index (by simp)),
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    rw [ih (fun i member => valid i (by simp [member]))]
    rfl

theorem helpers_reference (indices : Slice U128) :
    Ssz.getHelperIndices (indices.val.map UScalar.val) =
      (do Ssz.rejectRelated (indices.val.map UScalar.val); return canonicalHelpers indices.val) := by
  rw [Ssz.getHelperIndices]
  cases accepted : Ssz.rejectRelated (indices.val.map UScalar.val) with
  | error fault => simp [Bind.bind, Except.bind]
  | ok checkedUnit =>
    have valid := rejectRelated_valid _ (show Ssz.rejectRelated _ = .ok () from by
      cases checkedUnit; exact accepted)
    have collected := collectPaths_exact indices.val (fun index member =>
      valid index.val (List.mem_map.mpr ⟨index, member, rfl⟩))
    simp only [Bind.bind, Except.bind, collected, Pure.pure, Except.pure]
    rfl

end NyxSszVerification
