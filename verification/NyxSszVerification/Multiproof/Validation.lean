import NyxSszVerification.Multiproof.Dedup

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace NyxSszVerification

@[simp] theorem u128_any_eq (values : List U128) (candidate : U128) :
    List.anyM (core.cmp.PartialEqU128.eq candidate) values =
      RustM.ok (values.contains candidate) := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.anyM, bind_tc_ok, List.contains_cons]
    split <;> simp_all [pure]

@[step] theorem multiproof_contains_refines (indices : Slice U128) (candidate : U128) :
    core.slice.Slice.contains core.cmp.PartialEqU128 indices candidate ⦃ actual =>
      actual = indices.val.contains candidate ⦄ := by
  unfold core.slice.Slice.contains
  rw [u128_any_eq]
  simp

def repeatedResult (indices : List U128) : core.result.Result Unit NyxSszRust.merkle.ProofError :=
  if indices.Nodup then .Ok () else .Err .RepeatedIndex

@[step] theorem multiproof_repeated_loop_refines (indices : Slice U128) (offset : Usize)
    (within : offset.val ≤ indices.val.length) (unique : (indices.val.take offset.val).Nodup) :
    NyxSszRust.multiproof.reject_repeated_loop indices offset ⦃ actual =>
      actual = repeatedResult indices.val ⦄ := by
  unfold NyxSszRust.multiproof.reject_repeated_loop
  apply loop_total
    (invariant := fun next : Usize => next.val ≤ indices.val.length ∧
      (indices.val.take next.val).Nodup)
    (measure := fun next => indices.val.length - next.val)
  · intro next invariant
    obtain ⟨bounded, uniquePrefix⟩ := invariant
    unfold NyxSszRust.multiproof.reject_repeated_loop.body
    by_cases active : next.val < indices.val.length
    · have extend := List.take_succ_eq_append_getElem active
      simp only [if_pos (show next < Slice.len indices by scalar_tac)]
      step
      step
      step as ⟨found, agreement⟩
      by_cases hit : found = true
      · have member : indices.val[next.val] ∈ indices.val.take next.val := by
          simp_all
        have repeated : ¬indices.val.Nodup := by
          intro allUnique
          have nextUnique := allUnique.sublist (List.take_sublist (next.val + 1) indices.val)
          rw [extend, List.nodup_append] at nextUnique
          exact nextUnique.2.2 _ member _ (by simp) rfl
        simp [hit, repeatedResult, repeated]
      · have absent : indices.val[next.val] ∉ indices.val.take next.val := by simp_all
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [offset1_post, extend, List.nodup_append]
        simp_all
        intro value member same
        exact absent (UScalar.eq_of_val_eq same ▸ member)
    · have endEq : next.val = indices.val.length := by omega
      have allUnique : indices.val.Nodup := by simpa [endEq] using uniquePrefix
      step*
      simp [repeatedResult, allUnique]
  · exact ⟨within, unique⟩

@[step] theorem multiproof_repeated_refines (indices : Slice U128) :
    NyxSszRust.multiproof.reject_repeated indices ⦃ actual =>
      actual = repeatedResult indices.val ⦄ := by
  unfold NyxSszRust.multiproof.reject_repeated
  apply multiproof_repeated_loop_refines <;> simp

def unitResultAgrees : core.result.Result Unit NyxSszRust.merkle.ProofError →
    Except Ssz.Err Unit → Prop
  | .Ok _, .ok _ => True
  | .Err actual, .error expected => proofFaultAgrees actual expected
  | _, _ => False

@[step] theorem multiproof_ancestors_refines (indices : Slice U128) (ancestor : U128)
    (claim : Nat) :
    NyxSszRust.multiproof.validate_claim_loop indices ancestor ⦃ actual =>
      unitResultAgrees actual (Ssz.rejectAncestors (indices.val.map UScalar.val)
        claim (claimPath ancestor.val)) ⦄ := by
  unfold NyxSszRust.multiproof.validate_claim_loop
  apply loop_total
    (invariant := fun current : U128 =>
      Ssz.rejectAncestors (indices.val.map UScalar.val) claim (claimPath current.val) =
        Ssz.rejectAncestors (indices.val.map UScalar.val) claim (claimPath ancestor.val))
    (measure := fun current => current.val)
  · intro current invariant
    unfold NyxSszRust.multiproof.validate_claim_loop.body
    by_cases large : 2 ≤ current.val
    · rw [claimPath_step current.val large] at invariant
      simp only [Ssz.rejectAncestors, path_values_contains] at invariant
      step*
      all_goals simp_all [Ssz.gindexParent, unitResultAgrees, proofFaultAgrees,
        Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
      · rw [← invariant]
        trivial
      · refine ⟨?_, by omega⟩
        simpa only [Pure.pure, Except.pure] using invariant
    · have small : current.val ≤ 1 := by omega
      rw [claimPath_small _ small] at invariant
      simp only [Ssz.rejectAncestors] at invariant
      simp [show ¬current > 1#u128 by scalar_tac, ← invariant, unitResultAgrees]
  · rfl

def checkClaim (indices : List Nat) (claim : Nat) : Except Ssz.Err Unit := do
  let path ← Ssz.getPathIndices claim
  Ssz.rejectAncestors indices claim (path.drop 1)

@[step] theorem multiproof_validate_claim_refines (indices : Slice U128) (index : U128) :
    NyxSszRust.multiproof.validate_claim indices index ⦃ actual =>
      unitResultAgrees actual (checkClaim (indices.val.map UScalar.val) index.val) ⦄ := by
  by_cases zero : index = 0#u128
  · simp [zero, NyxSszRust.multiproof.validate_claim, NyxSszRust.gindex.length,
      NyxSszRust.gindex.depth, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      checkClaim, Ssz.getPathIndices, Ssz.gindexLength, Ssz.gindexDepth,
      unitResultAgrees, proofFaultAgrees, Bind.bind, Except.bind]
  by_cases root : index = 1#u128
  · simp [root, NyxSszRust.multiproof.validate_claim, NyxSszRust.gindex.length,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      checkClaim, Ssz.getPathIndices, Ssz.gindexLength, Ssz.gindexDepth,
      unitResultAgrees, proofFaultAgrees, Bind.bind, Except.bind]
  have large : 2 ≤ index.val := by scalar_tac
  unfold NyxSszRust.multiproof.validate_claim
  apply spec_bind (gindex_length_success index large)
  intro measured info
  obtain ⟨count, measuredEq, _⟩ := info
  simp only [measuredEq, core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]
  step as ⟨ancestor, same⟩
  have tailEq : (claimPath index.val).drop 1 = claimPath ancestor.val := by
    rw [claimPath_step _ large, List.drop_one, same]
    rfl
  have referenceEq : checkClaim (indices.val.map UScalar.val) index.val =
      Ssz.rejectAncestors (indices.val.map UScalar.val) index.val (claimPath ancestor.val) := by
    simp only [checkClaim, Ssz.getPathIndices, gindex_length_positive _ large,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    change Ssz.rejectAncestors _ _ ((claimPath index.val).drop 1) = _
    rw [tailEq]
  rw [referenceEq]
  exact multiproof_ancestors_refines indices ancestor index.val

theorem checkClaim_cons (indices : List Nat) (claim : Nat) (rest : List Nat) :
    Ssz.rejectClaimPaths indices (claim :: rest) =
      (do checkClaim indices claim; Ssz.rejectClaimPaths indices rest) := by
  rw [Ssz.rejectClaimPaths]
  unfold checkClaim
  cases Ssz.getPathIndices claim <;> simp only [Bind.bind, Except.bind]

theorem unitResult_ok {actual : Unit} {expected : Except Ssz.Err Unit}
    (agrees : unitResultAgrees (.Ok actual) expected) : expected = .ok () := by
  cases expected with
  | error _ => contradiction
  | ok value => cases value; rfl

@[step] theorem multiproof_validate_loop_refines (indices : Slice U128)
    (iter : core.slice.iter.Iter U128) :
    NyxSszRust.multiproof.validate_loop iter indices ⦃ actual =>
      unitResultAgrees actual (Ssz.rejectClaimPaths (indices.val.map UScalar.val)
        ((iter.slice.val.drop iter.i).map UScalar.val)) ⦄ := by
  unfold NyxSszRust.multiproof.validate_loop
  apply loop_total
    (invariant := fun current : core.slice.iter.Iter U128 =>
      Ssz.rejectClaimPaths (indices.val.map UScalar.val)
        ((current.slice.val.drop current.i).map UScalar.val) =
      Ssz.rejectClaimPaths (indices.val.map UScalar.val)
        ((iter.slice.val.drop iter.i).map UScalar.val))
    (measure := fun current => current.slice.val.length - current.i)
  · intro current invariant
    unfold NyxSszRust.multiproof.validate_loop.body core.slice.iter.IteratorSliceIter.next
    simp only [Slice.len_val, Slice.length]
    by_cases active : current.i < current.slice.val.length
    · rw [dif_pos active]
      simp only [bind_tc_ok]
      apply spec_bind (multiproof_validate_claim_refines indices _)
      intro checked agreement
      change unitResultAgrees checked
        (checkClaim (indices.val.map UScalar.val) current.slice.val[current.i].val) at agreement
      rw [List.drop_eq_getElem_cons active, List.map_cons, checkClaim_cons] at invariant
      cases checked with
      | Ok value =>
        rw [unitResult_ok agreement] at invariant
        simp only [Bind.bind, Except.bind] at invariant
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok, spec_ok]
        exact ⟨invariant, by omega⟩
      | Err fault =>
        cases expectedEq : checkClaim (indices.val.map UScalar.val)
            current.slice.val[current.i].val with
        | ok value => simp [expectedEq, unitResultAgrees] at agreement
        | error expectedFault =>
          rw [expectedEq] at invariant
          simp only [Bind.bind, Except.bind] at invariant
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
          change unitResultAgrees (.Err fault) _
          rw [← invariant]
          simpa only [unitResultAgrees, expectedEq] using agreement
    · rw [dif_neg active]
      have rest : current.slice.val.drop current.i = [] := List.drop_eq_nil_of_le (by omega)
      rw [rest, List.map_nil, Ssz.rejectClaimPaths] at invariant
      change unitResultAgrees (.Ok ()) _
      rw [← invariant]
      trivial
  · rfl

@[step] theorem multiproof_validate_refines (indices : Slice U128) :
    NyxSszRust.multiproof.validate indices ⦃ actual =>
      unitResultAgrees actual (Ssz.rejectRelated (indices.val.map UScalar.val)) ⦄ := by
  unfold NyxSszRust.multiproof.validate
  by_cases empty : indices.val = []
  · simp [empty, core.slice.Slice.is_empty, Ssz.rejectRelated,
      unitResultAgrees, proofFaultAgrees, throw, throwThe, MonadExceptOf.throw,
      Bind.bind, Except.bind]
  · have nonempty : indices.val.isEmpty = false := List.isEmpty_eq_false_iff.mpr empty
    simp only [core.slice.Slice.is_empty, Slice.length, List.length_eq_zero_iff, empty,
      bind_tc_ok]
    apply spec_bind (multiproof_repeated_refines indices)
    intro repeated agreement
    simp only [agreement, repeatedResult]
    by_cases unique : indices.val.Nodup
    · simp only [if_pos unique, core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok,
        SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter]
      have referenceEq : Ssz.rejectRelated (indices.val.map UScalar.val) =
          Ssz.rejectClaimPaths (indices.val.map UScalar.val) (indices.val.map UScalar.val) := by
        have mapped : (indices.val.map UScalar.val).Nodup :=
          (multiproof_nodup_values _).mpr unique
        have sized := (multiproof_dedup_length _).mpr mapped
        simp [Ssz.rejectRelated, nonempty, sized, Bind.bind, Except.bind,
          Pure.pure, Except.pure]
      rw [referenceEq]
      simpa only [List.drop_zero] using multiproof_validate_loop_refines indices ⟨indices, 0⟩
    · have different : (indices.val.map UScalar.val).eraseDups.length ≠
          indices.val.length := by
        intro same
        apply unique
        apply (multiproof_nodup_values _).mp
        apply (multiproof_dedup_length _).mp
        simpa only [List.length_map] using same
      simp [unique, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        Ssz.rejectRelated, nonempty, different, Bind.bind, Except.bind,
        unitResultAgrees, proofFaultAgrees, throw, throwThe, MonadExceptOf.throw,
        Pure.pure, Except.pure]

end NyxSszVerification
