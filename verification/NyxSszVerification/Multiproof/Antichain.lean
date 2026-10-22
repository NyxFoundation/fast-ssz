import NyxSszVerification.Multiproof.Frontier

namespace Ssz

theorem rejectRelated_checks {indices : List Nat} (accepted : rejectRelated indices = .ok ()) :
    indices ≠ [] ∧ indices.Nodup ∧ rejectClaimPaths indices indices = .ok () := by
  simp only [rejectRelated, Bind.bind, Except.bind, Pure.pure, Except.pure] at accepted
  split at accepted
  · simp [throw, throwThe, MonadExceptOf.throw] at accepted
  · rename_i nonempty
    split at accepted
    · simp [throw, throwThe, MonadExceptOf.throw] at accepted
    · rename_i same
      refine ⟨by simpa using nonempty, ?_, accepted⟩
      apply (NyxSszVerification.multiproof_dedup_length indices).mp
      simpa using same

private theorem rejectAncestors_excludes {indices ancestors : List Nat} {claim : Nat}
    (accepted : rejectAncestors indices claim ancestors = .ok ()) :
    ∀ ancestor ∈ ancestors, ancestor ∉ indices := by
  induction ancestors with
  | nil => simp
  | cons head rest ih =>
    by_cases present : head ∈ indices
    · simp [rejectAncestors, present, Bind.bind, Except.bind, throw, throwThe,
        MonadExceptOf.throw] at accepted
    · have tail : rejectAncestors indices claim rest = .ok () := by
        simpa [rejectAncestors, present, Bind.bind, Except.bind, Pure.pure, Except.pure] using accepted
      intro ancestor member
      rcases List.mem_cons.mp member with rfl | member
      · exact present
      · exact ih tail ancestor member

private theorem rejectClaimPaths_excludes {indices pending : List Nat}
    (accepted : rejectClaimPaths indices pending = .ok ()) :
    ∀ claim ∈ pending, ∃ path, getPathIndices claim = .ok path ∧
      ∀ ancestor ∈ path.drop 1, ancestor ∉ indices := by
  induction pending with
  | nil => simp
  | cons head rest ih =>
    cases pathEq : getPathIndices head with
    | error fault => simp [rejectClaimPaths, pathEq, Bind.bind, Except.bind] at accepted
    | ok path =>
      cases checked : rejectAncestors indices head path.tail with
      | error fault => simp [rejectClaimPaths, pathEq, checked, Bind.bind, Except.bind] at accepted
      | ok checkedUnit =>
        cases checkedUnit
        have tail : rejectClaimPaths indices rest = .ok () := by
          simpa [rejectClaimPaths, pathEq, checked, Bind.bind, Except.bind] using accepted
        intro claim member
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨path, pathEq, rejectAncestors_excludes (by simpa using checked)⟩
        · exact ih tail claim member

theorem rejectRelated_strict_shift {indices : List Nat}
    (accepted : rejectRelated indices = .ok ()) {claim step : Nat}
    (claimed : claim ∈ indices) (positive : 0 < step) (below : step < claim.log2) :
    claim >>> step ∉ indices := by
  obtain ⟨path, pathEq, excludes⟩ := rejectClaimPaths_excludes
    (rejectRelated_checks accepted).2.2 claim claimed
  cases measured : gindexLength claim with
  | error fault => simp [getPathIndices, measured, Bind.bind, Except.bind] at pathEq
  | ok depth =>
    obtain ⟨rfl, _, _⟩ := gindexLength_ok measured
    simp [getPathIndices, measured, Bind.bind, Except.bind, Pure.pure, Except.pure] at pathEq
    subst path
    apply excludes
    rw [← List.map_drop]
    apply List.mem_map.mpr
    refine ⟨step, List.mem_drop_iff_getElem.mpr ?_, rfl⟩
    refine ⟨step - 1, by simp; omega, ?_⟩
    simp only [List.getElem_range]
    omega

theorem shift_below_depth {claim step : Nat} (named : 1 ≤ claim)
    (below : 2 ≤ claim >>> step) : step < claim.log2 := by
  by_contra outside
  have distance : claim.log2 + (step - claim.log2) = step := by omega
  have upper : (claim >>> claim.log2) >>> (step - claim.log2) ≤ 1 := by
    rw [shiftRight_depth named]
    exact Nat.shiftRight_le 1 _
  rw [← Nat.shiftRight_add, distance] at upper
  omega

private theorem sibling_strict_shift (index step : Nat) (positive : 0 < step) :
    gindexSibling index >>> step = index >>> step := by
  have distance : step - 1 + 1 = step := by omega
  rw [← distance, Nat.add_comm (step - 1) 1, Nat.shiftRight_add, Nat.shiftRight_add]
  have half := gindexSibling_half index
  simpa [Nat.shiftRight_eq_div_pow] using congrArg (fun n => n >>> (step - 1)) half

theorem getHelperIndices_antichain {indices helpers : List Nat}
    (built : getHelperIndices indices = .ok helpers) :
    ∀ i ∈ indices ++ helpers, ∀ j ∈ indices ++ helpers, ∀ step,
      i >>> step = j → i = j := by
  obtain ⟨_, valid, frontier⟩ := getHelperIndices_frontier built
  have accepted : rejectRelated indices = .ok () := by
    unfold getHelperIndices at built
    cases checked : rejectRelated indices with
    | error fault => simp [checked, Bind.bind, Except.bind] at built
    | ok checkedUnit => cases checkedUnit; rfl
  intro i supplied j target step shifted
  by_cases zero : step = 0
  · simpa [zero] using shifted
  have positive : 0 < step := by omega
  have jBelow : 2 ≤ j := by
    rcases List.mem_append.mp target with claim | helper
    · exact valid j claim
    · exact (helperFrontier_sibling built (Or.inr helper)).1
  have origin : ∃ claim ∈ indices, ∃ distance, 0 < distance ∧ claim >>> distance = j := by
    rcases List.mem_append.mp supplied with claim | helper
    · exact ⟨i, claim, step, positive, shifted⟩
    · obtain ⟨mapped, _⟩ := (frontier i).mp helper
      obtain ⟨node, path, same⟩ := List.mem_map.mp mapped
      obtain ⟨claim, claimed, member⟩ := List.mem_flatMap.mp path
      obtain ⟨base, _, baseEq⟩ := List.mem_map.mp member
      refine ⟨claim, claimed, base + step, by omega, ?_⟩
      rw [Nat.shiftRight_add, baseEq, ← sibling_strict_shift node step positive, same]
      exact shifted
  obtain ⟨claim, claimed, distance, strict, reaches⟩ := origin
  have below := shift_below_depth (by have := valid claim claimed; omega)
    (show 2 ≤ claim >>> distance by omega)
  have onPath : j ∈ claimPaths indices := List.mem_flatMap.mpr
    ⟨claim, claimed, List.mem_map.mpr ⟨distance, List.mem_range.mpr below, reaches⟩⟩
  rcases List.mem_append.mp target with target | target
  · exact False.elim (rejectRelated_strict_shift accepted claimed strict below (reaches ▸ target))
  · exact False.elim (((frontier j).mp target).2 onPath)

theorem getHelperIndices_all_nodup {indices helpers : List Nat}
    (built : getHelperIndices indices = .ok helpers) : (indices ++ helpers).Nodup := by
  obtain ⟨_, valid, frontier⟩ := getHelperIndices_frontier built
  unfold getHelperIndices at built
  cases accepted : rejectRelated indices with
  | error fault => simp [accepted, Bind.bind, Except.bind] at built
  | ok checkedUnit =>
    cases checkedUnit
    cases collected : collectPathIndices indices with
    | error fault => simp [accepted, collected, Bind.bind, Except.bind] at built
    | ok paths =>
      simp [accepted, collected, Bind.bind, Except.bind, Pure.pure, Except.pure] at built
      have uniqueHelpers : helpers.Nodup := by
        rw [← built]
        apply List.Perm.nodup (List.mergeSort_perm _ _).symm
        exact (NyxSszVerification.multiproof_dedup_info _).2.filter _
      rw [List.nodup_append]
      refine ⟨(rejectRelated_checks accepted).2.1, uniqueHelpers, ?_⟩
      intro claim claimed helper supplied same
      subst helper
      exact ((frontier claim).mp supplied).2 (claim_mem_paths valid claimed)

end Ssz
