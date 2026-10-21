import NyxSszVerification.Multiproof.Maximum

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace NyxSszVerification

def helperCollectionAgrees (actual : core.result.Result (alloc.vec.Vec U128)
    NyxSszRust.merkle.ProofError) (expected : List Nat) (capacity : Nat)
    (overflow : NyxSszRust.merkle.ProofError) : Prop :=
  match actual with
  | .Ok values => values.val.map UScalar.val = expected ∧ expected.length ≤ capacity
  | .Err error => error = overflow ∧ capacity < expected.length

@[step] theorem multiproof_collect_loop_refines (indices : Slice U128) (capacity : Usize)
    (overflow : NyxSszRust.merkle.ProofError) (output : alloc.vec.Vec U128) (upper : U128)
    (bounded : output.val.length ≤ capacity.val)
    (frontier : ∃ pending, canonicalHelpers indices.val = output.val.map UScalar.val ++ pending ∧
      (canonicalHelpers indices.val).filter (fun helper => helper ≤ upper.val) = pending) :
    NyxSszRust.multiproof.collect_helpers_loop indices capacity overflow output upper ⦃ actual =>
      helperCollectionAgrees actual.1 (canonicalHelpers indices.val) capacity.val overflow ⦄ := by
  unfold NyxSszRust.multiproof.collect_helpers_loop
  apply loop_total
    (invariant := fun current : alloc.vec.Vec U128 × U128 =>
      current.1.val.length ≤ capacity.val ∧ ∃ pending,
        canonicalHelpers indices.val = current.1.val.map UScalar.val ++ pending ∧
        (canonicalHelpers indices.val).filter (fun helper => helper ≤ current.2.val) = pending)
    (measure := fun current => current.2.val)
  · rintro ⟨nextOutput, nextUpper⟩ ⟨within, pending, decomposition, filtered⟩
    unfold NyxSszRust.multiproof.collect_helpers_loop.body
    apply spec_bind (multiproof_select_refines indices nextUpper)
    intro selected agreement
    rw [select_head, filtered] at agreement
    cases pending with
    | nil =>
      have zero : selected = 0#u128 := by
        apply UScalar.eq_of_val_eq
        have value : selected.val = 0 := by simpa only [List.headD_nil] using agreement
        scalar_tac
      simp only [zero, ↓reduceIte, spec_ok, helperCollectionAgrees]
      simp only [List.append_nil] at decomposition
      exact ⟨decomposition.symm, by simpa only [decomposition, List.length_map] using within⟩
    | cons head tail =>
      simp only [List.headD_cons] at agreement
      have member : head ∈ canonicalHelpers indices.val := by
        rw [decomposition]
        simp
      have positive := (canonicalHelpers_bounds indices.val head member).1
      have headBound : head ≤ nextUpper.val := by
        have inside : head ∈ (canonicalHelpers indices.val).filter
            (fun helper => helper ≤ nextUpper.val) := by rw [filtered]; simp
        exact of_decide_eq_true (List.mem_filter.mp inside).2
      have nonzero : selected ≠ 0#u128 := by scalar_tac
      simp only [if_neg nonzero]
      by_cases full : nextOutput.val.length = capacity.val
      · have nativeFull : alloc.vec.Vec.len nextOutput = capacity := by scalar_tac
        simp only [if_pos nativeFull, spec_ok, helperCollectionAgrees]
        refine ⟨trivial, ?_⟩
        have size := congrArg List.length decomposition
        simp only [List.length_append, List.length_map, List.length_cons] at size
        omega
      · have nativeRoom : alloc.vec.Vec.len nextOutput ≠ capacity := by scalar_tac
        have room : nextOutput.val.length < Usize.max := by scalar_tac
        simp only [if_neg nativeRoom]
        step*
        refine ⟨?_, ?_, by scalar_tac⟩
        · simp only [helpers1_post, List.length_append, List.length_singleton]
          have prior : nextOutput.val.length ≤ capacity.val := within
          omega
        · have restEq := descending_filter_tail _ nextUpper.val head tail
            (canonicalHelpers_sorted indices.val) (by omega) filtered
          rw [upper1_post1, agreement, restEq, helpers1_post, List.map_append,
            List.map_singleton, agreement, List.append_assoc]
          exact decomposition
  · exact ⟨bounded, frontier⟩

def boundedHelpersAgrees (actual : core.result.Result (alloc.vec.Vec U128)
    NyxSszRust.merkle.ProofError) (expected : Except Ssz.Err (List Nat)) (capacity : Nat)
    (overflow : NyxSszRust.merkle.ProofError) : Prop :=
  match expected with
  | .ok values => helperCollectionAgrees actual values capacity overflow
  | .error fault => match actual with
    | .Err error => proofFaultAgrees error fault
    | .Ok _ => False

@[step] theorem multiproof_collect_refines (indices : Slice U128) (capacity : Usize)
    (overflow : NyxSszRust.merkle.ProofError) :
    NyxSszRust.multiproof.collect_helpers indices capacity overflow ⦃ actual =>
      boundedHelpersAgrees actual (Ssz.getHelperIndices (indices.val.map UScalar.val))
        capacity.val overflow ⦄ := by
  unfold NyxSszRust.multiproof.collect_helpers
  rw [helpers_reference]
  apply spec_bind (multiproof_validate_refines indices)
  intro checked agreement
  cases expectedEq : Ssz.rejectRelated (indices.val.map UScalar.val) with
  | error fault =>
    cases checked with
    | Ok value => simp [expectedEq, unitResultAgrees] at agreement
    | Err error =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
      step*
      simpa only [expectedEq, Bind.bind, Except.bind, boundedHelpersAgrees,
        unitResultAgrees] using agreement
  | ok checkedUnit =>
    cases checkedUnit
    cases checked with
    | Err error => simp [expectedEq, unitResultAgrees] at agreement
    | Ok value =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]
      have initial : ∃ pending, canonicalHelpers indices.val =
          (alloc.vec.Vec.new U128).val.map UScalar.val ++ pending ∧
          (canonicalHelpers indices.val).filter
            (fun helper => helper ≤ core.num.U128.MAX.val) = pending := by
        refine ⟨canonicalHelpers indices.val, rfl, ?_⟩
        apply List.filter_eq_self.mpr
        intro helper member
        have bound := (canonicalHelpers_bounds indices.val helper member).2
        have maximum : core.num.U128.MAX.val = U128.max := by
          simp only [core.num.U128.MAX, UScalar.ofNat, UScalar.val, U128.rMax,
            U128.max, U128.numBits]
          rfl
        simpa only [maximum, decide_eq_true_eq] using bound
      apply spec_bind (multiproof_collect_loop_refines indices capacity overflow
        (alloc.vec.Vec.new U128) core.num.U128.MAX (by simp) initial)
      intro result agrees
      rcases result with ⟨result, flag⟩
      cases flag <;> step*
      all_goals simpa only [expectedEq, Bind.bind, Except.bind,
        Pure.pure, Except.pure, boundedHelpersAgrees] using agrees

/-- Native output refusal is exactly mathematical helper-list unrepresentability. -/
@[step] theorem multiproof_helper_indices_refines (indices : Slice U128) :
    NyxSszRust.multiproof.helper_indices indices ⦃ actual =>
      boundedHelpersAgrees actual (Ssz.getHelperIndices (indices.val.map UScalar.val))
        Usize.max .SizeOverflow ⦄ := by
  unfold NyxSszRust.multiproof.helper_indices
  simpa using multiproof_collect_refines indices core.num.Usize.MAX .SizeOverflow

end NyxSszVerification
