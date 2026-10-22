import NyxSszVerification.Multiproof.Validation

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace NyxSszVerification

def chooseSibling (paths : List Nat) (upper best node : Nat) : Nat :=
  let sibling := Ssz.gindexSibling node
  if sibling ≤ upper ∧ sibling ∉ paths then max best sibling else best

def chooseHelpers (paths : List Nat) (upper : Nat) (pending : List Nat) (best : Nat) : Nat :=
  pending.foldl (chooseSibling paths upper) best

@[step] theorem multiproof_select_claim_refines (indices : Slice U128) (upper best node : U128) :
    NyxSszRust.multiproof.next_helper_loop0_loop0 indices upper best node ⦃ actual =>
      actual.val = chooseHelpers (pathsOf indices.val) upper.val (claimPath node.val) best.val ⦄ := by
  unfold NyxSszRust.multiproof.next_helper_loop0_loop0
  apply loop_total
    (invariant := fun current : U128 × U128 =>
      chooseHelpers (pathsOf indices.val) upper.val (claimPath current.2.val) current.1.val =
        chooseHelpers (pathsOf indices.val) upper.val (claimPath node.val) best.val)
    (measure := fun current => current.2.val)
  · rintro ⟨nextBest, nextNode⟩ invariant
    unfold NyxSszRust.multiproof.next_helper_loop0_loop0.body
    by_cases large : 2 ≤ nextNode.val
    · rw [claimPath_step _ large] at invariant
      simp only [chooseHelpers, List.foldl_cons] at invariant
      simp only [if_pos (show nextNode > 1#u128 by scalar_tac)]
      step as ⟨sibling, siblingValue⟩
      split <;> (try split) <;> step*
      all_goals simp_all [chooseSibling, chooseHelpers, max_def]
      all_goals try (split <;> step*)
      all_goals split_ifs at invariant <;> simp_all [Ssz.gindexParent]
      all_goals try omega
      have same : nextBest.val = Ssz.gindexSibling nextNode.val := by omega
      rw [same]
      exact ⟨invariant, by omega⟩
    · rw [claimPath_small nextNode.val (by omega)] at invariant
      simp only [chooseHelpers, List.foldl_nil] at invariant
      simp [show ¬nextNode > 1#u128 by scalar_tac, invariant, chooseHelpers]
  · rfl

@[step] theorem multiproof_select_loop_refines (indices : Slice U128)
    (iter : core.slice.iter.Iter U128) (upper best : U128) :
    NyxSszRust.multiproof.next_helper_loop0 iter indices upper best ⦃ actual =>
      actual.val = chooseHelpers (pathsOf indices.val) upper.val
        (pathsOf (iter.slice.val.drop iter.i)) best.val ⦄ := by
  unfold NyxSszRust.multiproof.next_helper_loop0
  apply loop_total
    (invariant := fun current : core.slice.iter.Iter U128 × U128 =>
      chooseHelpers (pathsOf indices.val) upper.val
        (pathsOf (current.1.slice.val.drop current.1.i)) current.2.val =
      chooseHelpers (pathsOf indices.val) upper.val
        (pathsOf (iter.slice.val.drop iter.i)) best.val)
    (measure := fun current => current.1.slice.val.length - current.1.i)
  · rintro ⟨current, nextBest⟩ invariant
    unfold NyxSszRust.multiproof.next_helper_loop0.body core.slice.iter.IteratorSliceIter.next
    simp only [Slice.len_val, Slice.length]
    by_cases active : current.i < current.slice.val.length
    · rw [dif_pos active]
      simp only [bind_tc_ok]
      apply spec_bind (multiproof_select_claim_refines indices upper nextBest _)
      intro selected agreement
      change selected.val = chooseHelpers (pathsOf indices.val) upper.val
        (claimPath current.slice.val[current.i].val) nextBest.val at agreement
      rw [List.drop_eq_getElem_cons active] at invariant
      simp only [pathsOf, List.flatMap_cons, chooseHelpers, List.foldl_append] at invariant
      simp only [spec_ok]
      refine ⟨?_, by omega⟩
      simpa only [chooseHelpers, pathsOf, agreement] using invariant
    · rw [dif_neg active]
      have rest : current.slice.val.drop current.i = [] := List.drop_eq_nil_of_le (by omega)
      rw [rest] at invariant
      change nextBest.val = _
      simpa only [chooseHelpers, pathsOf, List.flatMap_nil, List.foldl_nil] using invariant
  · rfl

@[step] theorem multiproof_select_refines (indices : Slice U128) (upper : U128) :
    NyxSszRust.multiproof.next_helper indices upper ⦃ actual =>
      actual.val = chooseHelpers (pathsOf indices.val) upper.val (pathsOf indices.val) 0 ⦄ := by
  unfold NyxSszRust.multiproof.next_helper
  simp only [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter, bind_tc_ok]
  simpa using
    multiproof_select_loop_refines indices ⟨indices, 0⟩ upper 0#u128

end NyxSszVerification
