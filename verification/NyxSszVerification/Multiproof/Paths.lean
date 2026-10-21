import NyxSszRust.Multiproof
import NyxSszVerification.Gindex
import NyxSszVerification.Loop

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace NyxSszVerification

def claimPath (index : Nat) : List Nat := gindexPath index index.log2

theorem claimPath_small (index : Nat) (small : index ≤ 1) : claimPath index = [] := by
  have cases : index = 0 ∨ index = 1 := by omega
  rcases cases with rfl | rfl <;> rfl

theorem claimPath_step (index : Nat) (large : 2 ≤ index) :
    claimPath index = index :: claimPath (index / 2) := by
  have depth : index.log2 = (index / 2).log2 + 1 :=
    (Nat.log2_def index).trans (if_pos large)
  unfold claimPath gindexPath
  rw [depth, List.range_succ_eq_map, List.map_cons, List.map_map]
  simp only [Nat.shiftRight_zero]
  congr 1
  apply List.map_congr_left
  intro level _
  simp [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]

@[step] theorem multiproof_claim_path_refines (node candidate : U128) :
    NyxSszRust.multiproof.claim_path node candidate ⦃ actual =>
      actual = (claimPath node.val).contains candidate.val ⦄ := by
  unfold NyxSszRust.multiproof.claim_path NyxSszRust.multiproof.claim_path_loop
  apply loop_total
    (invariant := fun current : U128 =>
      (claimPath current.val).contains candidate.val = (claimPath node.val).contains candidate.val)
    (measure := fun current => current.val)
  · intro current invariant
    unfold NyxSszRust.multiproof.claim_path_loop.body
    by_cases large : 2 ≤ current.val
    · rw [← invariant, claimPath_step current.val large]
      step*
      all_goals simp_all [Ssz.gindexParent, gindex_word_eq]
      all_goals omega
    · have small : current.val ≤ 1 := by omega
      rw [claimPath_small _ small] at invariant
      simp_all [show ¬current > 1#u128 by scalar_tac]
  · rfl

@[simp] theorem path_values_contains (values : List U128) (candidate : U128) :
    (values.map UScalar.val).contains candidate.val = values.contains candidate := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.contains_iff_mem, List.mem_map]
  constructor
  · rintro ⟨value, member, same⟩
    exact UScalar.eq_of_val_eq same ▸ member
  · intro member
    exact ⟨candidate, member, rfl⟩

def pathsOf (indices : List U128) : List Nat :=
  indices.flatMap fun index => claimPath index.val

@[step] theorem multiproof_on_path_loop_refines (iter : core.slice.iter.Iter U128)
    (candidate : U128) :
    NyxSszRust.multiproof.on_path_loop iter candidate ⦃ actual =>
      actual = (pathsOf (iter.slice.val.drop iter.i)).contains candidate.val ⦄ := by
  unfold NyxSszRust.multiproof.on_path_loop
  apply loop_total
    (invariant := fun current : core.slice.iter.Iter U128 =>
      (pathsOf (current.slice.val.drop current.i)).contains candidate.val =
        (pathsOf (iter.slice.val.drop iter.i)).contains candidate.val)
    (measure := fun current => current.slice.val.length - current.i)
  · intro current invariant
    unfold NyxSszRust.multiproof.on_path_loop.body core.slice.iter.IteratorSliceIter.next
    simp only [Slice.len_val, Slice.length]
    by_cases active : current.i < current.slice.val.length
    · have rest : current.slice.val.drop current.i = current.slice.val[current.i] ::
          current.slice.val.drop (current.i + 1) := by
        exact List.drop_eq_getElem_cons active
      rw [dif_pos active]
      simp only [bind_tc_ok]
      apply spec_bind (multiproof_claim_path_refines _ candidate)
      intro result agreement
      rw [rest] at invariant
      simp only [pathsOf, List.flatMap_cons, List.contains_append] at invariant
      change result = (claimPath current.slice.val[current.i].val).contains candidate.val
        at agreement
      cases result
      · simp only [Bool.false_eq_true, ↓reduceIte, spec_ok]
        refine ⟨?_, by omega⟩
        simpa only [pathsOf, ← agreement, Bool.false_or] using invariant
      · simp only [↓reduceIte, spec_ok]
        simpa only [pathsOf, ← agreement, Bool.true_or] using invariant
    · have rest : current.slice.val.drop current.i = [] := List.drop_eq_nil_of_le (by omega)
      rw [dif_neg active]
      change false = (pathsOf (iter.slice.val.drop iter.i)).contains candidate.val
      rw [rest] at invariant
      simpa only [pathsOf, List.flatMap_nil, List.contains_nil] using invariant
  · rfl

@[step] theorem multiproof_on_path_refines (indices : Slice U128) (candidate : U128) :
    NyxSszRust.multiproof.on_path indices candidate ⦃ actual =>
      actual = (pathsOf indices.val).contains candidate.val ⦄ := by
  unfold NyxSszRust.multiproof.on_path
  simp only [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter, bind_tc_ok]
  simpa using multiproof_on_path_loop_refines ⟨indices, 0⟩ candidate

end NyxSszVerification
