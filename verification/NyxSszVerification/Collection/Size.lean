import NyxSszRust.CollectionWire
import NyxSszVerification.Collections
import NyxSszVerification.Codec.Law
import NyxSszVerification.Loop

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxHeartbeats 2000000

namespace NyxSszVerification

@[simp, scalar_tac_simps] theorem collection_widen_usize (value : Usize) :
    (UScalar.cast .U128 value).val = value.val := by
  apply UScalar.cast_val_mod_pow_greater_numBits_eq
  cases System.Platform.numBits_eq <;> simp_all

@[simp, scalar_tac_simps] theorem collection_narrow_u128 (value : U128)
    (bound : value.val < 4294967296) : (UScalar.cast .Usize value).val = value.val := by
  apply UScalar.cast_val_mod_pow_of_inBounds_eq
  cases System.Platform.numBits_eq <;> simp_all
  omega

def collectionBodySize (parts : List (alloc.vec.Vec U8)) : Nat :=
  (parts.map fun part => part.val.length).sum

@[simp] theorem collectionBodySize_nil : collectionBodySize [] = 0 := rfl

@[simp] theorem collectionBodySize_cons (part : alloc.vec.Vec U8)
    (rest : List (alloc.vec.Vec U8)) :
    collectionBodySize (part :: rest) = part.val.length + collectionBodySize rest := rfl

def collectionLeading (parts : List (alloc.vec.Vec U8)) (fixed : Bool) : Nat :=
  if fixed then 0 else parts.length * 4

def collectionSizeAgrees
    (actual : core.result.Result (Usize × Usize) NyxSszRust.error.CodecError)
    (leading total : Nat) : Prop :=
  match actual with
  | .Ok (front, size) => front.val = leading ∧ size.val = total ∧ total < 4294967296
  | .Err .SizeOverflow => 4294967296 ≤ total
  | _ => False

@[step] theorem collection_size_loop_refines (parts : Slice (alloc.vec.Vec U8))
    (leading total : U128) (index : Usize)
    (within : index.val ≤ parts.val.length) (ordered : leading.val ≤ total.val)
    (bounded : total.val < 4294967296) :
    NyxSszRust.collection_wire.leading_and_total_loop parts leading total index ⦃ actual =>
      collectionSizeAgrees actual leading.val
        (total.val + collectionBodySize (parts.val.drop index.val)) ⦄ := by
  let expected := total.val + collectionBodySize (parts.val.drop index.val)
  unfold NyxSszRust.collection_wire.leading_and_total_loop
  apply loop_total
    (invariant := fun state : U128 × Usize =>
      state.2.val ≤ parts.val.length ∧ leading.val ≤ state.1.val ∧
      state.1.val < 4294967296 ∧
      state.1.val + collectionBodySize (parts.val.drop state.2.val) = expected)
    (measure := fun state => parts.val.length - state.2.val)
  · rintro ⟨nextTotal, nextIndex⟩ ⟨inBounds, afterLeading, budget, size⟩
    by_cases active : nextIndex.val < parts.val.length
    · have splitSize := size
      rw [List.drop_eq_getElem_cons active, collectionBodySize_cons] at splitSize
      have elementBound := (parts.val[nextIndex.val]).property
      unfold NyxSszRust.collection_wire.leading_and_total_loop.body
      step*
      · have platform := Usize.bounds_eq
        rw [i2_post]
        simp only [collection_widen_usize]
        scalar_tac
      · change collectionSizeAgrees _ leading.val expected
        simp only [collectionSizeAgrees]
        scalar_tac
      · refine ⟨by scalar_tac, by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
        simp only [index1_post]
        scalar_tac
    · unfold NyxSszRust.collection_wire.leading_and_total_loop.body
      step*
      have atEnd : nextIndex.val = parts.val.length := by scalar_tac
      have totalEq : nextTotal.val = expected := by
        simpa only [atEnd, List.drop_length, collectionBodySize_nil, Nat.add_zero] using size
      change collectionSizeAgrees _ leading.val expected
      simp only [collectionSizeAgrees, i1_post, i2_post,
        collection_narrow_u128 leading (by omega), collection_narrow_u128 nextTotal budget]
      exact ⟨trivial, totalEq, totalEq ▸ budget⟩
  · exact ⟨within, ordered, bounded, rfl⟩

@[step] theorem collection_size_refines (parts : Slice (alloc.vec.Vec U8)) (fixed : Bool) :
    NyxSszRust.collection_wire.leading_and_total parts fixed ⦃ actual =>
      collectionSizeAgrees actual (collectionLeading parts.val fixed)
        (collectionLeading parts.val fixed + collectionBodySize parts.val) ⦄ := by
  have lengthBound := parts.property
  unfold NyxSszRust.collection_wire.leading_and_total
  cases hFixed : fixed
  · simp only [Bool.false_eq_true, if_false, bind_assoc_eq]
    have platform := Usize.bounds_eq
    step*
    all_goals simp_all [collectionLeading, collectionSizeAgrees]
    all_goals scalar_tac
  · simpa [collectionLeading] using collection_size_loop_refines parts 0#u128 0#u128
      0#usize (by simp) (by simp) (by simp)

end NyxSszVerification
