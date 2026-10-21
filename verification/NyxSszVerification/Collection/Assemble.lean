import NyxSszVerification.Collection.Bodies
import NyxSszVerification.Collection.Offsets

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxHeartbeats 2000000

namespace NyxSszVerification

@[simp] theorem collectionSlots_nil (fixed : Bool) : collectionSlots [] fixed = [] := rfl

@[simp] theorem collectionSlots_cons (part : alloc.vec.Vec U8)
    (rest : List (alloc.vec.Vec U8)) (fixed : Bool) :
    collectionSlots (part :: rest) fixed = (fixed, bytesToSpec part.val) :: collectionSlots rest fixed := rfl

@[simp] theorem collection_slots_zip (parts : List (alloc.vec.Vec U8)) (fixed : Bool) :
    ((parts.map fun part => bytesToSpec part.val).map fun _ => fixed).zip
      (parts.map fun part => bytesToSpec part.val) = collectionSlots parts fixed := by
  induction parts with
  | nil => rfl
  | cons part rest ih => simpa [collectionSlots] using congrArg ((fixed, bytesToSpec part.val) :: ·) ih

@[simp] theorem collection_head_width (parts : List (alloc.vec.Vec U8)) (fixed : Bool) :
    Ssz.headWidth (collectionSlots parts fixed) =
      if fixed then collectionBodySize parts else parts.length * 4 := by
  induction parts with
  | nil => cases fixed <;> rfl
  | cons part rest ih => cases fixed <;> simp [Ssz.headWidth, ih, Ssz.bytesPerOffset]; omega

@[simp] theorem collection_body_width (parts : List (alloc.vec.Vec U8)) (fixed : Bool) :
    Ssz.bodyWidth (collectionSlots parts fixed) = if fixed then 0 else collectionBodySize parts := by
  induction parts with
  | nil => cases fixed <;> rfl
  | cons part rest ih => cases fixed <;> simp [Ssz.bodyWidth, ih]

@[simp] theorem collection_head_fixed (parts : List (alloc.vec.Vec U8)) (start : Nat) :
    Ssz.headOf start (collectionSlots parts true) = bytesToSpec (collectionBodyBytes parts) := by
  induction parts with
  | nil => rfl
  | cons part rest ih =>
    rw [collectionSlots_cons, Ssz.headOf, ih, collectionBodyBytes_cons]
    simp [bytesToSpec]

@[simp] theorem collection_bodies (parts : List (alloc.vec.Vec U8)) (fixed : Bool) :
    Ssz.bodiesOf (collectionSlots parts fixed) =
      if fixed then #[] else bytesToSpec (collectionBodyBytes parts) := by
  induction parts with
  | nil => cases fixed <;> rfl
  | cons part rest ih => cases fixed <;> simp only [collectionSlots_cons, Ssz.bodiesOf] <;>
      simp_all [bytesToSpec]

/-- Uniform sequence assembly still checks the total offset budget for fixed elements. -/
theorem collection_assemble_form (parts : List (alloc.vec.Vec U8)) (fixed : Bool) :
    Ssz.assemble ((parts.map fun part => bytesToSpec part.val).map fun _ => fixed)
      (parts.map fun part => bytesToSpec part.val) =
    if collectionLeading parts fixed + collectionBodySize parts ≥ 4294967296 then
      .error (.offsetOverflow (collectionLeading parts fixed + collectionBodySize parts))
    else .ok (if fixed then bytesToSpec (collectionBodyBytes parts)
      else Ssz.headOf (collectionLeading parts fixed) (collectionSlots parts false) ++
        bytesToSpec (collectionBodyBytes parts)) := by
  simp only [Ssz.assemble, collection_slots_zip, collection_head_width, collection_body_width]
  cases fixed <;>
    simp [collectionLeading, Ssz.bytesPerOffset, Bind.bind, Except.bind,
      Pure.pure, Except.pure, MonadExcept.throw, throwThe, MonadExceptOf.throw]

@[step] theorem collection_assemble_refines (parts : Slice (alloc.vec.Vec U8)) (fixed : Bool) :
    NyxSszRust.collection_wire.assemble parts fixed ⦃ actual =>
      codecEncodingAgrees actual (Ssz.assemble
        ((parts.val.map fun part => bytesToSpec part.val).map fun _ => fixed)
        (parts.val.map fun part => bytesToSpec part.val)) ⦄ := by
  rw [collection_assemble_form]
  unfold NyxSszRust.collection_wire.assemble
  apply spec_bind (collection_size_refines parts fixed)
  intro actual correct
  cases actual with
  | Err kind =>
    cases kind <;> simp only [collectionSizeAgrees] at correct
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      correct, codecEncodingAgrees, codecFaultAgrees]
  | Ok sizes =>
    obtain ⟨leading, total⟩ := sizes
    obtain ⟨leadingEq, totalEq, bounded⟩ := correct
    have totalBound : collectionLeading parts.val fixed + collectionBodySize parts.val < 4294967296 := by omega
    have platform := Usize.bounds_eq
    cases hFixed : fixed
    · have front : leading.val = parts.val.length * 4 := by simpa [hFixed, collectionLeading] using leadingEq
      have room : parts.val.length * 4 + collectionBodySize parts.val ≤ Usize.max := by
        simp only [hFixed, collectionLeading, Bool.false_eq_true, if_false] at totalBound
        scalar_tac
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok, Bool.false_eq_true, if_false]
      apply spec_bind (collection_offsets_loop_refines parts (alloc.vec.Vec.new _) leading 0#usize
        (by simp) (by simp; omega) (by simpa [front, hFixed, collectionLeading] using totalBound))
      intro header headerPost
      apply spec_bind (collection_bodies_loop2_refines parts header 0#usize (by simp)
        (by simp at headerPost ⊢; omega))
      intro output outputPost
      simp only [UScalar.ofNatCore_val_eq, List.drop_zero] at outputPost headerPost
      have bytesEq : bytesToSpec output.val = bytesToSpec header.val ++ bytesToSpec (collectionBodyBytes parts.val) := by
        simp [outputPost, bytesToSpec]
      simp only [hFixed, collectionLeading, Bool.false_eq_true, if_false] at totalBound
      simp only [collectionLeading, Bool.false_eq_true, if_false, spec_ok]
      rw [if_neg (Nat.not_le.mpr totalBound)]
      change bytesToSpec output.val = _
      rw [bytesEq, headerPost.2, front]
      simp [bytesToSpec]
    · have room : collectionBodySize parts.val ≤ Usize.max := by
        simp only [hFixed, collectionLeading, if_true, Nat.zero_add] at totalBound
        scalar_tac
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok, if_true]
      apply spec_bind (collection_bodies_loop_refines parts (alloc.vec.Vec.new _) 0#usize
        (by simp) (by simpa using room))
      intro output outputPost
      simp only [UScalar.ofNatCore_val_eq, List.drop_zero, List.nil_append] at outputPost
      simp only [hFixed, collectionLeading, if_true, Nat.zero_add] at totalBound
      simp [collectionLeading, Nat.not_le.mpr totalBound, codecEncodingAgrees, outputPost]

end NyxSszVerification
