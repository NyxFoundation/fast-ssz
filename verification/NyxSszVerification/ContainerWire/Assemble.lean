import NyxSszVerification.ContainerWire.Size
import NyxSszVerification.ContainerWire.Header
import NyxSszVerification.ContainerWire.Bodies

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxHeartbeats 2000000

namespace NyxSszVerification

/-- The unchanged reference budget check for paired internal-layout slots. -/
theorem container_assemble_form (slots : List (Bool × alloc.vec.Vec U8)) :
    Ssz.assemble (slots.map Prod.fst)
      (slots.map fun slot => bytesToSpec slot.2.val) =
    if containerHeadSize slots + containerBodySize slots ≥ 4294967296 then
      .error (.offsetOverflow (containerHeadSize slots + containerBodySize slots))
    else .ok (Ssz.headOf (containerHeadSize slots) (containerSlots slots) ++
      Ssz.bodiesOf (containerSlots slots)) := by
  simp [Ssz.assemble, container_slots_zip, containerHeadSize, containerBodySize,
    Ssz.bytesPerOffset, Bind.bind, Except.bind, Pure.pure, Except.pure,
    MonadExcept.throw, throwThe, MonadExceptOf.throw]

/-- Every native paired-slot slice refines raw reference assembly, not a value codec. -/
@[step] theorem container_assemble_refines (slots : Slice (Bool × alloc.vec.Vec U8)) :
    NyxSszRust.container_wire.assemble slots ⦃ actual =>
      codecEncodingAgrees actual (Ssz.assemble (slots.val.map Prod.fst)
        (slots.val.map fun slot => bytesToSpec slot.2.val)) ⦄ := by
  rw [container_assemble_form]
  unfold NyxSszRust.container_wire.assemble
  apply spec_bind (container_size_refines slots)
  intro actual correct
  cases actual with
  | Err kind =>
    cases kind <;> simp only [containerSizeAgrees] at correct
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      correct, codecEncodingAgrees, codecFaultAgrees]
  | Ok sizes =>
    obtain ⟨leading, body⟩ := sizes
    obtain ⟨leadingEq, bodyEq, bounded⟩ := correct
    have platform := Usize.bounds_eq
    have room : containerHeadSize slots.val + containerBodySize slots.val ≤ Usize.max := by
      scalar_tac
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]
    apply spec_bind (container_header_loop_refines slots leading (alloc.vec.Vec.new _) 0#usize
      (by simp) (by simp; omega) (by simpa [leadingEq] using bounded))
    intro header headerPost
    apply spec_bind (container_bodies_loop_refines slots header 0#usize (by simp)
      (by simp at headerPost ⊢; omega))
    intro output outputPost
    simp only [UScalar.ofNatCore_val_eq, List.drop_zero] at outputPost headerPost
    simp only [spec_ok]
    rw [if_neg (Nat.not_le.mpr bounded)]
    change bytesToSpec output.val = _
    rw [outputPost.2, headerPost.2, leadingEq]
    simp [bytesToSpec]

end NyxSszVerification
