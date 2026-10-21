import NyxSszVerification.ContainerWire.Model
import NyxSszVerification.PackedRoots.Words

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxHeartbeats 2000000

namespace NyxSszVerification

@[step] theorem container_advance_size_refines (leading body length : Usize) (fixed : Bool) :
    NyxSszRust.container_wire.advance_size leading body fixed length ⦃ actual =>
      containerSizeAgrees actual
        (leading.val + if fixed then length.val else 4)
        (body.val + if fixed then 0 else length.val) ⦄ := by
  have maximum := usize_max_le_u64
  unfold NyxSszRust.container_wire.advance_size
  cases chosen : fixed
  all_goals simp only [Bool.false_eq_true, if_false, if_true, bind_tc_ok]
  all_goals step*
  all_goals simp_all [containerSizeAgrees]
  all_goals
    constructor <;> apply Nat.mod_eq_of_lt <;>
      rcases System.Platform.numBits_eq with platform | platform <;> simp_all <;> omega

@[step] theorem container_size_loop_refines (slots : Slice (Bool × alloc.vec.Vec U8))
    (leading body index : Usize) (within : index.val ≤ slots.val.length)
    (budget : leading.val + body.val < 4294967296) :
    NyxSszRust.container_wire.leading_and_body_loop slots leading body index ⦃ actual =>
      containerSizeAgrees actual
        (leading.val + containerHeadSize (slots.val.drop index.val))
        (body.val + containerBodySize (slots.val.drop index.val)) ⦄ := by
  let head := leading.val + containerHeadSize (slots.val.drop index.val)
  let tail := body.val + containerBodySize (slots.val.drop index.val)
  unfold NyxSszRust.container_wire.leading_and_body_loop
  apply loop_total
    (invariant := fun state : Usize × Usize × Usize =>
      state.2.2.val ≤ slots.val.length ∧ state.1.val + state.2.1.val < 4294967296 ∧
      state.1.val + containerHeadSize (slots.val.drop state.2.2.val) = head ∧
      state.2.1.val + containerBodySize (slots.val.drop state.2.2.val) = tail)
    (measure := fun state => slots.val.length - state.2.2.val)
  · rintro ⟨nextLeading, nextBody, nextIndex⟩ ⟨inside, bounded, headEq, tailEq⟩
    by_cases active : nextIndex.val < slots.val.length
    · have headStep := headEq
      have tailStep := tailEq
      rw [List.drop_eq_getElem_cons active] at headStep tailStep
      unfold NyxSszRust.container_wire.leading_and_body_loop.body
      step*
      rcases v with ⟨fixed, part⟩
      rw [← b_post2] at headStep tailStep
      simp only [containerHeadSize_cons, containerBodySize_cons] at headStep tailStep
      step*
      · rcases val with ⟨outLeading, outBody⟩
        cases r <;> simp_all [containerSizeAgrees]
        step*
        refine ⟨by scalar_tac, ?_, ?_, ?_, by scalar_tac⟩
        all_goals scalar_tac
      · cases r with
        | Ok pair => simp_all
        | Err error =>
          cases error <;> simp only [containerSizeAgrees] at r_post
          change 4294967296 ≤
            (nextLeading.val + if fixed then part.val.length else 4) +
            (nextBody.val + if fixed then 0 else part.val.length) at r_post
          have overflow : 4294967296 ≤ head + tail := by
            rw [← headStep, ← tailStep]
            omega
          have fault : r1 = NyxSszRust.error.CodecError.SizeOverflow := by
            have branch : cf = core.ops.control_flow.ControlFlow.Break residual := by assumption
            have same := branch.symm.trans cf_post
            have residualEq : residual = core.result.Result.Err NyxSszRust.error.CodecError.SizeOverflow := by
              injection same
            have errors := r1_post1.symm.trans residualEq
            injection errors
          rw [r1_post3, ← r1_post2, fault]
          exact overflow
    · unfold NyxSszRust.container_wire.leading_and_body_loop.body
      step*
      have atEnd : nextIndex.val = slots.val.length := by scalar_tac
      simp only [atEnd, List.drop_length, containerHeadSize_nil, containerBodySize_nil,
        Nat.add_zero] at headEq tailEq
      change containerSizeAgrees _ head tail
      simp [containerSizeAgrees, ← headEq, ← tailEq, bounded]
  · exact ⟨within, budget, rfl, rfl⟩

@[step] theorem container_size_refines (slots : Slice (Bool × alloc.vec.Vec U8)) :
    NyxSszRust.container_wire.leading_and_body slots ⦃ actual =>
      containerSizeAgrees actual (containerHeadSize slots.val) (containerBodySize slots.val) ⦄ := by
  simpa [NyxSszRust.container_wire.leading_and_body] using
    container_size_loop_refines slots 0#usize 0#usize 0#usize (by simp) (by simp)

end NyxSszVerification
