import NyxSszVerification.Container.Metadata

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace NyxSszVerification

def headerOutcome (actual : core.result.Result Usize NyxSszRust.error.CodecError)
    (fields : List Ssz.Desc) (scope : Nat) (fault : NyxSszRust.error.CodecError) : Prop :=
  match actual with
  | .Ok width => width.val = Ssz.Desc.leadingWidth fields ∧ width.val ≤ scope
  | .Err error => error = fault ∧ scope < Ssz.Desc.leadingWidth fields

@[step] theorem header_width_loop_refines
    (widths : Slice WidthMetadata) (fields : List Ssz.Desc)
    (truth : containerMetadata widths.val fields) (scope : Usize)
    (fault : NyxSszRust.error.CodecError) (position index : Usize)
    (within : index.val ≤ widths.val.length) (bounded : position.val ≤ scope.val)
    (data : position.val + Ssz.Desc.leadingWidth (fields.drop index.val) =
      Ssz.Desc.leadingWidth fields) :
    NyxSszRust.container.header_width_loop widths scope fault position index ⦃ actual =>
      headerOutcome actual fields scope.val fault ⦄ := by
  unfold NyxSszRust.container.header_width_loop
  apply loop_total
    (invariant := fun state : Usize × Usize =>
      state.2.val ≤ widths.val.length ∧ state.1.val ≤ scope.val ∧
      state.1.val + Ssz.Desc.leadingWidth (fields.drop state.2.val) =
        Ssz.Desc.leadingWidth fields)
    (measure := fun state => widths.val.length - state.2.val)
  · rintro ⟨nextPosition, nextIndex⟩ ⟨inside, room, model⟩
    dsimp only at inside room model ⊢
    by_cases active : nextIndex.val < widths.val.length
    · have fieldInside : nextIndex.val < fields.length := by rw [← truth.1]; exact active
      have agrees := metadata_at widths.val fields truth nextIndex.val active
      rw [List.drop_eq_getElem_cons fieldInside, Ssz.Desc.leadingWidth] at model
      unfold NyxSszRust.container.header_width_loop.body
      step*
      all_goals try (cases o <;> step*)
      all_goals cases fixed : fields[nextIndex.val].fixedSize
      all_goals simp only [fixed, Option.getD_none, Option.getD_some,
        Ssz.bytesPerOffset] at model
      all_goals subst_vars
      all_goals simp_all [codecWidthAgrees, headerOutcome] <;> scalar_tac
    · have ending : nextIndex.val = fields.length := by have := truth.1; omega
      simp only [ending, List.drop_length, Ssz.Desc.leadingWidth, Nat.add_zero] at model
      unfold NyxSszRust.container.header_width_loop.body
      step*
      exact ⟨model, room⟩
  · exact ⟨within, bounded, data⟩

@[step] theorem header_width_refines
    (widths : Slice WidthMetadata) (fields : List Ssz.Desc)
    (truth : containerMetadata widths.val fields) (scope : Usize) (hasVariable : Bool) :
    NyxSszRust.container.header_width widths scope hasVariable ⦃ actual =>
      headerOutcome actual fields scope.val
        (if hasVariable then .ScopeTooSmall else .InvalidLength) ⦄ := by
  unfold NyxSszRust.container.header_width
  by_cases selected : hasVariable = true
  all_goals simp only [selected, ↓reduceIte, Bool.false_eq_true, bind_tc_ok]
  all_goals apply header_width_loop_refines widths fields truth scope _ 0#usize 0#usize
  all_goals simp

end NyxSszVerification
