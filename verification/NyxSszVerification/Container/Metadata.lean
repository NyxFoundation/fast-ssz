import NyxSszRust.Container
import NyxSszVerification.TypeInfo.Width
import NyxSszVerification.Sequence.Vector

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace NyxSszVerification

abbrev WidthMetadata := core.result.Result (Option Usize) NyxSszRust.error.CodecError

/-- The child metadata describes exactly the supplied fields, including natural overflow. -/
def containerMetadata (widths : List WidthMetadata) (fields : List Ssz.Desc) : Prop :=
  widths.length = fields.length ∧
    ∀ index (left : index < widths.length) (right : index < fields.length),
      codecWidthAgrees widths[index] fields[index].fixedSize

def variableFields (fields : List Ssz.Desc) : Bool :=
  fields.any fun field => field.fixedSize.isNone

@[simp] theorem variableFields_nil : variableFields [] = false := rfl

@[simp] theorem variableFields_cons (field : Ssz.Desc) (fields : List Ssz.Desc) :
    variableFields (field :: fields) = (field.fixedSize.isNone || variableFields fields) := by
  simp [variableFields]

theorem metadata_at (widths : List WidthMetadata) (fields : List Ssz.Desc)
    (truth : containerMetadata widths fields) (index : Nat) (inside : index < widths.length) :
    codecWidthAgrees widths[index] (fields[index]'(by rw [← truth.1]; exact inside)).fixedSize :=
  truth.2 index inside (by rw [← truth.1]; exact inside)

theorem metadata_fixed (actual : WidthMetadata) (width : Nat)
    (agrees : codecWidthAgrees actual (some width)) (bounded : width ≤ Usize.max) :
    ∃ child, actual = .Ok (some child) ∧ child.val = width := by
  cases actual with
  | Ok child =>
    cases child with
    | none => simp [codecWidthAgrees] at agrees
    | some child => exact ⟨child, rfl, agrees⟩
  | Err error =>
    cases error <;> simp_all [codecWidthAgrees]
    omega

theorem variable_drop_next (fields : List Ssz.Desc) (index : Nat)
    (inside : index < fields.length) :
    variableFields (fields.drop index) =
      (fields[index].fixedSize.isNone || variableFields (fields.drop (index + 1))) := by
  rw [List.drop_eq_getElem_cons inside, variableFields_cons]

@[step] theorem has_variable_loop_refines
    (widths : Slice WidthMetadata) (fields : List Ssz.Desc)
    (truth : containerMetadata widths.val fields) (index : Usize)
    (within : index.val ≤ widths.val.length) :
    NyxSszRust.container.has_variable_loop widths index ⦃ actual =>
      actual = variableFields (fields.drop index.val) ⦄ := by
  let expected := variableFields (fields.drop index.val)
  unfold NyxSszRust.container.has_variable_loop
  apply loop_total
    (invariant := fun next : Usize => next.val ≤ widths.val.length ∧
      variableFields (fields.drop next.val) = expected)
    (measure := fun next => widths.val.length - next.val)
  · intro next ⟨bounded, model⟩
    by_cases active : next.val < widths.val.length
    · have fieldInside : next.val < fields.length := by rw [← truth.1]; exact active
      have agrees := metadata_at widths.val fields truth next.val active
      have equation := variable_drop_next fields next.val fieldInside
      unfold NyxSszRust.container.has_variable_loop.body
      step*
      all_goals cases fixed : fields[next.val].fixedSize
      all_goals simp only [fixed, Option.isNone_none, Option.isNone_some,
        Bool.true_or, Bool.false_or] at equation
      all_goals grind [codecWidthAgrees]
    · unfold NyxSszRust.container.has_variable_loop.body
      step*
      have ending : next.val = fields.length := by have := truth.1; omega
      simpa [ending] using model.symm
  · exact ⟨within, rfl⟩

@[step] theorem has_variable_refines (widths : Slice WidthMetadata) (fields : List Ssz.Desc)
    (truth : containerMetadata widths.val fields) :
    NyxSszRust.container.has_variable widths ⦃ actual => actual = variableFields fields ⦄ := by
  unfold NyxSszRust.container.has_variable
  step*
  simpa using actual_post

end NyxSszVerification
