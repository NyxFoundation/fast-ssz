import NyxSszVerification.Container.Reference

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace NyxSszVerification

def containerHeaderOutcome (actual : core.result.Result Usize NyxSszRust.error.CodecError)
    (fields : List Ssz.Desc) (scope : Nat) : Prop :=
  match actual with
  | .Ok header => header.val = Ssz.Desc.leadingWidth fields ∧
      Ssz.Desc.leadingWidth fields ≤ scope ∧ Ssz.structBudget fields scope = .ok ()
  | .Err error => ∃ fault, Ssz.structBudget fields scope = .error fault ∧ codecFaultAgrees error fault

@[step] theorem check_header_refines (widths : Slice WidthMetadata) (fields : List Ssz.Desc)
    (truth : containerMetadata widths.val fields) (scope : Usize) :
    NyxSszRust.container.check_header widths scope ⦃ actual =>
      containerHeaderOutcome actual fields scope.val ⦄ := by
  unfold NyxSszRust.container.check_header
  step*
  all_goals subst_vars
  all_goals simp_all [headerOutcome, containerHeaderOutcome, struct_budget_form, codecFaultAgrees]
  · omega
  · have different : scope.val ≠ Ssz.Desc.leadingWidth fields := by omega
    simp [different]
  · have different : scope.val ≠ Ssz.Desc.leadingWidth fields := by omega
    cases variableFields fields <;> simp [different]

end NyxSszVerification
