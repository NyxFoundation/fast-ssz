import Lean
import NyxSszRust
import NyxSszVerification

open Lean Elab Command
/-- Audit transitive axioms. -/
elab "audit_nyx_ssz" : command => do
  let environment ← getEnv
  for entry in environment.constants.toList do
    let declName := entry.1
    let publicName := (privateToUserName? declName).getD declName
    if (`NyxSszRust).isPrefixOf publicName || (`NyxSszVerification).isPrefixOf publicName then
      for assumption in (← Lean.collectAxioms declName) do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains assumption do
          throwError "{declName} depends on forbidden axiom {assumption}"

audit_nyx_ssz

/-- Validate proof registration. -/
elab "check_refinement " target:ident " via " claim:ident : command => do
  let targetName := target.getId
  let claimInfo ← getConstInfo claim.getId
  unless (← getEnv).contains targetName do
    throwError "unknown extraction target {targetName}"
  match claimInfo with
  | .thmInfo _ => pure ()
  | _ => throwError "{claim.getId} is not a theorem"
  unless claimInfo.type.getUsedConstants.contains targetName do
    throwError "{claim.getId} does not mention {targetName} in its statement"
