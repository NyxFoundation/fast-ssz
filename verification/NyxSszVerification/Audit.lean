import Lean
import NyxSszRust
import NyxSszVerification
import NyxSszVerification.ContractAudit

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

/-- A trait instance must prove the registered law for that exact dictionary. -/
elab "check_trait_contract " target:ident " against " contract:ident " via " claim:ident : command => do
  unless contract.getId == ``NyxSszVerification.CodecLaw do
    throwError "unsupported trait correctness law"
  let targetName := target.getId
  match ← getConstInfo targetName with
  | .defnInfo _ => pure ()
  | _ => throwError "trait dictionary must be concretely extracted"
  let claimInfo ← getConstInfo claim.getId
  match claimInfo with
  | .thmInfo _ => pure ()
  | _ => throwError "trait contract claim is not a theorem"
  liftTermElabM do
    NyxSszContractAudit.checkContractType targetName contract.getId claimInfo.type
