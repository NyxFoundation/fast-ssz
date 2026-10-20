import Lean
import NyxSszVerification.Codec.Law

open Lean Meta

namespace NyxSszContractAudit

private def constructorArguments (target contract : Name) (conclusion : Expr) : MetaM (Array Expr) := do
  unless conclusion.getAppFn.isConstOf contract do
    throwError "theorem does not establish an unconditional registered trait contract or generic child-law contract"
  let arguments := conclusion.getAppArgs
  unless arguments.size == 5 && arguments[2]!.getAppFn.isConstOf target do
    throwError "trait contract theorem certifies the wrong dictionary"
  let parameters := arguments[2]!.getAppArgs
  unless parameters.all Expr.isFVar && parameters.toList.eraseDups.length == parameters.size do
    throwError "generic dictionary arguments must be distinct universal parameters"
  return parameters

private def childPremises (parameters arguments : Array Expr) (contract : Name) :
    MetaM (Array Expr × Array Expr) := do
  let mut children := #[]
  let mut observations := #[]
  for parameter in parameters do
    let type ← inferType parameter
    unless ← isProp type do continue
    unless type.getAppFn.isConstOf contract do
      throwError "theorem does not establish an unconditional registered trait contract: unsupported premise"
    let fields := type.getAppArgs
    unless fields.size == 5 && fields[2]!.isFVar && arguments.contains fields[2]!
        && !children.contains fields[2]! do
      throwError "generic correctness premises must certify each exact child dictionary once"
    children := children.push fields[2]!
    for field in #[fields[3]!, fields[4]!] do
      unless field.isFVar && !arguments.contains field && !observations.contains field do
        throwError "generic child shapes and observations must be independent universal parameters"
      observations := observations.push field
  return (children, observations)

private def validateParameters (parameters arguments children observations : Array Expr) : MetaM Unit := do
  for parameter in parameters do
    let type ← inferType parameter
    if ← isProp type then continue
    unless arguments.contains parameter do
      unless observations.contains parameter do
        throwError "unused or constrained generic correctness parameter"
      continue
    let type ← whnf type
    if type.isSort then continue
    if type.getAppFn.isConstOf ``NyxSszRust.codec.Ssz then
      unless children.contains parameter do
        throwError "every generic child dictionary requires its own registered correctness law"
    else unless ← isDefEq type (mkConst ``Aeneas.Std.Usize) do
      throwError "unsupported generic dictionary parameter type"

/-- Accept only universal constructor parameters and laws for its exact child dictionaries. -/
def checkContractType (target contract : Name) (claim : Expr) : MetaM Unit :=
  forallTelescopeReducing claim fun parameters conclusion => do
    let arguments ← constructorArguments target contract conclusion
    let (children, observations) ← childPremises parameters arguments contract
    validateParameters parameters arguments children observations

end NyxSszContractAudit
