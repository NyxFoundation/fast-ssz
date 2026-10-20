import NyxSszRust.Gindex
import NyxSszVerification.Merkle.Errors
import NyxSszVerification.Merkle.Arithmetic

open Aeneas Aeneas.Std

namespace NyxSszVerification

/-- Only an unrepresentable natural-number result may cause index overflow. -/
def gindexResultAgrees {T : Type} (observe : T → Nat) (limit : Nat) :
    core.result.Result T NyxSszRust.merkle.ProofError → Except Ssz.Err Nat → Prop
  | .Ok value, .ok expected => observe value = expected
  | .Err .IndexOverflow, .ok expected => limit < expected
  | .Err error, .error fault => proofFaultAgrees error fault
  | _, _ => False

def gindexListAgrees : core.result.Result (alloc.vec.Vec U128) NyxSszRust.merkle.ProofError →
    Except Ssz.Err (List Nat) → Prop
  | .Ok values, .ok expected => values.val.map UScalar.val = expected
  | .Err error, .error fault => proofFaultAgrees error fault
  | _, _ => False

def gindexPath (index count : Nat) : List Nat :=
  (List.range count).map fun level => index >>> level

def gindexBranch (index count : Nat) : List Nat :=
  (gindexPath index count).map fun node => node ^^^ 1

end NyxSszVerification
