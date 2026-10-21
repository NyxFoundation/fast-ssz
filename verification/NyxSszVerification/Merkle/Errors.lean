import NyxSszRust.Merkle
import Ssz.Codec.Error

namespace NyxSszVerification

def proofFaultAgrees : NyxSszRust.merkle.ProofError → Ssz.Err → Prop
  | .InvalidIndex, .notAGindex _ => True
  | .RootHasNoBranch, .rootHasNoBranch => True
  | .InvalidBranchLength, .branchLength _ _ => True
  | .EmptyRequest, .emptyRequest => True
  | .RepeatedIndex, .repeatedIndex => True
  | .NestedIndex, .nestedIndex _ => True
  | .InvalidLeafCount, .leafCount _ _ => True
  | .InvalidProofLength, .proofLength _ _ => True
  | _, _ => False

end NyxSszVerification
