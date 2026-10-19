import NyxSszVerification.Representation.Bytes
import NyxSszVerification.Merkle.Arithmetic

open Aeneas Aeneas.Std

namespace NyxSszVerification

abbrev RustNode := Array U8 32#usize

def proofNodes (nodes : List RustNode) : List Ssz.Bytes :=
  nodes.map fun node => bytesToSpec node.val

theorem node_check (node : RustNode) : Ssz.checkChunk (bytesToSpec node.val) = .ok () := by
  have width : (bytesToSpec node.val).size = 32 := by
    rw [bytesToSpec_array_size]
    scalar_tac
  simp [Ssz.checkChunk, Ssz.bytesPerChunk, width]

theorem proof_nodes_check (nodes : List RustNode) :
    Ssz.checkChunks (proofNodes nodes) = .ok () := by
  induction nodes with
  | nil => rfl
  | cons node rest ih =>
    simp only [proofNodes, List.map_cons, Ssz.checkChunks, node_check, Bind.bind, Except.bind]
    exact ih

end NyxSszVerification
