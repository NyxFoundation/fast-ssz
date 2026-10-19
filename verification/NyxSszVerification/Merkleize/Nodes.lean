import NyxSszVerification.Merkle.Nodes
import NyxSszVerification.Merkleize.Tree

open Aeneas Aeneas.Std

set_option maxRecDepth 4096
set_option maxHeartbeats 200000

namespace NyxSszVerification

@[simp] theorem proofNodes_length (nodes : List RustNode) :
    (proofNodes nodes).length = nodes.length := by simp [proofNodes]

def nodeTree (nodes : List RustNode) (depth : Nat) : Ssz.Bytes :=
  Ssz.subtreeRoot Ssz.combine depth (Ssz.padded Ssz.zeroChunk (proofNodes nodes).toArray)

@[simp] theorem nodeTree_empty (depth : Nat) :
    nodeTree [] depth = Ssz.zeroRoot Ssz.combine Ssz.zeroChunk depth := by
  have supply : Ssz.padded Ssz.zeroChunk #[] = fun _ => Ssz.zeroChunk := by
    funext position
    simp [Ssz.padded]
  change Ssz.subtreeRoot Ssz.combine depth (Ssz.padded Ssz.zeroChunk #[]) = _
  rw [supply]
  exact Ssz.subtreeRoot_const_zero Ssz.combine Ssz.zeroChunk depth

theorem nodeTree_take (nodes : List RustNode) (depth : Nat) :
    nodeTree (nodes.take (2 ^ depth)) depth = nodeTree nodes depth := by
  unfold nodeTree
  apply Ssz.subtreeRoot_congr
  intro position inside
  simp [proofNodes, Ssz.padded, inside]

theorem nodeTree_split (nodes : List RustNode) (depth : Nat) :
    nodeTree nodes (depth + 1) = Ssz.combine
      (nodeTree (nodes.take (2 ^ depth)) depth) (nodeTree (nodes.drop (2 ^ depth)) depth) := by
  rw [nodeTree_take]
  unfold nodeTree
  rw [Ssz.subtreeRoot]
  congr 1
  apply Ssz.subtreeRoot_congr
  intro position inside
  simp [proofNodes, Ssz.padded, List.getElem?_drop, Nat.add_comm]

theorem nodeTree_short (nodes : List RustNode) (depth : Nat) (short : nodes.length ≤ 2 ^ depth) :
    nodeTree nodes (depth + 1) =
      Ssz.combine (nodeTree nodes depth) (Ssz.zeroRoot Ssz.combine Ssz.zeroChunk depth) := by
  rw [nodeTree_split, nodeTree_take]
  have empty : nodes.drop (2 ^ depth) = [] := List.drop_eq_nil_iff.mpr short
  simp [empty]

theorem subtreeAt_nodeTree (nodes : List RustNode) (depth : Nat) :
    Ssz.subtreeAt (proofNodes nodes).toArray depth 0 = nodeTree nodes depth := by
  simpa only [nodeTree, Nat.zero_add] using subtreeAt_recursive (proofNodes nodes).toArray depth 0

end NyxSszVerification
