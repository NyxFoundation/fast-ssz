import NyxSszVerification.Collection.Bodies
import NyxSszVerification.Merkle.Nodes
import NyxSszVerification.TreeHash.Basic

open Aeneas Aeneas.Std

set_option maxHeartbeats 2000000

namespace NyxSszVerification

/-- A complete node is a packing boundary, independent of the suffix. -/
theorem collection_pack_prefix (node data : Ssz.Bytes) (size : node.size = 32) :
    Ssz.packBytes (node ++ data) = #[node] ++ Ssz.packBytes data := by
  apply _root_.Array.ext
  · simp only [Ssz.packBytes, _root_.Array.size_ofFn, _root_.Array.size_append,
      _root_.Array.size_singleton, Ssz.bytesPerChunk, size]
    omega
  · intro index inLeft inRight
    cases index with
    | zero =>
      simp only [_root_.Array.getElem_append, _root_.Array.size_singleton,
        Nat.zero_lt_succ, ↓reduceDIte, _root_.Array.getElem_singleton]
      simp [Ssz.packBytes, Ssz.bytesPerChunk, _root_.Array.extract_append, size]
    | succ index =>
      have start : node.size ≤ (index + 1) * 32 := by omega
      have empty : node.extract ((index + 1) * 32) (((index + 1) * 32) + 32) = #[] := by
        simp [start]
      have first : (index + 1) * 32 - node.size = index * 32 := by omega
      have last : (index + 1) * 32 + 32 - node.size = index * 32 + 32 := by omega
      simp only [_root_.Array.getElem_append, _root_.Array.size_singleton,
        Nat.not_lt_zero, Nat.succ_lt_succ_iff, Nat.not_lt_zero, ↓reduceDIte,
        Nat.add_sub_cancel]
      simp only [Ssz.packBytes, _root_.Array.getElem_ofFn, Ssz.bytesPerChunk,
        _root_.Array.extract_append, empty, first, last, _root_.Array.empty_append]

/-- Complete typed nodes pack back to those same nodes, in order. -/
theorem collection_pack_complete (chunks : List RustNode) (data : List U8) :
    Ssz.packBytes (bytesToSpec (chunks.flatMap fun chunk => chunk.val) ++ bytesToSpec data) =
      (proofNodes chunks).toArray ++ Ssz.packBytes (bytesToSpec data) := by
  induction chunks with
  | nil => simp [proofNodes, bytesToSpec]
  | cons chunk rest ih =>
    have size : (bytesToSpec chunk.val).size = 32 := by simp
    have bytes : bytesToSpec ((chunk :: rest).flatMap fun chunk => chunk.val) ++ bytesToSpec data =
        bytesToSpec chunk.val ++
          (bytesToSpec (rest.flatMap fun chunk => chunk.val) ++ bytesToSpec data) := by
      simp [bytesToSpec]
    rw [bytes, collection_pack_prefix _ _ size, ih]
    apply _root_.Array.toList_inj.mp
    simp [proofNodes]

end NyxSszVerification
