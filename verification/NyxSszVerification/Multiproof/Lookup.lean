import NyxSszVerification.Multiproof.Cut
import NyxSszVerification.Merkle

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace NyxSszVerification

def frontierNodes (indices : List U128) (nodes : List RustNode) : List (Nat × Ssz.Bytes) :=
  (indices.map UScalar.val).zip (proofNodes nodes)

@[simp] theorem frontierNodes_length (indices : List U128) (nodes : List RustNode)
    (sized : nodes.length = indices.length) :
    (frontierNodes indices nodes).length = indices.length := by simp [frontierNodes, proofNodes, sized]

theorem frontierNodes_at (indices : List U128) (nodes : List RustNode) (offset : Nat)
    (left : offset < indices.length) (right : offset < nodes.length) :
    (frontierNodes indices nodes)[offset]'(by simp [frontierNodes, proofNodes]; omega) =
      (indices[offset].val, bytesToSpec nodes[offset].val) := by simp [frontierNodes, proofNodes]

@[step] theorem multiproof_node_at_loop_refines (indices : Slice U128) (nodes : Slice RustNode)
    (index : U128) (offset : Usize) (sized : nodes.val.length = indices.val.length)
    (within : offset.val ≤ indices.val.length) :
    NyxSszRust.multiproof.node_at_loop indices nodes index offset ⦃ actual =>
      actual.map (fun node => bytesToSpec node.val) =
        Ssz.nodeAt ((frontierNodes indices.val nodes.val).drop offset.val) index.val ⦄ := by
  let source := frontierNodes indices.val nodes.val
  have sourceLength : source.length = indices.val.length := frontierNodes_length _ _ sized
  unfold NyxSszRust.multiproof.node_at_loop
  apply loop_total
    (invariant := fun current : Usize => current.val ≤ indices.val.length ∧
      Ssz.nodeAt (source.drop current.val) index.val = Ssz.nodeAt (source.drop offset.val) index.val)
    (measure := fun current => indices.val.length - current.val)
  · intro current invariant
    obtain ⟨bounded, same⟩ := invariant
    unfold NyxSszRust.multiproof.node_at_loop.body
    by_cases active : current.val < indices.val.length
    · have nodeActive : current.val < nodes.val.length := by omega
      have entry : source[current.val]'(by omega) =
          (indices.val[current.val].val, bytesToSpec nodes.val[current.val].val) :=
        frontierNodes_at _ _ _ active nodeActive
      rw [List.drop_eq_getElem_cons (by omega : current.val < source.length), entry] at same
      step*
      all_goals simp_all [Ssz.nodeAt, gindex_word_eq, source]
      all_goals omega
    · have endEq : current.val = indices.val.length := by omega
      have empty : source.drop current.val = [] := List.drop_eq_nil_of_le (by omega)
      rw [empty] at same
      step*
      simpa only [Ssz.nodeAt, List.find?_nil, Option.map_none] using same
  · exact ⟨within, rfl⟩

@[step] theorem multiproof_node_at_refines (indices : Slice U128) (nodes : Slice RustNode)
    (index : U128) (sized : nodes.val.length = indices.val.length) :
    NyxSszRust.multiproof.node_at indices nodes index ⦃ actual =>
      actual.map (fun node => bytesToSpec node.val) =
        Ssz.nodeAt (frontierNodes indices.val nodes.val) index.val ⦄ := by
  unfold NyxSszRust.multiproof.node_at
  simpa using multiproof_node_at_loop_refines indices nodes index 0#usize sized (by simp)

end NyxSszVerification
