import NyxSszVerification.Collection.BasicPacking
import NyxSszVerification.Collection.RootReference
import NyxSszVerification.Collection.RootFinish
import NyxSszVerification.Collection.Parts

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxHeartbeats 2000000

namespace NyxSszVerification

theorem collection_root_each_count (shape : Ssz.Desc) (values : List Ssz.Value)
    (roots : List Ssz.Bytes) (read : collectionRootEach shape values = .ok roots) :
    roots.length = values.length := by
  induction values generalizing roots with
  | nil => simp at read; simp [← read]
  | cons value values ih =>
    cases head : Ssz.hashTreeRoot shape value with
    | error fault => simp [head, Bind.bind, Except.bind] at read
    | ok root =>
      cases tail : collectionRootEach shape values with
      | error fault => simp [head, tail, Bind.bind, Except.bind] at read
      | ok rest =>
        simp [head, tail, Bind.bind, Except.bind, Pure.pure, Except.pure] at read
        subst roots
        simp [ih rest tail]

@[step] theorem collection_root_sequence_refines {T State : Type}
    (child : NyxSszRust.codec.Ssz T State) (shape : Ssz.Desc) (observe : T → Ssz.Value)
    (law : CodecLaw child shape observe) (valid : shape.wellFormed = .ok ())
    (values : Slice T) (positions : Usize) (mixLength : Bool)
    (within : values.val.length ≤ positions.val) :
    NyxSszRust.collection_tree.root_sequence child values positions mixLength ⦃ actual =>
      codecRootAgrees actual (collectionSequenceRoot shape (values.val.map observe) positions.val mixLength) ⦄ := by
  unfold NyxSszRust.collection_tree.root_sequence
  apply spec_bind (codec_is_basic_refines child shape law.declaration)
  intro actual basicEq
  rw [basicEq]
  by_cases basic : shape.isBasic = true
  · rw [if_pos basic]
    apply spec_bind (collection_encode_parts_refines child shape observe law valid values)
    intro partsResult partsAgrees
    cases partsResult with
    | Err kind =>
      cases encoded : Ssz.serializeEach shape (values.val.map observe) <;>
        simp_all [collectionPartsAgrees, collectionSequenceRoot, codecRootAgrees,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          Bind.bind, Except.bind]
    | Ok held =>
      cases held with
      | none =>
        cases encoded : Ssz.serializeEach shape (values.val.map observe) with
        | error fault => simp [collectionPartsAgrees, encoded] at partsAgrees
        | ok data =>
          simp only [encoded, collectionPartsAgrees] at partsAgrees
          exact False.elim (collection_basic_parts_native shape valid basic _ data encoded partsAgrees)
      | some parts =>
        have encoded : Ssz.serializeEach shape (values.val.map observe) =
            .ok (parts.val.map fun part => bytesToSpec part.val) := by
          cases encoded : Ssz.serializeEach shape (values.val.map observe) <;>
            simp_all [collectionPartsAgrees]
        have size := collection_basic_parts_bound shape basic _ parts.val encoded
        simp only [List.length_map] at size
        have widthBound := collection_basic_width_bound shape valid basic
        have bodyBound : collectionBodySize parts.val ≤ Usize.max * 32 := by
          rw [size]
          exact Nat.mul_le_mul values.property widthBound
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]
        apply spec_bind (collection_pack_parts_refines (alloc.vec.Vec.deref parts) bodyBound)
        intro chunks packed
        simp only [collection_deref_values] at packed
        apply spec_bind (collection_basic_capacity_refines child shape law.declaration valid basic positions)
        intro capacityResult capacityPost
        obtain ⟨capacity, same, capacityEq⟩ := capacityPost
        rw [same]
        simp only [bind_tc_ok]
        have chunkCount := congrArg _root_.Array.size packed
        simp only [_root_.List.size_toArray, proofNodes_length, Ssz.packBytes,
          _root_.Array.size_ofFn, bytesToSpec_size, collectionBodyBytes_length,
          Ssz.bytesPerChunk] at chunkCount
        have limit : chunks.val.length ≤ capacity.val := by
          have scaled := Nat.mul_le_mul_right shape.itemLength within
          rw [capacityEq, Ssz.chunksForBytes, Ssz.bytesPerChunk, chunkCount, size]
          exact Nat.div_le_div_right (by omega)
        have reference : collectionSequenceRoot shape (values.val.map observe) positions.val mixLength =
            (do let root ← Ssz.merkleizeBounded (proofNodes chunks.val).toArray (some capacity.val)
                return if mixLength then Ssz.mixIn root (Ssz.lengthWord values.val.length) else root) := by
          simp only [collectionSequenceRoot, basic, if_true, encoded, Bind.bind, Except.bind,
            Pure.pure, Except.pure, List.length_map, collection_pack_elements]
          rw [← capacityEq, ← packed]
        rw [reference]
        exact collection_root_finish (alloc.vec.Vec.deref chunks) capacity (Slice.len values) mixLength limit
  · rw [if_neg basic]
    apply spec_bind (collection_root_elements_refines child shape observe law valid values)
    intro rootsResult rootsAgrees
    cases rootsResult with
    | Err kind =>
      cases rooted : collectionRootEach shape (values.val.map observe) <;>
        simp_all [collectionRootsAgrees, collectionSequenceRoot, codecRootAgrees,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          Bind.bind, Except.bind]
    | Ok roots =>
      have rooted : collectionRootEach shape (values.val.map observe) = .ok (proofNodes roots.val) := by
        cases rooted : collectionRootEach shape (values.val.map observe) <;>
          simp_all [collectionRootsAgrees]
      have count := collection_root_each_count shape _ _ rooted
      simp only [proofNodes_length, List.length_map] at count
      have limit : roots.val.length ≤ positions.val := count.trans_le within
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]
      have reference : collectionSequenceRoot shape (values.val.map observe) positions.val mixLength =
          (do let root ← Ssz.merkleizeBounded (proofNodes roots.val).toArray (some positions.val)
              return if mixLength then Ssz.mixIn root (Ssz.lengthWord values.val.length) else root) := by
        simp [collectionSequenceRoot, basic, rooted, Bind.bind, Except.bind,
          Pure.pure, Except.pure]
      rw [reference]
      exact collection_root_finish (alloc.vec.Vec.deref roots) positions (Slice.len values) mixLength limit

end NyxSszVerification
