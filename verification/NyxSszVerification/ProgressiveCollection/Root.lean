import NyxSszVerification.ProgressiveCollection.RootReference
import NyxSszVerification.Collection.BasicPacking
import NyxSszVerification.Collection.Parts
import NyxSszVerification.Collection.LengthWord
import NyxSszVerification.PackedRoots.ProgressiveRoot
import NyxSszRust.ProgressiveCodec

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxHeartbeats 2000000

namespace NyxSszVerification

/-- The progressive tree and element-count mix-in use exactly the native nodes. -/
theorem progressive_collection_root_finish (chunks : Slice RustNode) (count : Usize) :
    (do
      let root ← NyxSszRust.merkle.merkleize_progressive chunks
      let wide ← lift (UScalar.cast .U128 count)
      let word ← NyxSszRust.tree_hash.hash_tree_root_u128 wide
      let result ← NyxSszRust.sha256.hash_pair root word
      RustM.ok (core.result.Result.Ok result)) ⦃ actual =>
        codecRootAgrees actual (.ok (Ssz.mixIn
          (Ssz.merkleizeProgressive (proofNodes chunks.val)) (Ssz.lengthWord count.val))) ⦄ := by
  apply spec_bind (merkleize_progressive_refines chunks)
  intro root rootPost
  step*
  simp_all [codecRootAgrees, Ssz.mixIn, collection_widen_usize]

@[step] theorem progressive_collection_root_sequence_refines {T State : Type}
    (child : NyxSszRust.codec.Ssz T State) (shape : Ssz.Desc) (observe : T → Ssz.Value)
    (law : CodecLaw child shape observe) (valid : shape.wellFormed = .ok ())
    (values : Slice T) :
    NyxSszRust.collection_tree.root_progressive_sequence child values ⦃ actual =>
      codecRootAgrees actual (progressiveCollectionRoot shape (values.val.map observe)) ⦄ := by
  unfold NyxSszRust.collection_tree.root_progressive_sequence
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
        simp_all [collectionPartsAgrees, progressiveCollectionRoot, codecRootAgrees,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          Bind.bind, Except.bind]
    | Ok parts =>
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
      have packedList := congrArg _root_.Array.toList packed
      simpa [progressiveCollectionRoot, basic, encoded, collection_pack_elements,
        ← packedList, Bind.bind, Except.bind, Pure.pure, Except.pure] using
          progressive_collection_root_finish (alloc.vec.Vec.deref chunks) (Slice.len values)
  · rw [if_neg basic]
    apply spec_bind (collection_root_elements_refines child shape observe law valid values)
    intro rootsResult rootsAgrees
    cases rootsResult with
    | Err kind =>
      cases rooted : collectionRootEach shape (values.val.map observe) <;>
        simp_all [collectionRootsAgrees, progressiveCollectionRoot, codecRootAgrees,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          Bind.bind, Except.bind]
    | Ok roots =>
      have rooted : collectionRootEach shape (values.val.map observe) = .ok (proofNodes roots.val) := by
        cases rooted : collectionRootEach shape (values.val.map observe) <;>
          simp_all [collectionRootsAgrees]
      simpa [core.result.Result.Insts.CoreOpsTry.branch, progressiveCollectionRoot,
        basic, rooted, Bind.bind, Except.bind, Pure.pure, Except.pure] using
          progressive_collection_root_finish (alloc.vec.Vec.deref roots) (Slice.len values)

theorem progressive_collection_root_refines {T State : Type}
    (child : NyxSszRust.codec.Ssz T State) (shape : Ssz.Desc) (observe : T → Ssz.Value)
    (law : CodecLaw child shape observe) (value : NyxSszRust.collections.ProgressiveList T) :
    NyxSszRust.collections.ProgressiveList.Insts.Nyx_sszCodecSszSequenceDecodeState.hash_tree_root child value
      ⦃ actual => codecRootAgrees actual
        (checkedHashTreeRoot (.progressiveList shape none) (.seq (value.values.val.map observe))) ⦄ := by
  unfold NyxSszRust.collections.ProgressiveList.Insts.Nyx_sszCodecSszSequenceDecodeState.hash_tree_root
  apply spec_bind (codec_validate_type_refines child shape law.declaration)
  intro actual agrees
  cases actual with
  | Err kind =>
    cases validity : shape.wellFormed <;>
      simp_all [codecValidityAgrees, checkedHashTreeRoot, codecRootAgrees, Ssz.Desc.wellFormed,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        Bind.bind, Except.bind]
  | Ok resultUnit =>
    cases resultUnit
    have valid : shape.wellFormed = .ok () := by
      cases validity : shape.wellFormed with
      | error fault => simp [validity, codecValidityAgrees] at agrees
      | ok resultUnit => cases resultUnit; rfl
    simpa [core.result.Result.Insts.CoreOpsTry.branch,
      NyxSszRust.collections.ProgressiveList.as_slice, checkedHashTreeRoot,
      Ssz.Desc.wellFormed, valid, progressive_collection_root_form, Bind.bind, Except.bind] using
        progressive_collection_root_sequence_refines child shape observe law valid
          (alloc.vec.Vec.deref value.values)

end NyxSszVerification
