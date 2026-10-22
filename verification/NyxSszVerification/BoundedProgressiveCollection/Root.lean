import NyxSszVerification.ProgressiveCollection.Root
import NyxSszVerification.BoundedProgressiveCollection.Codec

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace NyxSszVerification

/-- The pinned root's Progressive layout ignores the context cap on the full value domain. -/
theorem bounded_progressive_collection_root_form (shape : Ssz.Desc) (limit : Nat)
    (values : List Ssz.Value) :
    Ssz.hashTreeRoot (.progressiveList shape (some limit)) (.seq values) =
      Ssz.hashTreeRoot (.progressiveList shape none) (.seq values) := by
  simp only [Ssz.hashTreeRoot, Ssz.Desc.nesting, Ssz.hashTreeRootAt, Ssz.merkleLayout]

theorem bounded_progressive_collection_root_refines {T State : Type} (limit : Usize)
    (child : NyxSszRust.codec.Ssz T State) (shape : Ssz.Desc) (observe : T → Ssz.Value)
    (law : CodecLaw child shape observe) (value : NyxSszRust.collections.BoundedProgressiveList T limit) :
    NyxSszRust.collections.BoundedProgressiveList.Insts.Nyx_sszCodecSszSequenceDecodeState.hash_tree_root child value
      ⦃ actual => codecRootAgrees actual
        (checkedHashTreeRoot (.progressiveList shape (some limit.val)) (.seq (value.values.val.map observe))) ⦄ := by
  unfold NyxSszRust.collections.BoundedProgressiveList.Insts.Nyx_sszCodecSszSequenceDecodeState.hash_tree_root
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
      NyxSszRust.collections.BoundedProgressiveList.as_slice, checkedHashTreeRoot,
      Ssz.Desc.wellFormed, valid, bounded_progressive_collection_root_form,
      progressive_collection_root_form, Bind.bind, Except.bind] using
        progressive_collection_root_sequence_refines child shape observe law valid
          (alloc.vec.Vec.deref value.values)

end NyxSszVerification
