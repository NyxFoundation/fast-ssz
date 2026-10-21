import NyxSszVerification.Collection.RootSequence
import NyxSszVerification.Collection.Metadata

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxHeartbeats 2000000

namespace NyxSszVerification

theorem collection_root_vector_refines {T State : Type} (count : Usize)
    (child : NyxSszRust.codec.Ssz T State) (shape : Ssz.Desc) (observe : T → Ssz.Value)
    (law : CodecLaw child shape observe) (value : NyxSszRust.collections.Vector T count) :
    NyxSszRust.collections.Vector.Insts.Nyx_sszCodecSszSequenceDecodeState.hash_tree_root child value
      ⦃ actual => codecRootAgrees actual
        (checkedHashTreeRoot (.vector shape count.val) (.seq (value.values.val.map observe))) ⦄ := by
  unfold NyxSszRust.collections.Vector.Insts.Nyx_sszCodecSszSequenceDecodeState.hash_tree_root
  apply spec_bind (collection_vector_type_refines count child shape law.declaration)
  intro actual agrees
  cases actual with
  | Err kind =>
    cases validity : (Ssz.Desc.vector shape count.val).wellFormed <;>
      simp_all [codecValidityAgrees, checkedHashTreeRoot, codecRootAgrees,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        Bind.bind, Except.bind]
  | Ok resultUnit =>
    cases resultUnit
    have parentValid : (Ssz.Desc.vector shape count.val).wellFormed = .ok () := by
      cases validity : (Ssz.Desc.vector shape count.val).wellFormed with
      | error fault => simp [validity, codecValidityAgrees] at agrees
      | ok resultUnit => cases resultUnit; rfl
    have positive : 0 < count.val := by
      by_contra bad
      have zero : count.val = 0 := by omega
      simp [Ssz.Desc.wellFormed, zero, Bind.bind, Except.bind,
        MonadExcept.throw, throwThe, MonadExceptOf.throw] at parentValid
    have valid : shape.wellFormed = .ok () := by
      simpa [Ssz.Desc.wellFormed, Nat.ne_of_gt positive, Bind.bind, Except.bind,
        Pure.pure, Except.pure] using parentValid
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok,
      NyxSszRust.collections.Vector.as_slice]
    by_cases length : value.values.val.length = count.val
    · have equal : Slice.len (alloc.vec.Vec.deref value.values) = count := by scalar_tac
      have form := collection_vector_root_form shape count.val (value.values.val.map observe)
        (by simpa only [List.length_map] using length)
      simpa [equal, checkedHashTreeRoot, parentValid, form, Bind.bind, Except.bind] using
        collection_root_sequence_refines child shape observe law valid
          (alloc.vec.Vec.deref value.values) count false (by simpa only [collection_deref_values] using Nat.le_of_eq length)
    · simp [bne_iff_ne, checkedHashTreeRoot, parentValid, Ssz.hashTreeRoot, Ssz.Desc.nesting,
        Ssz.hashTreeRootAt, Ssz.merkleLayout, length, codecRootAgrees, codecFaultAgrees,
        Bind.bind, Except.bind, MonadExcept.throw, throwThe, MonadExceptOf.throw]

theorem collection_root_list_refines {T State : Type} (limit : Usize)
    (child : NyxSszRust.codec.Ssz T State) (shape : Ssz.Desc) (observe : T → Ssz.Value)
    (law : CodecLaw child shape observe) (value : NyxSszRust.collections.List T limit) :
    NyxSszRust.collections.List.Insts.Nyx_sszCodecSszSequenceDecodeState.hash_tree_root child value
      ⦃ actual => codecRootAgrees actual
        (checkedHashTreeRoot (.list shape limit.val) (.seq (value.values.val.map observe))) ⦄ := by
  unfold NyxSszRust.collections.List.Insts.Nyx_sszCodecSszSequenceDecodeState.hash_tree_root
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
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok,
      NyxSszRust.collections.List.as_slice]
    by_cases length : value.values.val.length ≤ limit.val
    · have form := collection_list_root_form shape limit.val (value.values.val.map observe)
        (by simpa only [List.length_map] using length)
      simpa [Nat.not_lt.mpr length, checkedHashTreeRoot, Ssz.Desc.wellFormed, valid, form,
        Bind.bind, Except.bind] using
        collection_root_sequence_refines child shape observe law valid
          (alloc.vec.Vec.deref value.values) limit true length
    · simp [Nat.lt_of_not_ge length, checkedHashTreeRoot, Ssz.Desc.wellFormed, valid,
        Ssz.hashTreeRoot, Ssz.Desc.nesting, Ssz.hashTreeRootAt, Ssz.merkleLayout,
        codecRootAgrees, codecFaultAgrees, Bind.bind, Except.bind,
        MonadExcept.throw, throwThe, MonadExceptOf.throw]

end NyxSszVerification
