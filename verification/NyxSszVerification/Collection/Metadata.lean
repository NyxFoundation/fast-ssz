import NyxSszRust.CollectionCodec
import NyxSszVerification.Codec.Metadata

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace NyxSszVerification

@[step] theorem collection_vector_type_refines {T State : Type} (count : Usize)
    (child : NyxSszRust.codec.Ssz T State) (shape : Ssz.Desc)
    (declared : child.TYPE ⦃ actual => typeDescriptorToSpec actual = shape ⦄) :
    NyxSszRust.collection_codec.vector_type count child ⦃ actual =>
      codecValidityAgrees actual (Ssz.Desc.vector shape count.val).wellFormed ⦄ := by
  unfold NyxSszRust.collection_codec.vector_type
  by_cases zero : count = 0#usize
  · simp [zero, Ssz.Desc.wellFormed, codecValidityAgrees, codecFaultAgrees,
      Bind.bind, Except.bind, MonadExcept.throw, throwThe, MonadExceptOf.throw]
  · have nonzero : count.val ≠ 0 := by scalar_tac
    simpa [zero, Ssz.Desc.wellFormed, nonzero, Bind.bind, Except.bind,
      Pure.pure, Except.pure] using codec_validate_type_refines child shape declared

@[step] theorem collection_vector_declaration_refines {T State : Type} (count : Usize)
    (child : NyxSszRust.codec.Ssz T State) (shape : Ssz.Desc)
    (declared : child.TYPE ⦃ actual => typeDescriptorToSpec actual = shape ⦄) :
    NyxSszRust.collections.Vector.Insts.Nyx_sszCodecSszSequenceDecodeState.TYPE count child
      ⦃ actual => typeDescriptorToSpec actual = .vector shape count.val ⦄ := by
  simp only [NyxSszRust.collections.Vector.Insts.Nyx_sszCodecSszSequenceDecodeState.TYPE]
  apply spec_bind declared
  intro actual correct
  simp [typeDescriptorToSpec, correct]

@[step] theorem collection_list_declaration_refines {T State : Type} (limit : Usize)
    (child : NyxSszRust.codec.Ssz T State) (shape : Ssz.Desc)
    (declared : child.TYPE ⦃ actual => typeDescriptorToSpec actual = shape ⦄) :
    NyxSszRust.collections.List.Insts.Nyx_sszCodecSszSequenceDecodeState.TYPE limit child
      ⦃ actual => typeDescriptorToSpec actual = .list shape limit.val ⦄ := by
  simp only [NyxSszRust.collections.List.Insts.Nyx_sszCodecSszSequenceDecodeState.TYPE]
  apply spec_bind declared
  intro actual correct
  simp [typeDescriptorToSpec, correct]

end NyxSszVerification
