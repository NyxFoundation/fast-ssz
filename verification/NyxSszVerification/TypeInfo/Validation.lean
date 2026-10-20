import NyxSszVerification.Codec.Law

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace NyxSszVerification

@[step] theorem type_info_is_basic_refines (declaration : NyxSszRust.type_info.TypeDescriptor) :
    NyxSszRust.type_info.is_basic declaration ⦃ actual =>
      actual = (typeDescriptorToSpec declaration).isBasic ⦄ := by
  cases h : declaration <;>
    simp_all [NyxSszRust.type_info.is_basic, typeDescriptorToSpec, Ssz.Desc.isBasic]

@[step] theorem type_info_validate_refines (declaration : NyxSszRust.type_info.TypeDescriptor) :
    NyxSszRust.type_info.validate declaration ⦃ actual =>
      codecValidityAgrees actual (typeDescriptorToSpec declaration).wellFormed ⦄ := by
  induction declaration with
  | Boolean =>
    simp [NyxSszRust.type_info.validate, typeDescriptorToSpec, Ssz.Desc.wellFormed, codecValidityAgrees]
  | Uint width =>
    simp only [NyxSszRust.type_info.validate, typeDescriptorToSpec]
    split <;> simp_all [Ssz.Desc.wellFormed, codecValidityAgrees, codecFaultAgrees]
  | Vector element count ih =>
    by_cases zero : count = 0#usize
    · simp [NyxSszRust.type_info.validate, zero, typeDescriptorToSpec, Ssz.Desc.wellFormed,
        codecValidityAgrees, codecFaultAgrees, Bind.bind, Except.bind,
        MonadExcept.throw, throwThe, MonadExceptOf.throw]
    · have nonzero : count.val ≠ 0 := by scalar_tac
      simpa [NyxSszRust.type_info.validate, zero, typeDescriptorToSpec, Ssz.Desc.wellFormed,
        nonzero, Bind.bind, Except.bind, Pure.pure, Except.pure] using ih
  | List element limit ih =>
    simpa [NyxSszRust.type_info.validate, typeDescriptorToSpec, Ssz.Desc.wellFormed] using ih
  | ProgressiveList element limit ih =>
    simpa [NyxSszRust.type_info.validate, typeDescriptorToSpec, Ssz.Desc.wellFormed] using ih

end NyxSszVerification
