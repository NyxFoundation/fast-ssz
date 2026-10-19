import NyxSszVerification.Codec.Law

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace NyxSszVerification

@[step] theorem type_info_fixed_size_refines (declaration : NyxSszRust.type_info.TypeDescriptor) :
    NyxSszRust.type_info.fixed_size declaration ⦃ actual =>
      codecWidthAgrees actual (typeDescriptorToSpec declaration).fixedSize ⦄ := by
  cases h : declaration <;>
    simp_all [NyxSszRust.type_info.fixed_size, typeDescriptorToSpec, codecWidthAgrees, Ssz.Desc.fixedSize]

@[step] theorem type_info_is_basic_refines (declaration : NyxSszRust.type_info.TypeDescriptor) :
    NyxSszRust.type_info.is_basic declaration ⦃ actual =>
      actual = (typeDescriptorToSpec declaration).isBasic ⦄ := by
  cases h : declaration <;>
    simp_all [NyxSszRust.type_info.is_basic, typeDescriptorToSpec, Ssz.Desc.isBasic]

@[step] theorem type_info_is_compatible_refines
    (left right : NyxSszRust.type_info.TypeDescriptor) :
    NyxSszRust.type_info.is_compatible left right ⦃ actual =>
      actual = Ssz.isCompatible (typeDescriptorToSpec left) (typeDescriptorToSpec right) ⦄ := by
  cases hl : left <;> cases hr : right <;>
    simp_all [NyxSszRust.type_info.is_compatible, typeDescriptorToSpec,
      Ssz.isCompatible, Ssz.compatibleAt, Ssz.Desc.nesting, Ssz.Desc.byteSequence, BEq.beq, Ssz.Desc.beq]
  exact ⟨fun equality => congrArg UScalar.val equality, UScalar.eq_of_val_eq⟩

@[step] theorem type_info_validate_refines (declaration : NyxSszRust.type_info.TypeDescriptor) :
    NyxSszRust.type_info.validate declaration ⦃ actual =>
      codecValidityAgrees actual (typeDescriptorToSpec declaration).wellFormed ⦄ := by
  cases h : declaration with
  | Boolean => simp [NyxSszRust.type_info.validate, typeDescriptorToSpec, Ssz.Desc.wellFormed, codecValidityAgrees]
  | Uint width =>
    simp only [NyxSszRust.type_info.validate, typeDescriptorToSpec]
    split <;> simp_all [Ssz.Desc.wellFormed, codecValidityAgrees, codecFaultAgrees]

end NyxSszVerification
