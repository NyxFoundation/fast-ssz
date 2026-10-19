import NyxSszVerification.TypeInfo

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace NyxSszVerification

theorem codec_fixed_size_refines {T State : Type} (codecInst : NyxSszRust.codec.Ssz T State)
    (shape : Ssz.Desc)
    (declared : codecInst.TYPE ⦃ declaration => typeDescriptorToSpec declaration = shape ⦄) :
    NyxSszRust.codec.fixed_size codecInst ⦃ actual => codecWidthAgrees actual shape.fixedSize ⦄ := by
  unfold NyxSszRust.codec.fixed_size
  apply spec_bind declared
  intro declaration agrees
  rw [← agrees]
  exact type_info_fixed_size_refines declaration

theorem codec_is_basic_refines {T State : Type} (codecInst : NyxSszRust.codec.Ssz T State)
    (shape : Ssz.Desc)
    (declared : codecInst.TYPE ⦃ declaration => typeDescriptorToSpec declaration = shape ⦄) :
    NyxSszRust.codec.is_basic codecInst ⦃ actual => actual = shape.isBasic ⦄ := by
  unfold NyxSszRust.codec.is_basic
  apply spec_bind declared
  intro declaration agrees
  rw [← agrees]
  exact type_info_is_basic_refines declaration

theorem codec_validate_type_refines {T State : Type} (codecInst : NyxSszRust.codec.Ssz T State)
    (shape : Ssz.Desc)
    (declared : codecInst.TYPE ⦃ declaration => typeDescriptorToSpec declaration = shape ⦄) :
    NyxSszRust.codec.validate_type codecInst ⦃ actual => codecValidityAgrees actual shape.wellFormed ⦄ := by
  unfold NyxSszRust.codec.validate_type
  apply spec_bind declared
  intro declaration agrees
  rw [← agrees]
  exact type_info_validate_refines declaration

theorem codec_is_compatible_refines {Left LeftState Right RightState : Type}
    (left : NyxSszRust.codec.Ssz Left LeftState) (right : NyxSszRust.codec.Ssz Right RightState)
    (leftShape rightShape : Ssz.Desc)
    (leftDeclared : left.TYPE ⦃ declaration => typeDescriptorToSpec declaration = leftShape ⦄)
    (rightDeclared : right.TYPE ⦃ declaration => typeDescriptorToSpec declaration = rightShape ⦄) :
    NyxSszRust.codec.is_compatible left right ⦃ actual =>
      actual = Ssz.isCompatible leftShape rightShape ⦄ := by
  unfold NyxSszRust.codec.is_compatible
  apply spec_bind leftDeclared
  intro leftDeclaration leftAgrees
  apply spec_bind rightDeclared
  intro rightDeclaration rightAgrees
  rw [← leftAgrees, ← rightAgrees]
  exact type_info_is_compatible_refines leftDeclaration rightDeclaration

end NyxSszVerification
