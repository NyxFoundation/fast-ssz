import NyxSszVerification.Codec.Law
import NyxSszVerification.Bitfield.Count

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace NyxSszVerification

theorem codec_width_none (actual : core.result.Result (Option Usize) NyxSszRust.error.CodecError)
    (agrees : codecWidthAgrees actual none) : actual = .Ok none := by
  cases actual with
  | Ok width => cases width <;> simp_all [codecWidthAgrees]
  | Err error => cases error <;> simp_all [codecWidthAgrees]

@[step] theorem type_info_fixed_size_refines (declaration : NyxSszRust.type_info.TypeDescriptor) :
    NyxSszRust.type_info.fixed_size declaration ⦃ actual =>
      codecWidthAgrees actual (typeDescriptorToSpec declaration).fixedSize ⦄ := by
  induction declaration with
  | Boolean => simp [NyxSszRust.type_info.fixed_size, typeDescriptorToSpec, Ssz.Desc.fixedSize, codecWidthAgrees]
  | Uint width => simp [NyxSszRust.type_info.fixed_size, typeDescriptorToSpec, Ssz.Desc.fixedSize, codecWidthAgrees]
  | BitVector count =>
    unfold NyxSszRust.type_info.fixed_size
    step*
    simp_all [typeDescriptorToSpec, Ssz.Desc.fixedSize, codecWidthAgrees]
  | BitList limit =>
    simp [NyxSszRust.type_info.fixed_size, typeDescriptorToSpec, Ssz.Desc.fixedSize, codecWidthAgrees]
  | ProgressiveBitList limit =>
    simp [NyxSszRust.type_info.fixed_size, typeDescriptorToSpec, Ssz.Desc.fixedSize, codecWidthAgrees]
  | List element limit ih =>
    simp [NyxSszRust.type_info.fixed_size, typeDescriptorToSpec, Ssz.Desc.fixedSize, codecWidthAgrees]
  | ProgressiveList element limit ih =>
    simp [NyxSszRust.type_info.fixed_size, typeDescriptorToSpec, Ssz.Desc.fixedSize, codecWidthAgrees]
  | Vector element count ih =>
    unfold NyxSszRust.type_info.fixed_size
    apply spec_bind ih
    intro actual agrees
    cases expectedEq : (typeDescriptorToSpec element).fixedSize with
    | none =>
      have same := codec_width_none actual (by simpa only [expectedEq] using agrees)
      rw [same]
      simp [typeDescriptorToSpec, Ssz.Desc.fixedSize, expectedEq, codecWidthAgrees]
    | some expected =>
      cases actual with
      | Ok childWidth =>
        cases childWidth with
        | none => simp [expectedEq, codecWidthAgrees] at agrees
        | some width =>
          have widthEq : width.val = expected := by simpa [expectedEq, codecWidthAgrees] using agrees
          step*
          all_goals simp_all [typeDescriptorToSpec, Ssz.Desc.fixedSize, codecWidthAgrees]
      | Err error =>
        cases error <;> simp only [expectedEq, codecWidthAgrees] at agrees
        step*
        · simp [typeDescriptorToSpec, Ssz.Desc.fixedSize, expectedEq, codecWidthAgrees]
        · have positive : 0 < count.val := by scalar_tac
          have growth := Nat.mul_le_mul_left expected (Nat.succ_le_iff.mpr positive)
          simp only [Nat.mul_one] at growth
          simp only [typeDescriptorToSpec, Ssz.Desc.fixedSize, expectedEq,
            Option.map_some, codecWidthAgrees]
          omega

end NyxSszVerification
