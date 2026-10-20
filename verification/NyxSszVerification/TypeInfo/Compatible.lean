import NyxSszVerification.TypeInfo.Model

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace NyxSszVerification

theorem metadata_usize_eq (left right : Usize) : left = right ↔ left.val = right.val :=
  ⟨fun same => congrArg UScalar.val same, UScalar.eq_of_val_eq⟩

theorem type_info_compatible_exact (left right : NyxSszRust.type_info.TypeDescriptor) :
    NyxSszRust.type_info.is_compatible left right = RustM.ok (declarationCompatible left right) := by
  induction left generalizing right <;> cases right <;>
    simp_all [NyxSszRust.type_info.is_compatible, declarationCompatible,
      metadata_usize_eq, Bool.beq_eq_decide_eq]
  all_goals split <;> simp_all

theorem declaration_nesting_positive (declaration : NyxSszRust.type_info.TypeDescriptor) :
    0 < (typeDescriptorToSpec declaration).nesting := by
  cases h : declaration <;> simp [typeDescriptorToSpec, Ssz.Desc.nesting]

theorem declaration_equal_compatible (left right : NyxSszRust.type_info.TypeDescriptor)
    (same : Ssz.Desc.beq (typeDescriptorToSpec left) (typeDescriptorToSpec right) = true) :
    declarationCompatible left right = true := by
  induction left generalizing right <;> cases right <;>
    simp_all [typeDescriptorToSpec, Ssz.Desc.beq, declarationCompatible]

def declarationByteElement : NyxSszRust.type_info.TypeDescriptor → Bool
  | .Uint width => width.val == 1
  | _ => false

theorem declaration_byte_vector (element : NyxSszRust.type_info.TypeDescriptor) (count : Nat) :
    (Ssz.Desc.vector (typeDescriptorToSpec element) count).byteSequence =
      if declarationByteElement element then some (.asVector count) else none := by
  cases element <;> simp [typeDescriptorToSpec, Ssz.Desc.byteSequence, declarationByteElement]
  split <;> simp_all

theorem declaration_byte_list (element : NyxSszRust.type_info.TypeDescriptor) (limit : Nat) :
    (Ssz.Desc.list (typeDescriptorToSpec element) limit).byteSequence =
      if declarationByteElement element then some (.asList limit) else none := by
  cases element <;> simp [typeDescriptorToSpec, Ssz.Desc.byteSequence, declarationByteElement]
  split <;> simp_all

theorem byte_element_compatible_left (left right : NyxSszRust.type_info.TypeDescriptor)
    (byte : declarationByteElement left = true) :
    declarationCompatible left right = declarationByteElement right := by
  cases left <;> cases right <;>
    simp_all [declarationCompatible, declarationByteElement, Bool.beq_comm]

theorem byte_element_compatible_right (left right : NyxSszRust.type_info.TypeDescriptor)
    (byte : declarationByteElement right = true) :
    declarationCompatible left right = declarationByteElement left := by
  cases left <;> cases right <;>
    simp_all [declarationCompatible, declarationByteElement]

theorem metadata_byte_vector_beq (left right : Nat) :
    (Ssz.ByteShape.asVector left == Ssz.ByteShape.asVector right) = (left == right) := by
  by_cases same : left = right <;> simp [same]

theorem metadata_byte_list_beq (left right : Nat) :
    (Ssz.ByteShape.asList left == Ssz.ByteShape.asList right) = (left == right) := by
  by_cases same : left = right <;> simp [same]

theorem declaration_compatible_at (left right : NyxSszRust.type_info.TypeDescriptor) (budget : Nat)
    (enough : (typeDescriptorToSpec left).nesting ≤ budget) :
    Ssz.compatibleAt budget (typeDescriptorToSpec left) (typeDescriptorToSpec right) =
      declarationCompatible left right := by
  induction left generalizing right budget
  all_goals
    cases budget with
    | zero => simp_all [typeDescriptorToSpec, Ssz.Desc.nesting]
    | succ fuel =>
      unfold Ssz.compatibleAt
      split
      · exact (declaration_equal_compatible _ _ ‹_›).symm
      · cases right <;>
          simp_all only [typeDescriptorToSpec, Ssz.Desc.nesting]
        all_goals try simp only [declaration_byte_vector, declaration_byte_list]
        all_goals simp_all [Ssz.Desc.byteSequence, declarationCompatible, BEq.beq, Ssz.Desc.beq]
        all_goals split_ifs <;>
          simp_all [byte_element_compatible_left, byte_element_compatible_right,
            metadata_byte_vector_beq, metadata_byte_list_beq, Bool.beq_eq_decide_eq, Option.instBEq.beq]

@[step] theorem type_info_is_compatible_refines
    (left right : NyxSszRust.type_info.TypeDescriptor) :
    NyxSszRust.type_info.is_compatible left right ⦃ actual =>
      actual = Ssz.isCompatible (typeDescriptorToSpec left) (typeDescriptorToSpec right) ⦄ := by
  have enough : (typeDescriptorToSpec left).nesting ≤
      (typeDescriptorToSpec left).nesting + (typeDescriptorToSpec right).nesting := Nat.le_add_right _ _
  simp [type_info_compatible_exact, Ssz.isCompatible, declaration_compatible_at left right _ enough]

end NyxSszVerification
