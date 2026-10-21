import NyxSszRust.TypeInfo
import Ssz.Type.Valid

open Aeneas Aeneas.Std

namespace NyxSszVerification

/-- Preserve the complete declaration, including illegal integer widths. -/
def typeDescriptorToSpec : NyxSszRust.type_info.TypeDescriptor → Ssz.Desc
  | .Boolean => .bool
  | .BitVector count => .bitVector count.val
  | .BitList limit => .bitList limit.val
  | .ProgressiveBitList limit => .progressiveBitList (limit.map fun cap => cap.val)
  | .Uint width => .uint width.val
  | .Vector element count => .vector (typeDescriptorToSpec element) count.val
  | .List element limit => .list (typeDescriptorToSpec element) limit.val
  | .ProgressiveList element limit =>
      .progressiveList (typeDescriptorToSpec element) (limit.map fun cap => cap.val)

/-- Compatibility preserves structure but ignores progressive capacity, as the tree does. -/
def declarationCompatible : NyxSszRust.type_info.TypeDescriptor →
    NyxSszRust.type_info.TypeDescriptor → Bool
  | .Boolean, .Boolean => true
  | .BitVector left, .BitVector right => left.val == right.val
  | .BitList left, .BitList right => left.val == right.val
  | .ProgressiveBitList _, .ProgressiveBitList _ => true
  | .Uint left, .Uint right => left.val == right.val
  | .Vector left n, .Vector right m => n.val == m.val && declarationCompatible left right
  | .List left n, .List right m => n.val == m.val && declarationCompatible left right
  | .ProgressiveList left _, .ProgressiveList right _ => declarationCompatible left right
  | _, _ => false

end NyxSszVerification
