import NyxSszRust.TypeInfo
import Ssz.Type.Valid

open Aeneas Aeneas.Std

namespace NyxSszVerification

/-- Preserve the complete declaration, including illegal integer widths. -/
def typeDescriptorToSpec : NyxSszRust.type_info.TypeDescriptor → Ssz.Desc
  | .Boolean => .bool
  | .Uint width => .uint width.val

end NyxSszVerification
