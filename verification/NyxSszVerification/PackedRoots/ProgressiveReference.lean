import NyxSszVerification.PackedRoots.Reference

open Aeneas Aeneas.Std

namespace NyxSszVerification

/-- The byte-root API validates its optional bound before rooting the complete uint8
sequence. This explicit composition is intentional: the pinned upstream root ignores
progressive bounds. Neither the upstream root nor the generic CodecLaw is changed. -/
def checkedProgressiveByteRoot (limit : Option Nat) (bytes : List U8) : Except Ssz.Err Ssz.Bytes := do
  let values := byteValues bytes
  Ssz.boundCheck limit values.length
  checkedHashTreeRoot (.progressiveList (.uint 1) limit) (.seq values)

/-- The bit-root API validates the complete Boolean observation's length before the
unchanged upstream root. A view uses this same wrapper, with its full widened count
represented by the observation's natural-number size, never a narrowed usize. -/
def checkedProgressiveBitRoot (limit : Option Nat) (bits : _root_.Array Bool) : Except Ssz.Err Ssz.Bytes := do
  Ssz.boundCheck limit bits.size
  checkedHashTreeRoot (.progressiveBitList limit) (.bits bits)

end NyxSszVerification
