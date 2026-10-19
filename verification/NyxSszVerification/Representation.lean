import Aeneas
import Ssz.Codec.Error

open Aeneas Aeneas.Std

namespace NyxSszVerification

/-- Preserve the eight bits. -/
def byteToSpec (byte : U8) : UInt8 := ⟨byte.bv⟩

/-- Preserve byte order and length. -/
def bytesToSpec (bytes : List U8) : Ssz.Bytes :=
  (bytes.map byteToSpec).toArray

theorem byteToSpec_injective : Function.Injective byteToSpec := by
  intro ⟨left⟩ ⟨right⟩ equal
  cases equal
  rfl

end NyxSszVerification
