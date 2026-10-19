import NyxSszVerification.Representation.Bytes
import Ssz.Codec.Deserialize
import Ssz.Type.Valid

open Aeneas Aeneas.Std

namespace NyxSszVerification

def bitsToSpec (bits : List Bool) : _root_.Array Bool := bits.toArray

@[simp] theorem bitsToSpec_size (bits : List Bool) : (bitsToSpec bits).size = bits.length := by
  simp [bitsToSpec]

def packedPrefix (bits : List Bool) (count : Nat) : List UInt8 :=
  (List.range count).map fun index => Ssz.packByte (bitsToSpec bits) index

@[simp] theorem packedPrefix_zero (bits : List Bool) : packedPrefix bits 0 = [] := rfl

@[simp] theorem packedPrefix_length (bits : List Bool) (count : Nat) :
    (packedPrefix bits count).length = count := by
  simp [packedPrefix]

theorem packedPrefix_succ (bits : List Bool) (count : Nat) :
    packedPrefix bits (count + 1) =
      packedPrefix bits count ++ [Ssz.packByte (bitsToSpec bits) count] := by
  simp [packedPrefix, List.range_succ]

theorem packByte_drop (bits : List Bool) (index : Nat) :
    Ssz.packByte (bitsToSpec (bits.drop (index * 8))) 0 =
      Ssz.packByte (bitsToSpec bits) index := by
  simp [Ssz.packByte, bitsToSpec]

theorem packBits_prefix (bits : List Bool) (count : Nat) :
    (packedPrefix bits count).toArray = Ssz.packBits (bitsToSpec bits) count := by
  apply _root_.Array.ext
  · simp [packedPrefix, Ssz.packBits]
  intro index left right
  simp [packedPrefix, Ssz.packBits]

def referenceBit (bytes : List U8) (index : Nat) : Bool :=
  ((bytesToSpec bytes)[index / 8]! >>> UInt8.ofNat (index % 8)) &&& 1 == 1

def unpackedPrefix (bytes : List U8) (count : Nat) : List Bool :=
  (List.range count).map (referenceBit bytes)

@[simp] theorem unpackedPrefix_zero (bytes : List U8) : unpackedPrefix bytes 0 = [] := rfl

@[simp] theorem unpackedPrefix_length (bytes : List U8) (count : Nat) :
    (unpackedPrefix bytes count).length = count := by
  simp [unpackedPrefix]

theorem unpackedPrefix_succ (bytes : List U8) (count : Nat) :
    unpackedPrefix bytes (count + 1) = unpackedPrefix bytes count ++ [referenceBit bytes count] := by
  simp [unpackedPrefix, List.range_succ]

theorem unpackBits_prefix (bytes : List U8) (count : Nat) :
    (unpackedPrefix bytes count).toArray = Ssz.unpackBits (bytesToSpec bytes) count := by
  apply _root_.Array.ext
  · simp [unpackedPrefix, Ssz.unpackBits]
  intro index left right
  simp [unpackedPrefix, referenceBit, Ssz.unpackBits]

end NyxSszVerification
