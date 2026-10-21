import NyxSszRust.BitCodec
import NyxSszVerification.ProgressiveBits
import NyxSszVerification.PackedRoots.ViewPacking
import NyxSszVerification.Codec.Law

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace NyxSszVerification

/-- Logical interpretation on the full extracted domain, including malformed storage. -/
def ownedVectorCount (bytes : List U8) (n : Nat) : Nat :=
  if bytes.isEmpty then 0 else (bytes.length - 1) * 8 + if n % 8 = 0 then 8 else n % 8

def ownedVectorBits (bytes : List U8) (n : Nat) : _root_.Array Bool :=
  Ssz.unpackBits (bytesToSpec bytes) (ownedVectorCount bytes n)

def ownedListBits (bytes : List U8) : _root_.Array Bool :=
  Ssz.unpackBits (bytesToSpec bytes) (delimitedLength bytes)

def observeOwnedVector {N : Usize} (value : NyxSszRust.bitcollections.BitVector N) : Ssz.Value :=
  .bits (ownedVectorBits value.encoded.val N.val)

def observeOwnedList {MAX : Usize} (value : NyxSszRust.bitcollections.BitList MAX) : Ssz.Value :=
  .bits (ownedListBits value.encoded.val)

def observeOwnedProgressive (value : NyxSszRust.bitcollections.ProgressiveBitList) : Ssz.Value :=
  .bits (ownedListBits value.encoded.val)

/-- Canonicality is an exact checked-decoder guarantee, not an assumption on arbitrary values. -/
def canonicalOwnedVector (bytes : List U8) (n : Nat) : Prop :=
  0 < n ∧ bytes.length = (n + 7) / 8 ∧
    checkedDeserialize (.bitVector n) (bytesToSpec bytes) = .ok (.bits (ownedVectorBits bytes n))

def canonicalOwnedList (bytes : List U8) (limit : Option Nat) : Prop :=
  (0 < bytes.length ∧ (bytesToSpec bytes)[bytes.length - 1]! ≠ 0) ∧
    checkedDeserialize (.progressiveBitList limit) (bytesToSpec bytes) = .ok (.bits (ownedListBits bytes))

end NyxSszVerification
