import FastSszVerification.Bitfield.Model
import Mathlib.Tactic.IntervalCases

open Aeneas Aeneas.Std

namespace FastSszVerification

theorem byte_bit_equiv (byte : U8) (position : Nat) (inside : position < 8) :
    ((byteToSpec byte >>> UInt8.ofNat position) &&& 1 == 1) =
      decide (((byte.bv >>> position) &&& 1#8) = 1#8) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  rw [← UInt8.toBitVec_inj]
  interval_cases position <;> rfl

theorem byte_bit_equiv_nat (byte : U8) (position : Nat) (inside : position < 8) :
    ((byteToSpec byte >>> UInt8.ofNat position) &&& 1 == 1) =
      decide ((byte.val >>> position) % 2 = 1) := by
  rw [byte_bit_equiv _ _ inside]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, ← BitVec.toNat_inj, BitVec.toNat_and,
    BitVec.toNat_ushiftRight, UScalar.bv_toNat, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod, Nat.and_one_is_mod]

theorem referenceBit_bv (bytes : List U8) (index : Nat)
    (inside : index / 8 < bytes.length) :
    referenceBit bytes index = decide (((bytes[index / 8]!.bv >>> (index % 8)) &&& 1#8) = 1#8) := by
  unfold referenceBit
  have byte : (bytesToSpec bytes)[index / 8]! = byteToSpec bytes[index / 8]! := by
    simp [bytesToSpec, inside]
  rw [byte, byte_bit_equiv _ _ (Nat.mod_lt _ (by decide))]

theorem byte_shift_zero (byte : U8) (position : Nat) (inside : position < 8) :
    (byteToSpec byte >>> UInt8.ofNat position = 0) ↔ (byte.bv >>> position = 0#8) := by
  rw [← UInt8.toBitVec_inj]
  interval_cases position <;> rfl

theorem bytesToSpec_at (bytes : List U8) (index : Nat) (inside : index < bytes.length) :
    (bytesToSpec bytes)[index]! = byteToSpec bytes[index] := by
  simp [bytesToSpec, inside]

theorem byte_shift_zero_nat (byte : U8) (position : Nat) (inside : position < 8) :
    (byteToSpec byte >>> UInt8.ofNat position = 0) ↔ (byte.val >>> position = 0) := by
  rw [byte_shift_zero _ _ inside]
  constructor
  · intro same
    have value := congrArg BitVec.toNat same
    simpa only [BitVec.toNat_ushiftRight, UScalar.bv_toNat, BitVec.toNat_zero] using value
  · intro same
    apply BitVec.eq_of_toNat_eq
    simpa only [BitVec.toNat_ushiftRight, UScalar.bv_toNat, BitVec.toNat_zero] using same

theorem bytesToSpec_at_default (bytes : List U8) (index : Nat) :
    (bytesToSpec bytes)[index]! = byteToSpec bytes[index]! := by
  by_cases inside : index < bytes.length
  · simp [bytesToSpec, inside]
  · simp [bytesToSpec, inside, byteToSpec]
    rfl

theorem bytesToSpec_getElem (bytes : List U8) (index : Nat)
    (inside : index < (bytesToSpec bytes).size) :
    (bytesToSpec bytes)[index]'inside = byteToSpec bytes[index]! := by
  have valid : index < bytes.length := by simpa using inside
  simp [bytesToSpec, valid]

end FastSszVerification
