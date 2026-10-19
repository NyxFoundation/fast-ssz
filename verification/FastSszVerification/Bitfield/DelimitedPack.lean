import FastSszVerification.Bitfield.Model
import Mathlib.Tactic.IntervalCases

open Aeneas Aeneas.Std

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace FastSszVerification

theorem bitAt_push (bits : _root_.Array Bool) (position : Nat) :
    (bits.push true)[position]?.getD false =
      (bits[position]?.getD false || decide (position = bits.size)) := by
  by_cases ending : position = bits.size
  · simp [ending]
  · simp [ending, _root_.Array.getElem?_push]

theorem packByte_push_before (bits : _root_.Array Bool) (index : Nat)
    (before : (index + 1) * 8 ≤ bits.size) :
    Ssz.packByte (bits.push true) index = Ssz.packByte bits index := by
  have same (offset : Nat) (inside : offset < 8) :
      (bits.push true)[index * 8 + offset]?.getD false =
        bits[index * 8 + offset]?.getD false := by
    rw [bitAt_push]
    have different : index * 8 + offset ≠ bits.size := by omega
    simp [different]
  have first := same 0 (by decide)
  simp only [Nat.add_zero] at first
  simp [Ssz.packByte, same, first]

theorem packByte_push_last (bits : _root_.Array Bool) :
    Ssz.packByte (bits.push true) (bits.size / 8) =
      Ssz.packByte bits (bits.size / 8) ||| (1 <<< UInt8.ofNat (bits.size % 8)) := by
  have missing (offset : Nat) (past : bits.size % 8 ≤ offset) :
      bits[bits.size / 8 * 8 + offset]?.getD false = false := by
    have beyond : ¬bits.size / 8 * 8 + offset < bits.size := by omega
    simp [beyond]
  have ending (offset : Nat) :
      bits.size / 8 * 8 + offset = bits.size ↔ offset = bits.size % 8 := by omega
  have firstEnding : bits.size / 8 * 8 = bits.size ↔ bits.size % 8 = 0 := by omega
  have firstMissing (past : bits.size % 8 = 0) :
      bits[bits.size / 8 * 8]?.getD false = false := by
    simpa using missing 0 (by omega)
  have bounded : bits.size % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize remainder : bits.size % 8 = count at *
  interval_cases count <;> simp_all [Ssz.packByte, bitAt_push]

theorem packByte_past_end (bits : _root_.Array Bool) (index : Nat)
    (past : bits.size ≤ index * 8) : Ssz.packByte bits index = 0 := by
  have missing (offset : Nat) : bits[index * 8 + offset]?.getD false = false := by
    have beyond : ¬index * 8 + offset < bits.size := by omega
    simp [beyond]
  have first := missing 0
  simp only [Nat.add_zero] at first
  simp [Ssz.packByte, missing, first]

theorem packBitsDelimited_aligned (bits : _root_.Array Bool) (aligned : bits.size % 8 = 0) :
    Ssz.packBitsDelimited bits = (Ssz.packBits bits ((bits.size + 7) / 8)).push 1 := by
  apply _root_.Array.ext
  · simp [Ssz.packBitsDelimited, Ssz.packBits]
    omega
  intro index left right
  by_cases earlier : index < (bits.size + 7) / 8
  · have before : (index + 1) * 8 ≤ bits.size := by omega
    simp [Ssz.packBitsDelimited, Ssz.packBits, _root_.Array.getElem_push,
      earlier, packByte_push_before _ _ before]
  · have last : index = bits.size / 8 := by
      simp only [Ssz.packBitsDelimited, Ssz.packBits, _root_.Array.size_ofFn] at left
      omega
    subst index
    have past : bits.size ≤ bits.size / 8 * 8 := by omega
    simp [Ssz.packBitsDelimited, Ssz.packBits, _root_.Array.getElem_push,
      earlier, packByte_push_last,
      packByte_past_end _ _ past, aligned]

theorem packBitsDelimited_unaligned (bits : _root_.Array Bool) (unaligned : bits.size % 8 ≠ 0) :
    Ssz.packBitsDelimited bits = (Ssz.packBits bits ((bits.size + 7) / 8)).set!
      (bits.size / 8) (Ssz.packByte bits (bits.size / 8) ||| (1 <<< UInt8.ofNat (bits.size % 8))) := by
  apply _root_.Array.ext
  · simp [Ssz.packBitsDelimited, Ssz.packBits]
    omega
  intro index left right
  by_cases ending : index = bits.size / 8
  · subst index
    simp [Ssz.packBitsDelimited, Ssz.packBits, packByte_push_last]
  · have before : (index + 1) * 8 ≤ bits.size := by
      simp only [Ssz.packBitsDelimited, Ssz.packBits, _root_.Array.size_ofFn] at left
      omega
    have inside : index < (bits.size + 7) / 8 := by
      simpa [Ssz.packBits] using right
    simp [Ssz.packBitsDelimited, Ssz.packBits,
      inside, Ne.symm ending, packByte_push_before _ _ before]

theorem bytesToSpec_push (bytes : List U8) (byte : U8) :
    bytesToSpec (bytes ++ [byte]) = (bytesToSpec bytes).push (byteToSpec byte) := by
  simp [bytesToSpec]

theorem bytesToSpec_set (bytes : List U8) (index : Nat) (byte : U8) :
    bytesToSpec (bytes.set index byte) = (bytesToSpec bytes).set! index (byteToSpec byte) := by
  simp [bytesToSpec, List.map_set, List.setIfInBounds_toArray]

theorem byte_or_shift_one (left result : U8) (count : Nat) (inside : count < 8)
    (same : result.bv = left.bv ||| (1#8 <<< count)) :
    byteToSpec result = byteToSpec left ||| (1 <<< UInt8.ofNat count) := by
  interval_cases count <;> apply UInt8.toBitVec_inj.1 <;> simp [byteToSpec, same]

end FastSszVerification
