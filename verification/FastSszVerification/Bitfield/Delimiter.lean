import FastSszRust.Bitfield
import FastSszVerification.Bitfield.Read
import FastSszVerification.Loop

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace FastSszVerification

@[step] theorem highest_bit_refines (byte : U8) :
    FastSszRust.bitfield.highest_bit byte ⦃ result =>
      result.val = Ssz.highestBit (byteToSpec byte) ∧ result.val < 8 ⦄ := by
  unfold FastSszRust.bitfield.highest_bit
  step*
  all_goals try clear i_post2 i1_post2
  all_goals try clear i2_post2 i3_post2
  all_goals try clear i4_post2 i5_post2
  all_goals try clear i6_post2 i7_post2
  all_goals try clear i8_post2 i9_post2
  all_goals try clear i10_post2 i11_post2
  all_goals try clear i12_post2 i13_post2
  all_goals
    simp only [Ssz.highestBit, byte_bit_equiv_nat byte 7 (by decide),
      byte_bit_equiv_nat byte 6 (by decide), byte_bit_equiv_nat byte 5 (by decide),
      byte_bit_equiv_nat byte 4 (by decide), byte_bit_equiv_nat byte 3 (by decide),
      byte_bit_equiv_nat byte 2 (by decide), byte_bit_equiv_nat byte 1 (by decide),
      decide_eq_true_eq]
    simp_all [UScalar.eq_equiv]

@[step] theorem all_zero_loop_refines (bytes : Slice U8) (index : Usize)
    (within : index.val ≤ bytes.val.length)
    (known : ∀ position, position < index.val → bytes.val[position]! = 0#u8) :
    FastSszRust.bitfield.all_zero_loop bytes index ⦃ result =>
      result ↔ ∀ position, position < bytes.val.length → bytes.val[position]! = 0#u8 ⦄ := by
  unfold FastSszRust.bitfield.all_zero_loop
  apply loop_total
    (invariant := fun current : Usize => current.val ≤ bytes.val.length ∧
      ∀ position, position < current.val → bytes.val[position]! = 0#u8)
    (measure := fun current => bytes.val.length - current.val)
  · intro current state
    rcases state with ⟨inBounds, data⟩
    unfold FastSszRust.bitfield.all_zero_loop.body
    step*
    all_goals simp_all
    all_goals grind
  · exact ⟨within, known⟩

@[simp] theorem byteToSpec_eq_zero (byte : U8) :
    byteToSpec byte = 0 ↔ byte = 0#u8 := by
  change byteToSpec byte = byteToSpec (0#u8) ↔ _
  exact byteToSpec_injective.eq_iff

theorem bytesToSpec_getElem_bang (bytes : List U8) (index : Nat) :
    (bytesToSpec bytes)[index]! = byteToSpec bytes[index]! := by
  by_cases inside : index < bytes.length
  · simp [inside, bytesToSpec_getElem]
  · simp [inside, bytesToSpec, byteToSpec]
    rfl

theorem bytesToSpec_all_zero (bytes : List U8) :
    (bytesToSpec bytes).all (· == 0) ↔
      ∀ position, position < bytes.length → bytes[position]! = 0#u8 := by
  rw [_root_.Array.all_eq_true]
  simp [bytesToSpec_getElem]

@[step] theorem all_zero_refines (bytes : Slice U8) :
    FastSszRust.bitfield.all_zero bytes ⦃ result =>
      result = (bytesToSpec bytes.val).all (· == 0) ⦄ := by
  unfold FastSszRust.bitfield.all_zero
  apply spec_mono (all_zero_loop_refines bytes 0#usize (by simp) (by simp))
  intro result agrees
  apply Bool.eq_iff_iff.mpr
  rw [agrees, bytesToSpec_all_zero]

end FastSszVerification
