import NyxSszRust.Bitfield
import NyxSszVerification.Bitfield.Model

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace NyxSszVerification

@[step] theorem bit_at_refines (bits : Slice Bool) (index : Usize) :
    NyxSszRust.bitfield.bit_at bits index ⦃ byte =>
      byte.bv = if bits.val[index.val]?.getD false then 1#8 else 0#8 ⦄ := by
  unfold NyxSszRust.bitfield.bit_at
  step*
  all_goals
    simp_lists
    simp_all

private theorem native_byte_ite (condition : Prop) [Decidable condition] (left right : UInt8) :
    (if condition then left else right).toBitVec =
      if condition then left.toBitVec else right.toBitVec := by
  split <;> rfl

private theorem byte_shift_ite (condition : Prop) [Decidable condition]
    (left right : BitVec 8) (amount : Nat) :
    (if condition then left else right) <<< amount =
      if condition then left <<< amount else right <<< amount := by
  split <;> rfl

@[step] theorem pack_byte_refines (bits : Slice Bool) :
    NyxSszRust.bitfield.pack_byte bits ⦃ byte =>
      byteToSpec byte = Ssz.packByte (bitsToSpec bits.val) 0 ⦄ := by
  unfold NyxSszRust.bitfield.pack_byte
  step*
  apply UInt8.toBitVec_inj.1
  simp_all [byteToSpec, Ssz.packByte, bitsToSpec, native_byte_ite, byte_shift_ite]

end NyxSszVerification
