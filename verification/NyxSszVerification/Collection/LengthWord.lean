import NyxSszVerification.Collection.Size
import NyxSszVerification.TreeHash
import NyxSszVerification.Sha256

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxHeartbeats 1000000

namespace NyxSszVerification

@[simp] theorem collection_uint_bytes_zero (width : Nat) :
    Ssz.uintBytes width 0 = _root_.Array.replicate width 0 := by
  induction width with
  | zero => rfl
  | succ width ih =>
    simp only [Ssz.uintBytes, Nat.zero_mod, Nat.zero_div, ih]
    apply _root_.Array.toList_inj.mp
    simp [List.replicate_succ]

/-- Zero-extending a bounded little-endian integer preserves its high zero bytes. -/
theorem collection_uint_bytes_padding (width padding value : Nat) (bound : value < 256 ^ width) :
    Ssz.uintBytes (width + padding) value =
      Ssz.uintBytes width value ++ _root_.Array.replicate padding 0 := by
  induction width generalizing value with
  | zero =>
    have zero : value = 0 := by simpa using bound
    simp [zero]
  | succ width ih =>
    have smaller : value / 256 < 256 ^ width := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      simpa [Nat.pow_succ, Nat.mul_comm] using bound
    rw [Nat.succ_add, Ssz.uintBytes, Ssz.uintBytes, ih _ smaller]
    simp only [_root_.Array.append_assoc]

@[step] theorem collection_length_word_refines (count : Usize) :
    NyxSszRust.tree_hash.hash_tree_root_u128 (UScalar.cast .U128 count) ⦃ actual =>
      bytesToSpec actual.val = Ssz.lengthWord count.val ⦄ := by
  let value := UScalar.cast .U128 count
  have bound : value.val < 2 ^ (8 * 16) := by scalar_tac
  have encoding : Ssz.serialize (.uint 16) (.uint value.val) = .ok (Ssz.uintBytes 16 value.val) := by
    simp only [Ssz.serialize, if_pos bound]
  have form := hashTreeRoot_uint_encoded 16 value.val (Ssz.uintBytes 16 value.val)
    encoding (by simp only [Ssz.uintBytes_size]; decide) (by simp only [Ssz.uintBytes_size]; decide)
  simp only [Ssz.uintBytes_size, show 32 - 16 = 16 from rfl] at form
  apply spec_mono (hash_tree_root_u128_refines value)
  intro actual correct
  rw [form] at correct
  simp only [Except.ok.injEq] at correct
  rw [← correct]
  change Ssz.uintBytes 16 (UScalar.cast .U128 count).val ++ _root_.Array.replicate 16 0 =
    Ssz.uintBytes 32 count.val
  simpa only [collection_widen_usize] using
    (collection_uint_bytes_padding 16 16 count.val (by scalar_tac)).symm

end NyxSszVerification
