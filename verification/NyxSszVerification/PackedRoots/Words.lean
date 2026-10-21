import NyxSszVerification.Collection.LengthWord
import NyxSszVerification.ProgressiveBits.View

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxHeartbeats 1000000

namespace NyxSszVerification

/-- A widened view count is mixed in without truncating it to a machine size. -/
@[step] theorem packed_length_word_refines (count : U128) :
    NyxSszRust.tree_hash.hash_tree_root_u128 count ⦃ actual =>
      bytesToSpec actual.val = Ssz.lengthWord count.val ⦄ := by
  have bound : count.val < 2 ^ (8 * 16) := by scalar_tac
  have encoding : Ssz.serialize (.uint 16) (.uint count.val) = .ok (Ssz.uintBytes 16 count.val) := by
    simp only [Ssz.serialize, if_pos bound]
  have form := hashTreeRoot_uint_encoded 16 count.val (Ssz.uintBytes 16 count.val)
    encoding (by simp only [Ssz.uintBytes_size]; decide) (by simp only [Ssz.uintBytes_size]; decide)
  simp only [Ssz.uintBytes_size, show 32 - 16 = 16 from rfl] at form
  apply spec_mono (hash_tree_root_u128_refines count)
  intro actual correct
  rw [form] at correct
  simp only [Except.ok.injEq] at correct
  rw [← correct]
  exact (collection_uint_bytes_padding 16 16 count.val (by scalar_tac)).symm

/-- The native bound check reports exactly the reference's over-limit category. -/
@[step] theorem packed_check_bound_refines (count : U128) (limit : Option Usize) :
    NyxSszRust.tree_hash.check_bound count limit ⦃ actual =>
      codecValidityAgrees actual (Ssz.boundCheck (limit.map fun cap => cap.val) count.val) ⦄ := by
  cases chosen : limit
  all_goals simp only [NyxSszRust.tree_hash.check_bound]
  all_goals step*
  all_goals simp_all [codecValidityAgrees, codecFaultAgrees, Ssz.boundCheck]
  all_goals split_ifs <;> simp_all
  all_goals scalar_tac

end NyxSszVerification
