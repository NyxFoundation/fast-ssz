import FastSszVerification.TreeHash.Basic
import FastSszVerification.TreeHash.Pad
import FastSszVerification.Boolean
import FastSszVerification.Unsigned.U256

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxRecDepth 4096
set_option maxHeartbeats 200000

namespace FastSszVerification

theorem hash_tree_root_bool_refines (value : Bool) :
    FastSszRust.tree_hash.hash_tree_root_bool value ⦃ root =>
      Ssz.hashTreeRoot .bool (.bool value) = .ok (bytesToSpec root.val) ⦄ := by
  obtain ⟨encoded, runs, encoding⟩ := encode_bool_refines value
  unfold FastSszRust.tree_hash.hash_tree_root_bool
  simp only [Bind.bind, runs, bind_ok]
  apply spec_mono (scalar_chunk_refines encoded (by simp))
  intro root padded
  have form := hashTreeRoot_bool_encoded value (bytesToSpec encoded.val) encoding (by simp) (by simp)
  simpa only [padded, bytesToSpec_padding, bytesToSpec_size, Array.length_eq] using form

theorem hash_tree_root_u8_refines (value : U8) :
    FastSszRust.tree_hash.hash_tree_root_u8 value ⦃ root =>
      Ssz.hashTreeRoot (.uint 1) (.uint value.val) = .ok (bytesToSpec root.val) ⦄ := by
  unfold FastSszRust.tree_hash.hash_tree_root_u8
  simp only [Bind.bind]
  apply spec_bind (encode_u8_refines value)
  intro encoded encoding
  apply spec_mono (scalar_chunk_refines encoded (by simp))
  intro root padded
  have form := hashTreeRoot_uint_encoded 1 value.val (bytesToSpec encoded.val) encoding (by simp) (by simp)
  simpa only [padded, bytesToSpec_padding, bytesToSpec_size, Array.length_eq] using form

theorem hash_tree_root_u16_refines (value : U16) :
    FastSszRust.tree_hash.hash_tree_root_u16 value ⦃ root =>
      Ssz.hashTreeRoot (.uint 2) (.uint value.val) = .ok (bytesToSpec root.val) ⦄ := by
  unfold FastSszRust.tree_hash.hash_tree_root_u16
  simp only [Bind.bind]
  apply spec_bind (encode_u16_refines value)
  intro encoded encoding
  apply spec_mono (scalar_chunk_refines encoded (by simp))
  intro root padded
  have form := hashTreeRoot_uint_encoded 2 value.val (bytesToSpec encoded.val) encoding (by simp) (by simp)
  simpa only [padded, bytesToSpec_padding, bytesToSpec_size, Array.length_eq] using form

theorem hash_tree_root_u32_refines (value : U32) :
    FastSszRust.tree_hash.hash_tree_root_u32 value ⦃ root =>
      Ssz.hashTreeRoot (.uint 4) (.uint value.val) = .ok (bytesToSpec root.val) ⦄ := by
  unfold FastSszRust.tree_hash.hash_tree_root_u32
  simp only [Bind.bind]
  apply spec_bind (encode_u32_refines value)
  intro encoded encoding
  apply spec_mono (scalar_chunk_refines encoded (by simp))
  intro root padded
  have form := hashTreeRoot_uint_encoded 4 value.val (bytesToSpec encoded.val) encoding (by simp) (by simp)
  simpa only [padded, bytesToSpec_padding, bytesToSpec_size, Array.length_eq] using form

theorem hash_tree_root_u64_refines (value : U64) :
    FastSszRust.tree_hash.hash_tree_root_u64 value ⦃ root =>
      Ssz.hashTreeRoot (.uint 8) (.uint value.val) = .ok (bytesToSpec root.val) ⦄ := by
  unfold FastSszRust.tree_hash.hash_tree_root_u64
  simp only [Bind.bind]
  apply spec_bind (encode_u64_refines value)
  intro encoded encoding
  apply spec_mono (scalar_chunk_refines encoded (by simp))
  intro root padded
  have form := hashTreeRoot_uint_encoded 8 value.val (bytesToSpec encoded.val) encoding (by simp) (by simp)
  simpa only [padded, bytesToSpec_padding, bytesToSpec_size, Array.length_eq] using form

theorem hash_tree_root_u128_refines (value : U128) :
    FastSszRust.tree_hash.hash_tree_root_u128 value ⦃ root =>
      Ssz.hashTreeRoot (.uint 16) (.uint value.val) = .ok (bytesToSpec root.val) ⦄ := by
  unfold FastSszRust.tree_hash.hash_tree_root_u128
  simp only [Bind.bind]
  apply spec_bind (encode_u128_refines value)
  intro encoded encoding
  apply spec_mono (scalar_chunk_refines encoded (by simp))
  intro root padded
  have form := hashTreeRoot_uint_encoded 16 value.val (bytesToSpec encoded.val) encoding (by simp) (by simp)
  simpa only [padded, bytesToSpec_padding, bytesToSpec_size, Array.length_eq] using form

theorem hash_tree_root_u256_refines (value : RustU256) :
    FastSszRust.tree_hash.hash_tree_root_u256 value ⦃ root =>
      Ssz.hashTreeRoot (.uint 32) (.uint (u256Value value)) = .ok (bytesToSpec root.val) ⦄ := by
  unfold FastSszRust.tree_hash.hash_tree_root_u256
  apply spec_mono (encode_u256_refines value)
  intro encoded encoding
  have size : (bytesToSpec encoded.val).size = 32 := by simp
  have form := hashTreeRoot_uint_encoded 32 (u256Value value) (bytesToSpec encoded.val) encoding
    (by simp) (by simp)
  simpa only [size, Nat.sub_self, _root_.Array.replicate_zero, _root_.Array.append_empty] using form

end FastSszVerification
