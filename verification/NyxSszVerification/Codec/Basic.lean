import NyxSszVerification.Codec.Adapter
import NyxSszVerification.TreeHash

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace NyxSszVerification

theorem bool_codec_refines :
    CodecLaw NyxSszRust.Bool.Insts.Nyx_sszCodecSszTuple .bool Ssz.Value.bool := by
  constructor
  · simp [NyxSszRust.Bool.Insts.Nyx_sszCodecSszTuple.TYPE, typeDescriptorToSpec]
  · intro value
    dsimp only [NyxSszRust.Bool.Insts.Nyx_sszCodecSszTuple]
    unfold NyxSszRust.Bool.Insts.Nyx_sszCodecSszTuple.encode
    apply encode_adapter (valid := rfl)
    obtain ⟨encoded, runs, correct⟩ := encode_bool_refines value
    rw [runs]
    exact correct
  · intro bytes
    dsimp only [NyxSszRust.Bool.Insts.Nyx_sszCodecSszTuple]
    unfold NyxSszRust.Bool.Insts.Nyx_sszCodecSszTuple.decode
    have scalar : NyxSszRust.scalar.decode_bool bytes ⦃ actual =>
        scalarDecodingAgrees Ssz.Value.bool actual
          (checkedDeserialize .bool (bytesToSpec bytes.val)) ⦄ := by
      rw [decode_bool_refines]
      exact boolean_scalar_agrees (bytesToSpec bytes.val)
    convert decode_adapter scalar using 1
    congr 1
    funext result
    cases result <;> rfl
  · intro value
    dsimp only [NyxSszRust.Bool.Insts.Nyx_sszCodecSszTuple]
    unfold NyxSszRust.Bool.Insts.Nyx_sszCodecSszTuple.hash_tree_root
    apply root_adapter (valid := rfl)
    exact hash_tree_root_bool_refines value

theorem u8_codec_refines :
    CodecLaw NyxSszRust.U8.Insts.Nyx_sszCodecSszTuple (.uint 1) (fun value : U8 => .uint (value.val)) := by
  constructor
  · simp [NyxSszRust.U8.Insts.Nyx_sszCodecSszTuple.TYPE, typeDescriptorToSpec]
  · intro value
    dsimp only [NyxSszRust.U8.Insts.Nyx_sszCodecSszTuple]
    unfold NyxSszRust.U8.Insts.Nyx_sszCodecSszTuple.encode
    apply encode_adapter (valid := rfl)
    exact encode_u8_refines value
  · intro bytes
    dsimp only [NyxSszRust.U8.Insts.Nyx_sszCodecSszTuple]
    unfold NyxSszRust.U8.Insts.Nyx_sszCodecSszTuple.decode
    have scalar : NyxSszRust.scalar.decode_u8 bytes ⦃ actual =>
        scalarDecodingAgrees (fun value : U8 => .uint (value.val)) actual
          (checkedDeserialize (.uint 1) (bytesToSpec bytes.val)) ⦄ := by
      apply spec_mono (decode_u8_refines bytes)
      intro actual agrees
      exact uint_scalar_agrees (fun value : U8 => value.val) actual _ agrees
    convert decode_adapter scalar using 1
    congr 1
    funext result
    cases result <;> rfl
  · intro value
    dsimp only [NyxSszRust.U8.Insts.Nyx_sszCodecSszTuple]
    unfold NyxSszRust.U8.Insts.Nyx_sszCodecSszTuple.hash_tree_root
    apply root_adapter (valid := rfl)
    exact hash_tree_root_u8_refines value


theorem u16_codec_refines :
    CodecLaw NyxSszRust.U16.Insts.Nyx_sszCodecSszTuple (.uint 2) (fun value : U16 => .uint (value.val)) := by
  constructor
  · simp [NyxSszRust.U16.Insts.Nyx_sszCodecSszTuple.TYPE, typeDescriptorToSpec]
  · intro value
    dsimp only [NyxSszRust.U16.Insts.Nyx_sszCodecSszTuple]
    unfold NyxSszRust.U16.Insts.Nyx_sszCodecSszTuple.encode
    apply encode_adapter (valid := rfl)
    exact encode_u16_refines value
  · intro bytes
    dsimp only [NyxSszRust.U16.Insts.Nyx_sszCodecSszTuple]
    unfold NyxSszRust.U16.Insts.Nyx_sszCodecSszTuple.decode
    have scalar : NyxSszRust.scalar.decode_u16 bytes ⦃ actual =>
        scalarDecodingAgrees (fun value : U16 => .uint (value.val)) actual
          (checkedDeserialize (.uint 2) (bytesToSpec bytes.val)) ⦄ := by
      apply spec_mono (decode_u16_refines bytes)
      intro actual agrees
      exact uint_scalar_agrees (fun value : U16 => value.val) actual _ agrees
    convert decode_adapter scalar using 1
    congr 1
    funext result
    cases result <;> rfl
  · intro value
    dsimp only [NyxSszRust.U16.Insts.Nyx_sszCodecSszTuple]
    unfold NyxSszRust.U16.Insts.Nyx_sszCodecSszTuple.hash_tree_root
    apply root_adapter (valid := rfl)
    exact hash_tree_root_u16_refines value


theorem u32_codec_refines :
    CodecLaw NyxSszRust.U32.Insts.Nyx_sszCodecSszTuple (.uint 4) (fun value : U32 => .uint (value.val)) := by
  constructor
  · simp [NyxSszRust.U32.Insts.Nyx_sszCodecSszTuple.TYPE, typeDescriptorToSpec]
  · intro value
    dsimp only [NyxSszRust.U32.Insts.Nyx_sszCodecSszTuple]
    unfold NyxSszRust.U32.Insts.Nyx_sszCodecSszTuple.encode
    apply encode_adapter (valid := rfl)
    exact encode_u32_refines value
  · intro bytes
    dsimp only [NyxSszRust.U32.Insts.Nyx_sszCodecSszTuple]
    unfold NyxSszRust.U32.Insts.Nyx_sszCodecSszTuple.decode
    have scalar : NyxSszRust.scalar.decode_u32 bytes ⦃ actual =>
        scalarDecodingAgrees (fun value : U32 => .uint (value.val)) actual
          (checkedDeserialize (.uint 4) (bytesToSpec bytes.val)) ⦄ := by
      apply spec_mono (decode_u32_refines bytes)
      intro actual agrees
      exact uint_scalar_agrees (fun value : U32 => value.val) actual _ agrees
    convert decode_adapter scalar using 1
    congr 1
    funext result
    cases result <;> rfl
  · intro value
    dsimp only [NyxSszRust.U32.Insts.Nyx_sszCodecSszTuple]
    unfold NyxSszRust.U32.Insts.Nyx_sszCodecSszTuple.hash_tree_root
    apply root_adapter (valid := rfl)
    exact hash_tree_root_u32_refines value


theorem u64_codec_refines :
    CodecLaw NyxSszRust.U64.Insts.Nyx_sszCodecSszTuple (.uint 8) (fun value : U64 => .uint (value.val)) := by
  constructor
  · simp [NyxSszRust.U64.Insts.Nyx_sszCodecSszTuple.TYPE, typeDescriptorToSpec]
  · intro value
    dsimp only [NyxSszRust.U64.Insts.Nyx_sszCodecSszTuple]
    unfold NyxSszRust.U64.Insts.Nyx_sszCodecSszTuple.encode
    apply encode_adapter (valid := rfl)
    exact encode_u64_refines value
  · intro bytes
    dsimp only [NyxSszRust.U64.Insts.Nyx_sszCodecSszTuple]
    unfold NyxSszRust.U64.Insts.Nyx_sszCodecSszTuple.decode
    have scalar : NyxSszRust.scalar.decode_u64 bytes ⦃ actual =>
        scalarDecodingAgrees (fun value : U64 => .uint (value.val)) actual
          (checkedDeserialize (.uint 8) (bytesToSpec bytes.val)) ⦄ := by
      apply spec_mono (decode_u64_refines bytes)
      intro actual agrees
      exact uint_scalar_agrees (fun value : U64 => value.val) actual _ agrees
    convert decode_adapter scalar using 1
    congr 1
    funext result
    cases result <;> rfl
  · intro value
    dsimp only [NyxSszRust.U64.Insts.Nyx_sszCodecSszTuple]
    unfold NyxSszRust.U64.Insts.Nyx_sszCodecSszTuple.hash_tree_root
    apply root_adapter (valid := rfl)
    exact hash_tree_root_u64_refines value


theorem u128_codec_refines :
    CodecLaw NyxSszRust.U128.Insts.Nyx_sszCodecSszTuple (.uint 16) (fun value : U128 => .uint (value.val)) := by
  constructor
  · simp [NyxSszRust.U128.Insts.Nyx_sszCodecSszTuple.TYPE, typeDescriptorToSpec]
  · intro value
    dsimp only [NyxSszRust.U128.Insts.Nyx_sszCodecSszTuple]
    unfold NyxSszRust.U128.Insts.Nyx_sszCodecSszTuple.encode
    apply encode_adapter (valid := rfl)
    exact encode_u128_refines value
  · intro bytes
    dsimp only [NyxSszRust.U128.Insts.Nyx_sszCodecSszTuple]
    unfold NyxSszRust.U128.Insts.Nyx_sszCodecSszTuple.decode
    have scalar : NyxSszRust.scalar.decode_u128 bytes ⦃ actual =>
        scalarDecodingAgrees (fun value : U128 => .uint (value.val)) actual
          (checkedDeserialize (.uint 16) (bytesToSpec bytes.val)) ⦄ := by
      apply spec_mono (decode_u128_refines bytes)
      intro actual agrees
      exact uint_scalar_agrees (fun value : U128 => value.val) actual _ agrees
    convert decode_adapter scalar using 1
    congr 1
    funext result
    cases result <;> rfl
  · intro value
    dsimp only [NyxSszRust.U128.Insts.Nyx_sszCodecSszTuple]
    unfold NyxSszRust.U128.Insts.Nyx_sszCodecSszTuple.hash_tree_root
    apply root_adapter (valid := rfl)
    exact hash_tree_root_u128_refines value


theorem u256_codec_refines :
    CodecLaw NyxSszRust.ruint.Uint2564.Insts.Nyx_sszCodecSszTuple (.uint 32) (fun value : RustU256 => .uint (u256Value value)) := by
  constructor
  · simp [NyxSszRust.ruint.Uint2564.Insts.Nyx_sszCodecSszTuple.TYPE, typeDescriptorToSpec]
  · intro value
    dsimp only [NyxSszRust.ruint.Uint2564.Insts.Nyx_sszCodecSszTuple]
    unfold NyxSszRust.ruint.Uint2564.Insts.Nyx_sszCodecSszTuple.encode
    apply encode_adapter (valid := rfl)
    exact encode_u256_refines value
  · intro bytes
    dsimp only [NyxSszRust.ruint.Uint2564.Insts.Nyx_sszCodecSszTuple]
    unfold NyxSszRust.ruint.Uint2564.Insts.Nyx_sszCodecSszTuple.decode
    have scalar : NyxSszRust.scalar.decode_u256 bytes ⦃ actual =>
        scalarDecodingAgrees (fun value : RustU256 => .uint (u256Value value)) actual
          (checkedDeserialize (.uint 32) (bytesToSpec bytes.val)) ⦄ := by
      apply spec_mono (decode_u256_refines bytes)
      intro actual agrees
      exact uint_scalar_agrees (fun value : RustU256 => u256Value value) actual _ agrees
    convert decode_adapter scalar using 1
    congr 1
    funext result
    cases result <;> rfl
  · intro value
    dsimp only [NyxSszRust.ruint.Uint2564.Insts.Nyx_sszCodecSszTuple]
    unfold NyxSszRust.ruint.Uint2564.Insts.Nyx_sszCodecSszTuple.hash_tree_root
    apply root_adapter (valid := rfl)
    exact hash_tree_root_u256_refines value

end NyxSszVerification
