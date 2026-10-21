import NyxSszVerification.OwnedBits.Codec
import NyxSszVerification.PackedRoots.View
import NyxSszVerification.PackedRoots.Bits
import NyxSszVerification.PackedRoots.Bytes

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace NyxSszVerification

theorem owned_spec_pair {α : Type} (m : RustM α) (p q : α → Prop)
    (first : m ⦃ actual => p actual ⦄) (second : m ⦃ actual => q actual ⦄) :
    m ⦃ actual => p actual ∧ q actual ⦄ := by
  cases m <;> simp_all [spec, theta, wp_return]

theorem owned_borrowed_decoder_preserves (bytes : Slice U8) (limit : Option Usize) :
    NyxSszRust.bitfield.decode_progressive_bit_list bytes limit ⦃ actual =>
      match actual with | .Ok view => view.encoded = bytes | .Err _ => True ⦄ := by
  unfold NyxSszRust.bitfield.decode_progressive_bit_list
  step*

theorem owned_borrowed_decoder_refines (bytes : Slice U8) (limit : Option Usize) :
    NyxSszRust.bitfield.decode_progressive_bit_list bytes limit ⦃ actual =>
      progressiveBitDecodingAgrees actual (checkedDeserialize
        (.progressiveBitList (limit.map fun cap => cap.val)) (bytesToSpec bytes.val)) ∧
      (match actual with | .Ok view => view.encoded = bytes | .Err _ => True) ⦄ := by
  exact owned_spec_pair _ _ _ (decode_progressive_bit_list_refines bytes limit)
    (owned_borrowed_decoder_preserves bytes limit)

theorem owned_canonical_list_decode (bytes : Slice U8) (limit : Option Usize)
    (nonempty : 0 < bytes.val.length)
    (nonzero : (bytesToSpec bytes.val)[bytes.val.length - 1]! ≠ 0)
    (within : ∀ cap, limit = some cap → delimitedLength bytes.val ≤ cap.val) :
    checkedDeserialize (.progressiveBitList (limit.map fun cap => cap.val)) (bytesToSpec bytes.val) =
      .ok (.bits (ownedListBits bytes.val)) := by
  have notEmpty : bytes.val ≠ [] := by intro empty; simp_all
  cases chosen : limit <;>
    simp_all [checkedDeserialize, Ssz.Desc.wellFormed, Ssz.deserialize, Ssz.unpackDelimited,
      ownedListBits, delimitedLength, Bind.bind, Except.bind, Pure.pure, Except.pure]
  split_ifs <;> try simp_all
  omega

theorem owned_bounded_list_root (bytes : Slice U8) (limit : Usize)
    (nonempty : 0 < bytes.val.length)
    (nonzero : (bytesToSpec bytes.val)[bytes.val.length - 1]! ≠ 0)
    (within : delimitedLength bytes.val ≤ limit.val) :
    NyxSszRust.bit_storage.root_bounded_list bytes limit ⦃ actual =>
      codecRootAgrees actual (checkedHashTreeRoot (.bitList limit.val) (.bits (ownedListBits bytes.val))) ⦄ := by
  have decoded : checkedDeserialize (.progressiveBitList (some limit.val)) (bytesToSpec bytes.val) =
      .ok (.bits (ownedListBits bytes.val)) :=
    owned_canonical_list_decode bytes (some limit) nonempty nonzero (by simp_all)
  unfold NyxSszRust.bit_storage.root_bounded_list
  apply spec_bind (owned_borrowed_decoder_refines bytes (some limit))
  intro result agrees
  cases result with
  | Err error => simp [decoded, progressiveBitDecodingAgrees] at agrees
  | Ok view =>
    rcases agrees with ⟨agrees, same⟩
    simp only [Option.map_some, decoded, progressiveBitDecodingAgrees] at agrees
    rcases agrees with ⟨canonical, bitsEq⟩
    apply spec_bind (bit_list_view_len_bits_refines view canonical.1)
    intro length lengthEq
    have bytesEq : view.encoded = bytes := same
    rw [← bytesEq]
    apply spec_bind (bitlist_payload_refines view length canonical.1 lengthEq)
    intro payload packed
    apply spec_bind (packed_div_ceil_bits limit)
    intro capacity capacityEq
    have countEq : payload.1.val = ((viewBits view).size + 7) / 8 := by
      have sizes := congrArg _root_.Array.size packed.2.1
      simpa [Ssz.packBits, packed.1] using sizes
    have room : (payload.1.val + 31) / 32 ≤ capacity.val := by
      rw [countEq, packed_bits_node_count, capacityEq, bitsEq, ownedListBits_size]
      omega
    apply spec_mono (packed_root_bounded_refines view.encoded payload.1 payload.2 capacity (some length) packed.1 room)
    intro actual root
    have lengthSize : length.val = (viewBits view).size := by simpa using lengthEq
    have packedEq : bytesToSpec (packedInput bytes.val payload.1.val payload.2) =
        Ssz.packBits (ownedListBits bytes.val) (((ownedListBits bytes.val).size + 7) / 8) := by
      simpa only [same, bitsEq] using packed.2.1
    have capEq : (limit.val + 256 - 1) / 256 = (limit.val + 255) / 256 := by omega
    simpa only [same, packedEq, Option.map_some, lengthSize, capacityEq,
      bitsEq, checkedHashTreeRoot_bitList, ownedListBits_size, Nat.not_lt.mpr within,
      ↓reduceIte, Ssz.chunksForBits, Ssz.bitsPerChunk, Ssz.bytesPerChunk, Nat.reduceMul,
      capEq] using root

end NyxSszVerification
