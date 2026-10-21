import NyxSszVerification.OwnedBits.RootHelpers

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace NyxSszVerification

theorem owned_list_root_refines {MAX : Usize} (value : NyxSszRust.bitcollections.BitList MAX) :
    NyxSszRust.bitcollections.BitList.Insts.Nyx_sszCodecSszTuple.hash_tree_root value ⦃ actual =>
      codecRootAgrees actual (checkedHashTreeRoot (.bitList MAX.val) (observeOwnedList value)) ⦄ := by
  unfold NyxSszRust.bitcollections.BitList.Insts.Nyx_sszCodecSszTuple.hash_tree_root
    NyxSszRust.bitcollections.BitList.Insts.Nyx_sszCodecSszTuple.encode
  simp only [bind_assoc_eq]
  apply spec_bind (owned_bit_list_as_ssz_bytes_refines value)
  intro bytes byteEq
  apply spec_bind (owned_normalize_list_storage bytes (some MAX))
  intro result correct
  cases result with
  | Ok output =>
    rcases correct with ⟨data, within⟩
    have bound := within MAX rfl
    have nonempty : 0 < output.val.length := by rw [data]; exact ownedNormalizedList_nonempty _
    have nonzero : (bytesToSpec output.val)[output.val.length - 1]! ≠ 0 := by
      rw [data]; exact ownedNormalizedList_last _
    have count : delimitedLength output.val ≤ MAX.val := by simpa [data] using bound
    step*
    have same : val = output := by grind
    subst val
    apply spec_mono (owned_bounded_list_root (alloc.vec.Vec.deref output) MAX nonempty nonzero count)
    intro actual root
    simpa only [alloc.vec.Vec.deref, data, ownedNormalizedList_bits, byteEq, observeOwnedList] using root
  | Err error =>
    rcases correct with ⟨errorEq, cap, capEq, over⟩
    have same : cap = MAX := by simpa using capEq.symm
    subst cap
    step*
    simp_all [checkedHashTreeRoot_bitList, observeOwnedList, codecRootAgrees, codecFaultAgrees]

theorem owned_progressive_root_refines (value : NyxSszRust.bitcollections.ProgressiveBitList) :
    NyxSszRust.bitcollections.ProgressiveBitList.Insts.Nyx_sszCodecSszTuple.hash_tree_root value ⦃ actual =>
      codecRootAgrees actual (checkedHashTreeRoot (.progressiveBitList none) (observeOwnedProgressive value)) ⦄ := by
  unfold NyxSszRust.bitcollections.ProgressiveBitList.Insts.Nyx_sszCodecSszTuple.hash_tree_root
    NyxSszRust.bitcollections.ProgressiveBitList.Insts.Nyx_sszCodecSszTuple.encode
  simp only [bind_assoc_eq]
  apply spec_bind (owned_progressive_bit_list_as_ssz_bytes_refines value)
  intro bytes byteEq
  apply spec_bind (owned_normalize_list_storage bytes none)
  intro result correct
  cases result with
  | Err error => simp at correct
  | Ok output =>
    have data := correct.1
    have nonempty : 0 < output.val.length := by rw [data]; exact ownedNormalizedList_nonempty _
    have nonzero : (bytesToSpec output.val)[output.val.length - 1]! ≠ 0 := by
      rw [data]; exact ownedNormalizedList_last _
    have decoded : checkedDeserialize (.progressiveBitList none) (bytesToSpec output.val) =
        .ok (.bits (ownedListBits output.val)) :=
      owned_canonical_list_decode (alloc.vec.Vec.deref output) none nonempty nonzero (by simp)
    step*
    have same : val = output := by grind
    subst val
    apply spec_bind (owned_borrowed_decoder_refines (alloc.vec.Vec.deref output) none)
    intro result agrees
    cases result with
    | Err error => simp [decoded, progressiveBitDecodingAgrees] at agrees
    | Ok view =>
      have reference := agrees.1
      simp only [Option.map_none, alloc.vec.Vec.deref, decoded, progressiveBitDecodingAgrees] at reference
      rcases reference with ⟨canonical, bitsEq⟩
      apply spec_mono (hash_tree_root_progressive_bit_list_view_unbounded_refines view canonical)
      intro actual root
      simpa only [bitsEq, alloc.vec.Vec.deref, data, ownedNormalizedList_bits, byteEq,
        observeOwnedProgressive] using root

theorem owned_vector_root_refines {N : Usize} (value : NyxSszRust.bitcollections.BitVector N) :
    NyxSszRust.bitcollections.BitVector.Insts.Nyx_sszCodecSszTuple.hash_tree_root value ⦃ actual =>
      codecRootAgrees actual (checkedHashTreeRoot (.bitVector N.val) (observeOwnedVector value)) ⦄ := by
  unfold NyxSszRust.bitcollections.BitVector.Insts.Nyx_sszCodecSszTuple.hash_tree_root
    NyxSszRust.bitcollections.BitVector.Insts.Nyx_sszCodecSszTuple.encode
  simp only [bind_assoc_eq]
  apply spec_bind (owned_bit_vector_as_ssz_bytes_refines value)
  intro bytes byteEq
  apply spec_bind (owned_normalize_vector_storage bytes N)
  intro result correct
  cases result with
  | Ok output =>
    rcases correct with ⟨positive, width, mask, maskValue, data⟩
    have count := ownedVectorCount_of_length bytes.val N.val positive width
    have packed := packedInput_packBits bytes.val bytes.val.length N.val mask (by omega) width maskValue
    have outputWidth : output.val.length = (N.val + 7) / 8 := by simp [data, width]
    have outputPacked : bytesToSpec output.val =
        Ssz.packBits (ownedVectorBits bytes.val N.val) ((N.val + 7) / 8) := by
      simpa only [data, ownedVectorBits, count] using packed
    step*
    have same : val = output := by grind
    subst val
    apply spec_mono (hash_tree_root_byte_vector_refines (alloc.vec.Vec.deref output) i)
    intro actual root
    have capEq : Ssz.chunksForBytes i.val = Ssz.chunksForBits N.val := by
      simp [Ssz.chunksForBytes, Ssz.chunksForBits, Ssz.bytesPerChunk, i_post]
      omega
    have nonzero : i.val ≠ 0 := by omega
    have inputCount : (ownedVectorBits value.encoded.val N.val).size = N.val := by
      simp only [ownedVectorBits_size, ← byteEq, count]
    have byteSize : (bytesToSpec output.val).size = i.val := by simp [outputWidth, i_post]
    rw [checkedHashTreeRoot_byteVector] at root
    simp only [alloc.vec.Vec.deref, nonzero, byteSize, bne_self_eq_false, Bool.false_eq_true,
      ↓reduceIte] at root
    simp only [capEq, outputPacked, byteEq] at root
    simpa only [checkedHashTreeRoot_bitVector, observeOwnedVector, Nat.ne_of_gt positive,
      inputCount, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] using root
  | Err error =>
    rcases correct with ⟨zero, errorEq⟩ | ⟨positive, mismatch, errorEq⟩
    · step*
      simp_all [checkedHashTreeRoot_bitVector, observeOwnedVector, codecRootAgrees, codecFaultAgrees]
    · have countNe : ownedVectorCount value.encoded.val N.val ≠ N.val := by
        intro same
        apply mismatch
        rw [byteEq]
        exact (ownedVectorCount_length_iff _ _ positive).mp same
      step*
      simp_all [checkedHashTreeRoot_bitVector, observeOwnedVector, codecRootAgrees, codecFaultAgrees,
        Nat.ne_of_gt positive]

end NyxSszVerification
