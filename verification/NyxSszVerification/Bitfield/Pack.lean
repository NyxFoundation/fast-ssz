import NyxSszVerification.Bitfield.Byte
import NyxSszVerification.Bitfield.Count
import NyxSszVerification.Loop

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace NyxSszVerification

@[step] theorem pack_loop_refines (bits : Slice Bool) (count : Usize)
    (output : alloc.vec.Vec U8) (index : Usize)
    (counted : count.val = (bits.val.length + 7) / 8)
    (within : index.val ≤ count.val)
    (initialData : output.val.map byteToSpec = packedPrefix bits.val index.val) :
    NyxSszRust.bitfield.pack_bits_loop bits count output index ⦃ result =>
      result.val.map byteToSpec = packedPrefix bits.val count.val ⦄ := by
  unfold NyxSszRust.bitfield.pack_bits_loop
  apply loop_total
    (invariant := fun state : alloc.vec.Vec U8 × Usize =>
      state.2.val ≤ count.val ∧ state.1.val.map byteToSpec = packedPrefix bits.val state.2.val)
    (measure := fun state => count.val - state.2.val)
  · rintro ⟨nextOutput, nextIndex⟩ ⟨inBounds, data⟩
    have outputLength : nextOutput.val.length = nextIndex.val := by
      have same := congrArg List.length data
      simpa only [List.length_map, packedPrefix_length] using same
    unfold NyxSszRust.bitfield.pack_bits_loop.body
    step*
    all_goals simp_all [packedPrefix_succ, packByte_drop, List.map_append]
    all_goals omega
  · exact ⟨within, initialData⟩

@[step] theorem pack_bits_refines (bits : Slice Bool) :
    NyxSszRust.bitfield.pack_bits bits ⦃ output =>
      bytesToSpec output.val =
        Ssz.packBits (bitsToSpec bits.val) ((bits.val.length + 7) / 8) ⦄ := by
  unfold NyxSszRust.bitfield.pack_bits
  step*
  all_goals simp_all [bytesToSpec, packBits_prefix]

end NyxSszVerification
