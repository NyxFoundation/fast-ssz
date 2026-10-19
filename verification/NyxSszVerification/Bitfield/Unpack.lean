import NyxSszRust.Bitfield
import NyxSszVerification.Bitfield.Read
import NyxSszVerification.Loop

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace NyxSszVerification

@[step] theorem unpack_loop_refines (bytes : Slice U8) (count : Usize)
    (output : alloc.vec.Vec Bool) (index : Usize)
    (capacity : count.val ≤ bytes.val.length * 8)
    (within : index.val ≤ count.val)
    (initialData : output.val = unpackedPrefix bytes.val index.val) :
    NyxSszRust.bitfield.unpack_bits_loop bytes count output index ⦃ result =>
      result.val = unpackedPrefix bytes.val count.val ⦄ := by
  unfold NyxSszRust.bitfield.unpack_bits_loop
  apply loop_total
    (invariant := fun state : alloc.vec.Vec Bool × Usize =>
      state.2.val ≤ count.val ∧ state.1.val = unpackedPrefix bytes.val state.2.val)
    (measure := fun state => count.val - state.2.val)
  · rintro ⟨nextOutput, nextIndex⟩ ⟨inBounds, data⟩
    have outputLength : nextOutput.val.length = nextIndex.val := by
      rw [data, unpackedPrefix_length]
    unfold NyxSszRust.bitfield.unpack_bits_loop.body
    step*
    all_goals simp_all [unpackedPrefix_succ, UScalar.eq_equiv_bv_eq]
    have inBytes : nextIndex.val / 8 < bytes.val.length := by scalar_tac
    constructor
    · rw [referenceBit_bv _ _ inBytes]
      simp [inBytes]
    · omega
  · exact ⟨within, initialData⟩

@[step] theorem unpack_bits_refines (bytes : Slice U8) (count : Usize)
    (capacity : count.val ≤ bytes.val.length * 8) :
    NyxSszRust.bitfield.unpack_bits bytes count ⦃ output =>
      bitsToSpec output.val = Ssz.unpackBits (bytesToSpec bytes.val) count.val ⦄ := by
  unfold NyxSszRust.bitfield.unpack_bits
  step*
  all_goals simp_all [bitsToSpec, unpackBits_prefix]

end NyxSszVerification
