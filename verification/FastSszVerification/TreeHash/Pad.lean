import FastSszRust.TreeHash
import FastSszVerification.Representation.Bytes

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace FastSszVerification

theorem replicate_set_prefix {α : Type} (values : List α) (zero : α) (size : Nat)
    (within : values.length ≤ size) :
    (List.replicate size zero).setSlice! 0 values =
      values ++ List.replicate (size - values.length) zero := by
  simp [List.setSlice!, Nat.min_eq_left within]

@[step] theorem scalar_chunk_refines {size : Usize} (encoded : Array U8 size)
    (within : size.val ≤ 32) :
    FastSszRust.tree_hash.scalar_chunk encoded ⦃ root =>
      root.val = encoded.val ++ List.replicate (32 - size.val) 0#u8 ⦄ := by
  unfold FastSszRust.tree_hash.scalar_chunk
  step*
  all_goals simp_all
  have sizeEq : encoded.val.length = size.val := by have shape := encoded.property; scalar_tac
  have fits : encoded.val.length ≤ 32 := by omega
  simpa only [sizeEq, List.replicate_succ, List.replicate_zero] using
    replicate_set_prefix encoded.val (0#u8) 32 fits

theorem bytesToSpec_padding (bytes : List U8) (count : Nat) :
    bytesToSpec (bytes ++ List.replicate count 0#u8) =
      bytesToSpec bytes ++ _root_.Array.replicate count 0 := by
  simp [bytesToSpec, byteToSpec]

end FastSszVerification
