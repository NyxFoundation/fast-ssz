import NyxSszVerification.Collection.Pack

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxHeartbeats 2000000

namespace NyxSszVerification

/-- Filling one byte preserves the completed prefix and the unused zero suffix. -/
theorem packed_byte_write_refines (chunks : alloc.vec.Vec RustNode) (pending : RustNode)
    (filled : Usize) (byte : U8) (remaining data : List U8)
    (bound : data.length ≤ Usize.max * 32)
    (initial : collectionPackingState chunks pending filled (byte :: remaining) data) :
    (do
      let (_, back) ← Array.index_mut_usize pending filled
      let next ← filled + 1#usize
      if next = 32#usize then do
        let output ← alloc.vec.Vec.push chunks (back byte)
        RustM.ok (output, Array.repeat 32#usize 0#u8, 0#usize)
      else RustM.ok (chunks, back byte, next)) ⦃ actual =>
        collectionPackingState actual.1 actual.2.1 actual.2.2 remaining data ⦄ := by
  obtain ⟨used, padding, bytes⟩ := initial
  have length := congrArg List.length bytes
  simp only [List.length_append, collectionChunkBytes_length, List.length_take,
    List.length_cons, Array.length_eq, UScalar.ofNatCore_val_eq,
    Nat.min_eq_left (Nat.le_of_lt used)] at length
  have update := collection_pending_update pending filled.val byte used padding
  step
  step
  by_cases full : next = 32#usize
  · simp only [full, if_true]
    step*
    have pendingEq : (back byte).val = pending.val.set filled.val byte := by simp [__post3]
    have fullCount : filled.val + 1 = 32 := by scalar_tac
    have closed : (back byte).val = pending.val.take filled.val ++ [byte] := by
      have current := update.1
      rw [← pendingEq, fullCount] at current
      simpa only [List.take_of_length_le (by simp : (back byte).val.length ≤ 32)] using current
    refine ⟨by simp, by simp, ?_⟩
    simp only [output_post, collectionChunkBytes_append, collectionChunkBytes_singleton, closed]
    simpa only [UScalar.ofNatCore_val_eq, List.take_zero, List.append_nil,
      List.append_assoc, List.singleton_append] using bytes
  · simp only [full, if_false]
    step*
    have pendingEq : (back byte).val = pending.val.set filled.val byte := by simp [__post3]
    refine ⟨by scalar_tac, ?_, ?_⟩
    · simpa only [pendingEq, next_post] using update.2
    · rw [pendingEq, next_post, update.1]
      simpa only [List.append_assoc, List.singleton_append] using bytes

private theorem packed_bind_assoc {α β γ : Type} (first : RustM α)
    (next : α → RustM β) (finish : β → RustM γ) :
    Std.bind (Std.bind first next) finish = Std.bind first (fun value => Std.bind (next value) finish) := by
  cases first <;> rfl

/-- The byte-writing block can be used without changing the extracted bind association. -/
theorem packed_byte_write_then_refines {α : Type}
    (chunks : alloc.vec.Vec RustNode) (pending : RustNode) (filled : Usize) (byte : U8)
    (remaining data : List U8) (bound : data.length ≤ Usize.max * 32)
    (initial : collectionPackingState chunks pending filled (byte :: remaining) data)
    (finish : alloc.vec.Vec RustNode × RustNode × Usize → RustM α) (post : α → Prop)
    (complete : ∀ actual, collectionPackingState actual.1 actual.2.1 actual.2.2 remaining data →
      finish actual ⦃ post ⦄) :
    (do
      let (_, back) ← Array.index_mut_usize pending filled
      let next ← filled + 1#usize
      let result ← if next = 32#usize then do
        let output ← alloc.vec.Vec.push chunks (back byte)
        RustM.ok (output, Array.repeat 32#usize 0#u8, 0#usize)
      else RustM.ok (chunks, back byte, next)
      finish result) ⦃ post ⦄ := by
  have correct := spec_bind
    (packed_byte_write_refines chunks pending filled byte remaining data bound initial) complete
  simp only [Bind.bind, Aeneas.Std.uncurry, packed_bind_assoc] at correct ⊢
  exact correct

end NyxSszVerification
