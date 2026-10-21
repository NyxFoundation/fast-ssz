import NyxSszVerification.Collection.PackReference
import NyxSszRust.CollectionTree
import NyxSszVerification.Loop

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxHeartbeats 2000000

namespace NyxSszVerification

def collectionChunkBytes (chunks : List RustNode) : List U8 := chunks.flatMap fun chunk => chunk.val

@[simp] theorem collectionChunkBytes_nil : collectionChunkBytes [] = [] := rfl

@[simp] theorem collectionChunkBytes_append (left right : List RustNode) :
    collectionChunkBytes (left ++ right) = collectionChunkBytes left ++ collectionChunkBytes right := by
  simp [collectionChunkBytes]

@[simp] theorem collectionChunkBytes_singleton (chunk : RustNode) :
    collectionChunkBytes [chunk] = chunk.val := by simp [collectionChunkBytes]

@[simp] theorem collectionChunkBytes_length (chunks : List RustNode) :
    (collectionChunkBytes chunks).length = chunks.length * 32 := by
  induction chunks with
  | nil => rfl
  | cons chunk rest ih =>
    simp only [collectionChunkBytes, List.flatMap_cons, List.length_append,
      List.length_cons, chunk.property, UScalar.ofNatCore_val_eq] at *
    omega

/-- An open node contains a completed prefix and zero-filled unused positions. -/
def collectionPackingState (chunks : alloc.vec.Vec RustNode) (pending : RustNode)
    (filled : Usize) (remaining data : List U8) : Prop :=
  filled.val < 32 ∧ pending.val.drop filled.val = List.replicate (32 - filled.val) 0#u8 ∧
    collectionChunkBytes chunks.val ++ pending.val.take filled.val ++ remaining = data

/-- Writing the next pending byte changes no preceding byte or unused padding. -/
theorem collection_pending_update (pending : RustNode) (filled : Nat) (byte : U8)
    (within : filled < 32)
    (padding : pending.val.drop filled = List.replicate (32 - filled) 0#u8) :
    (pending.val.set filled byte).take (filled + 1) = pending.val.take filled ++ [byte] ∧
      (pending.val.set filled byte).drop (filled + 1) = List.replicate (32 - (filled + 1)) 0#u8 := by
  have size := pending.property
  have active : filled < pending.val.length := by scalar_tac
  have nextTake : (pending.val.set filled byte).take (filled + 1) = pending.val.take filled ++ [byte] := by
    rw [List.take_succ_eq_append_getElem (by simpa using active), List.take_set_of_le (by omega),
      List.getElem_set_self]
  refine ⟨nextTake, ?_⟩
  rw [List.drop_set_of_lt (by omega), ← List.drop_drop (i := 1) (j := filled), padding]
  simp [List.drop_replicate, Nat.sub_sub]

end NyxSszVerification
