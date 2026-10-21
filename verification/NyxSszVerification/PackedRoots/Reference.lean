import NyxSszVerification.Codec.Law
import NyxSszVerification.Sequence.Bytes
import NyxSszVerification.Bitfield.Model

open Aeneas Aeneas.Std

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace NyxSszVerification

/-- Evaluate packed bytes with either a bounded tree or a progressive spine. -/
def packedRoot (data : Ssz.Bytes) (capacity : Option Nat) (length : Option Nat) :
    Except Ssz.Err Ssz.Bytes := do
  let root ← match capacity with
    | none => .ok (Ssz.merkleizeProgressive (Ssz.packBytes data).toList)
    | some cap => Ssz.merkleizeBounded (Ssz.packBytes data) (some cap)
  return match length with
    | none => root
    | some n => Ssz.mixIn root (Ssz.lengthWord n)

/-- A packed layout needs no recursive rooting of its leaves. -/
theorem hashTreeRootAt_packed (budget : Nat) (shape : Ssz.Desc) (value : Ssz.Value)
    (data : Ssz.Bytes) (capacity length : Option Nat)
    (layout : Ssz.merkleLayout shape value =
      .ok (.packing (Ssz.packBytes data) capacity (length.map Ssz.lengthWord))) :
    Ssz.hashTreeRootAt (budget + 1) shape value = packedRoot data capacity length := by
  cases capacity <;> cases length <;>
    simp [Ssz.hashTreeRootAt, layout, Ssz.layoutChunksAt, Ssz.MerkleLayout.packing,
      Ssz.Leaves.count, packedRoot, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Fixed byte vectors validate their declaration before checking the payload size. -/
theorem checkedHashTreeRoot_byteVector (n : Nat) (data : Ssz.Bytes) :
    checkedHashTreeRoot (.byteVector n) (.bytes data) =
      if n = 0 then .error .vectorEmpty
      else if data.size != n then .error (.scope n data.size)
      else packedRoot data (some (Ssz.chunksForBytes n)) none := by
  by_cases empty : n = 0
  · simp [checkedHashTreeRoot, Ssz.Desc.wellFormed, empty, Bind.bind, Except.bind]
  by_cases size : data.size = n
  · have layout : Ssz.merkleLayout (.byteVector n) (.bytes data) =
        .ok (.packing (Ssz.packBytes data) (some (Ssz.chunksForBytes n))) := by
      simp [Ssz.merkleLayout, Ssz.fixedLeaf, Ssz.serialize, size, Ssz.packBytes,
        Ssz.chunksForBytes, Bind.bind, Except.bind, Pure.pure, Except.pure]
    simpa [checkedHashTreeRoot, Ssz.Desc.wellFormed, Ssz.hashTreeRoot,
      Ssz.Desc.nesting, empty, size, Bind.bind, Except.bind] using
      hashTreeRootAt_packed 0 (.byteVector n) (.bytes data) data
        (some (Ssz.chunksForBytes n)) none layout
  · simp [checkedHashTreeRoot, Ssz.Desc.wellFormed, Ssz.hashTreeRoot,
      Ssz.Desc.nesting, Ssz.hashTreeRootAt, Ssz.merkleLayout, Ssz.fixedLeaf,
      Ssz.serialize, empty, size, Bind.bind, Except.bind]

/-- Bounded byte lists mix in the byte count, not the packed chunk count. -/
theorem checkedHashTreeRoot_byteList (limit : Nat) (data : Ssz.Bytes) :
    checkedHashTreeRoot (.byteList limit) (.bytes data) =
      if data.size > limit then .error (.overLimit limit data.size)
      else packedRoot data (some (Ssz.chunksForBytes limit)) (some data.size) := by
  by_cases over : data.size > limit
  · simp [checkedHashTreeRoot, Ssz.Desc.wellFormed, Ssz.hashTreeRoot,
      Ssz.Desc.nesting, Ssz.hashTreeRootAt, Ssz.merkleLayout, over,
      Bind.bind, Except.bind, MonadExcept.throw, throwThe, MonadExceptOf.throw]
  · have layout : Ssz.merkleLayout (.byteList limit) (.bytes data) =
        .ok (.packing (Ssz.packBytes data) (some (Ssz.chunksForBytes limit))
          ((some data.size).map Ssz.lengthWord)) := by
      simp [Ssz.merkleLayout, over, Bind.bind, Except.bind, Pure.pure, Except.pure]
    simpa [checkedHashTreeRoot, Ssz.Desc.wellFormed, Ssz.hashTreeRoot,
      Ssz.Desc.nesting, over, Bind.bind, Except.bind] using
      hashTreeRootAt_packed 0 (.byteList limit) (.bytes data) data
        (some (Ssz.chunksForBytes limit)) (some data.size) layout

/-- Bit-vector packing has no delimiter bit and no length mix-in. -/
theorem checkedHashTreeRoot_bitVector (n : Nat) (data : _root_.Array Bool) :
    checkedHashTreeRoot (.bitVector n) (.bits data) =
      if n = 0 then .error .vectorEmpty
      else if data.size != n then .error (.scope n data.size)
      else packedRoot (Ssz.packBits data ((data.size + 7) / 8))
        (some (Ssz.chunksForBits n)) none := by
  by_cases empty : n = 0
  · simp [checkedHashTreeRoot, Ssz.Desc.wellFormed, empty, Bind.bind, Except.bind]
  by_cases size : data.size = n
  · have layout : Ssz.merkleLayout (.bitVector n) (.bits data) =
        .ok (.packing (Ssz.packBytes (Ssz.packBits data ((data.size + 7) / 8)))
          (some (Ssz.chunksForBits n))) := by
      simp [Ssz.merkleLayout, Ssz.packedBits, size, Bind.bind, Except.bind,
        Pure.pure, Except.pure]
    simpa [checkedHashTreeRoot, Ssz.Desc.wellFormed, Ssz.hashTreeRoot,
      Ssz.Desc.nesting, empty, size, Bind.bind, Except.bind] using
      hashTreeRootAt_packed 0 (.bitVector n) (.bits data)
        (Ssz.packBits data ((data.size + 7) / 8)) (some (Ssz.chunksForBits n)) none layout
  · simp [checkedHashTreeRoot, Ssz.Desc.wellFormed, Ssz.hashTreeRoot,
      Ssz.Desc.nesting, Ssz.hashTreeRootAt, Ssz.merkleLayout, empty, size,
      Bind.bind, Except.bind, MonadExcept.throw, throwThe, MonadExceptOf.throw]

/-- Bounded bit lists mix in the bit count. -/
theorem checkedHashTreeRoot_bitList (limit : Nat) (data : _root_.Array Bool) :
    checkedHashTreeRoot (.bitList limit) (.bits data) =
      if data.size > limit then .error (.overLimit limit data.size)
      else packedRoot (Ssz.packBits data ((data.size + 7) / 8))
        (some (Ssz.chunksForBits limit)) (some data.size) := by
  by_cases over : data.size > limit
  · simp [checkedHashTreeRoot, Ssz.Desc.wellFormed, Ssz.hashTreeRoot,
      Ssz.Desc.nesting, Ssz.hashTreeRootAt, Ssz.merkleLayout, over,
      Bind.bind, Except.bind, MonadExcept.throw, throwThe, MonadExceptOf.throw]
  · have layout : Ssz.merkleLayout (.bitList limit) (.bits data) =
        .ok (.packing (Ssz.packBytes (Ssz.packBits data ((data.size + 7) / 8)))
          (some (Ssz.chunksForBits limit)) ((some data.size).map Ssz.lengthWord)) := by
      simp [Ssz.merkleLayout, Ssz.packedBits, over, Bind.bind, Except.bind,
        Pure.pure, Except.pure]
    simpa [checkedHashTreeRoot, Ssz.Desc.wellFormed, Ssz.hashTreeRoot,
      Ssz.Desc.nesting, over, Bind.bind, Except.bind] using
      hashTreeRootAt_packed 0 (.bitList limit) (.bits data)
        (Ssz.packBits data ((data.size + 7) / 8)) (some (Ssz.chunksForBits limit))
        (some data.size) layout

/-- Concatenating serialized uint8 values preserves exactly the original bytes. -/
theorem fold_byteParts (bytes : List U8) (initial : Ssz.Bytes) :
    (byteParts bytes).foldl (fun total part => total ++ part) initial =
      initial ++ bytesToSpec bytes := by
  induction bytes generalizing initial with
  | nil => simp [byteParts, bytesToSpec]
  | cons head tail ih =>
    change (byteParts tail).foldl (fun total part => total ++ part)
      (initial ++ #[byteToSpec head]) = initial ++ bytesToSpec (head :: tail)
    rw [ih, _root_.Array.append_assoc]
    congr 1
    apply _root_.Array.toList_inj.mp
    simp [bytesToSpec]

/-- The pinned layout deliberately ignores the progressive list's optional bound. -/
theorem checkedHashTreeRoot_progressiveByteList (bound : Option Nat) (bytes : List U8) :
    checkedHashTreeRoot (.progressiveList (.uint 1) bound) (.seq (byteValues bytes)) =
      packedRoot (bytesToSpec bytes) none (some bytes.length) := by
  have layout : Ssz.merkleLayout (.progressiveList (.uint 1) bound)
        (.seq (byteValues bytes)) =
      .ok (.packing (Ssz.packBytes (bytesToSpec bytes)) none
        ((some bytes.length).map Ssz.lengthWord)) := by
    simp [Ssz.merkleLayout, Ssz.sequenceLayout, Ssz.Desc.isBasic,
      serialize_byteValues, Ssz.packElements, fold_byteParts,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  simpa [checkedHashTreeRoot, Ssz.Desc.wellFormed, Ssz.hashTreeRoot,
    Ssz.Desc.nesting, Bind.bind, Except.bind] using
    hashTreeRootAt_packed 1 (.progressiveList (.uint 1) bound) (.seq (byteValues bytes))
      (bytesToSpec bytes) none (some bytes.length) layout

/-- Progressive bit roots likewise do not validate the optional bound. -/
theorem checkedHashTreeRoot_progressiveBitList (bound : Option Nat)
    (data : _root_.Array Bool) :
    checkedHashTreeRoot (.progressiveBitList bound) (.bits data) =
      packedRoot (Ssz.packBits data ((data.size + 7) / 8)) none (some data.size) := by
  have layout : Ssz.merkleLayout (.progressiveBitList bound) (.bits data) =
      .ok (.packing (Ssz.packBytes (Ssz.packBits data ((data.size + 7) / 8))) none
        ((some data.size).map Ssz.lengthWord)) := by
    rfl
  simpa [checkedHashTreeRoot, Ssz.Desc.wellFormed, Ssz.hashTreeRoot,
    Ssz.Desc.nesting, Bind.bind, Except.bind] using
    hashTreeRootAt_packed 0 (.progressiveBitList bound) (.bits data)
      (Ssz.packBits data ((data.size + 7) / 8)) none (some data.size) layout

/-- The observed boolean list has its original logical length. -/
theorem checkedHashTreeRoot_progressiveBits (bound : Option Nat) (bits : List Bool) :
    checkedHashTreeRoot (.progressiveBitList bound) (.bits (bitsToSpec bits)) =
      packedRoot (Ssz.packBits (bitsToSpec bits) ((bits.length + 7) / 8))
        none (some bits.length) := by
  simpa using checkedHashTreeRoot_progressiveBitList bound (bitsToSpec bits)

end NyxSszVerification
