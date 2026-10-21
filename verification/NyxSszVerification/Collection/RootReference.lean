import NyxSszVerification.Collection.RootElements

open Aeneas Aeneas.Std

namespace NyxSszVerification

/-- The reference sequence tree, sharing the child's exact observation and root budget. -/
def collectionSequenceRoot (shape : Ssz.Desc) (values : List Ssz.Value)
    (positions : Nat) (mixLength : Bool) : Except Ssz.Err Ssz.Bytes := do
  let chunks ← if shape.isBasic then do
    let parts ← Ssz.serializeEach shape values
    pure (Ssz.packElements parts)
  else do
    let roots ← collectionRootEach shape values
    pure roots.toArray
  let capacity := if shape.isBasic then Ssz.chunksForBytes (positions * shape.itemLength) else positions
  let root ← Ssz.merkleizeBounded chunks (some capacity)
  return if mixLength then Ssz.mixIn root (Ssz.lengthWord values.length) else root

theorem collection_nested_chunks (shape : Ssz.Desc) (values : List Ssz.Value)
    (positions : Nat) (word : Option Ssz.Bytes) :
    Ssz.layoutChunksAt shape.nesting
      (Ssz.MerkleLayout.nesting (values.map fun value => some (shape, value)) (some positions) word) =
      (collectionRootEach shape values).map List.toArray := by
  simp [Ssz.layoutChunksAt, Ssz.MerkleLayout.nesting, Ssz.Leaves.count,
    collectionRootEach, ← List.map_take, List.mapM_map, Function.comp_def,
    Functor.map, Except.map]
  rfl

theorem collection_vector_root_form (shape : Ssz.Desc) (positions : Nat) (values : List Ssz.Value)
    (length : values.length = positions) :
    Ssz.hashTreeRoot (.vector shape positions) (.seq values) =
      collectionSequenceRoot shape values positions false := by
  simp only [Ssz.hashTreeRoot, Ssz.Desc.nesting, Ssz.hashTreeRootAt, Ssz.merkleLayout,
    length, bne_self_eq_false, Bool.false_eq_true, if_false]
  by_cases basic : shape.isBasic = true
  · cases parts : Ssz.serializeEach shape values <;>
      simp [Ssz.sequenceLayout, basic, Ssz.layoutChunksAt, Ssz.MerkleLayout.packing,
        Ssz.Leaves.count, collectionSequenceRoot, parts, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · simp only [Ssz.sequenceLayout, if_neg basic, Bind.bind, Except.bind, Pure.pure, Except.pure]
    rw [collection_nested_chunks]
    cases roots : collectionRootEach shape values <;>
      simp [collectionSequenceRoot, basic, roots, Ssz.MerkleLayout.nesting,
        Bind.bind, Except.bind, Except.map, Pure.pure, Except.pure]

theorem collection_list_root_form (shape : Ssz.Desc) (positions : Nat) (values : List Ssz.Value)
    (length : values.length ≤ positions) :
    Ssz.hashTreeRoot (.list shape positions) (.seq values) =
      collectionSequenceRoot shape values positions true := by
  simp only [Ssz.hashTreeRoot, Ssz.Desc.nesting, Ssz.hashTreeRootAt, Ssz.merkleLayout,
    if_neg (Nat.not_lt.mpr length)]
  by_cases basic : shape.isBasic = true
  · cases parts : Ssz.serializeEach shape values <;>
      simp [Ssz.sequenceLayout, basic, Ssz.layoutChunksAt, Ssz.MerkleLayout.packing,
        Ssz.Leaves.count, collectionSequenceRoot, parts, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · simp only [Ssz.sequenceLayout, if_neg basic, Bind.bind, Except.bind, Pure.pure, Except.pure]
    rw [collection_nested_chunks]
    cases roots : collectionRootEach shape values <;>
      simp [collectionSequenceRoot, basic, roots, Ssz.MerkleLayout.nesting,
        Bind.bind, Except.bind, Except.map, Pure.pure, Except.pure]

end NyxSszVerification
