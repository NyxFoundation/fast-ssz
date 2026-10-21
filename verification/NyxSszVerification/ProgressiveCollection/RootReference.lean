import NyxSszVerification.Collection.RootReference

open Aeneas Aeneas.Std

namespace NyxSszVerification

/-- An unbounded progressive spine over packed basic elements or exact child roots. -/
def progressiveCollectionRoot (shape : Ssz.Desc) (values : List Ssz.Value) :
    Except Ssz.Err Ssz.Bytes := do
  let chunks ← if shape.isBasic then do
    let parts ← Ssz.serializeEach shape values
    pure (Ssz.packElements parts)
  else do
    let roots ← collectionRootEach shape values
    pure roots.toArray
  return Ssz.mixIn (Ssz.merkleizeProgressive chunks.toList) (Ssz.lengthWord values.length)

theorem progressive_collection_nested_chunks (shape : Ssz.Desc) (values : List Ssz.Value)
    (word : Option Ssz.Bytes) :
    Ssz.layoutChunksAt shape.nesting
      (Ssz.MerkleLayout.nesting (values.map fun value => some (shape, value)) none word) =
      (collectionRootEach shape values).map List.toArray := by
  simp [Ssz.layoutChunksAt, Ssz.MerkleLayout.nesting, Ssz.Leaves.count,
    collectionRootEach, ← List.map_take, List.mapM_map, Function.comp_def,
    Functor.map, Except.map]
  rfl

theorem progressive_collection_root_form (shape : Ssz.Desc) (values : List Ssz.Value) :
    Ssz.hashTreeRoot (.progressiveList shape none) (.seq values) =
      progressiveCollectionRoot shape values := by
  simp only [Ssz.hashTreeRoot, Ssz.Desc.nesting, Ssz.hashTreeRootAt, Ssz.merkleLayout]
  by_cases basic : shape.isBasic = true
  · cases parts : Ssz.serializeEach shape values <;>
      simp [Ssz.sequenceLayout, basic, Ssz.layoutChunksAt, Ssz.MerkleLayout.packing,
        Ssz.Leaves.count, progressiveCollectionRoot, parts,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
  · simp only [Ssz.sequenceLayout, if_neg basic, Bind.bind, Except.bind, Pure.pure, Except.pure]
    rw [progressive_collection_nested_chunks]
    cases roots : collectionRootEach shape values <;>
      simp [progressiveCollectionRoot, basic, roots, Ssz.MerkleLayout.nesting,
        Bind.bind, Except.bind, Except.map, Pure.pure, Except.pure]

end NyxSszVerification
