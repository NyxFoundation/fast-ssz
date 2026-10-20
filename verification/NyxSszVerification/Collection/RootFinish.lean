import NyxSszVerification.Collection.LengthWord
import NyxSszVerification.Merkleize

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace NyxSszVerification

@[step] theorem collection_merkleize_success (chunks : Slice RustNode) (capacity : Usize)
    (within : chunks.val.length ≤ capacity.val) :
    NyxSszRust.merkle.merkleize chunks (some capacity) ⦃ actual =>
      ∃ root, actual = .Ok root ∧
        Ssz.merkleizeBounded (proofNodes chunks.val).toArray (some capacity.val) =
          .ok (bytesToSpec root.val) ⦄ := by
  apply spec_mono (merkleize_refines chunks (some capacity))
  intro actual correct
  have reference : Ssz.merkleizeBounded (proofNodes chunks.val).toArray (some capacity.val) =
      .ok (Ssz.subtreeAt (proofNodes chunks.val).toArray (Ssz.depthFor capacity.val) 0) := by
    simp [Ssz.merkleizeBounded, Nat.not_lt.mpr within, Bind.bind, Except.bind, Pure.pure, Except.pure]
  cases actual with
  | Err kind => cases kind; simp [reference, merkleizeAgrees] at correct
  | Ok root =>
    simp only [Option.map_some, reference, merkleizeAgrees] at correct
    exact ⟨root, rfl, by simpa only [correct] using reference⟩

/-- A checked bounded tree and its optional length mix-in use the exact same nodes. -/
theorem collection_root_finish (chunks : Slice RustNode) (capacity count : Usize) (mixLength : Bool)
    (within : chunks.val.length ≤ capacity.val) :
    (do
      let actual ← NyxSszRust.merkle.merkleize chunks (some capacity)
      match actual with
      | .Ok root =>
        if mixLength then
          let word ← NyxSszRust.tree_hash.hash_tree_root_u128 (UScalar.cast .U128 count)
          let result ← NyxSszRust.sha256.hash_pair root word
          RustM.ok (core.result.Result.Ok result)
        else RustM.ok (core.result.Result.Ok root)
      | .Err _ => RustM.ok (core.result.Result.Err NyxSszRust.error.CodecError.InvalidLength)) ⦃ actual =>
        codecRootAgrees actual (do
          let root ← Ssz.merkleizeBounded (proofNodes chunks.val).toArray (some capacity.val)
          return if mixLength then Ssz.mixIn root (Ssz.lengthWord count.val) else root) ⦄ := by
  apply spec_bind (collection_merkleize_success chunks capacity within)
  intro actual correct
  obtain ⟨root, same, reference⟩ := correct
  rw [same]
  cases hMix : mixLength
  · simp [reference, codecRootAgrees, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · simp only [if_true]
    apply spec_bind (collection_length_word_refines count)
    intro word wordPost
    apply spec_bind (hash_pair_spec root word)
    intro result resultPost
    simp [reference, codecRootAgrees, Ssz.mixIn, resultPost, wordPost,
      Bind.bind, Except.bind, Pure.pure, Except.pure]

end NyxSszVerification
