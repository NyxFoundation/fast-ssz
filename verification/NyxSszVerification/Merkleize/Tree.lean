import Ssz.Merkle.Tree
import Ssz.Proofs.Merkle.Merkleize

set_option maxRecDepth 4096
set_option maxHeartbeats 200000

namespace NyxSszVerification

/-- Re-establish cache laws over the pinned executable definitions. -/
theorem zero_cache_size (built : Nat) : (Ssz.zeroRootsUpTo built).size = built + 1 := by
  induction built with
  | zero => rfl
  | succ built ih => simp [Ssz.zeroRootsUpTo, ih]

theorem zero_cache_entry (built : Nat) : ∀ depth, depth ≤ built →
    (Ssz.zeroRootsUpTo built)[depth]?.getD Ssz.zeroChunk =
      Ssz.zeroRoot Ssz.combine Ssz.zeroChunk depth := by
  induction built with
  | zero =>
    intro depth covered
    have atZero : depth = 0 := by omega
    subst depth
    rfl
  | succ built ih =>
    intro depth covered
    have size := zero_cache_size built
    by_cases earlier : depth < built + 1
    · have different : depth ≠ (Ssz.zeroRootsUpTo built).size := by omega
      simp only [Ssz.zeroRootsUpTo, Array.getElem?_push, if_neg different]
      exact ih depth (by omega)
    · have last : depth = built + 1 := by omega
      subst depth
      simp only [Ssz.zeroRootsUpTo, Array.getElem?_push, if_pos size.symm,
        Option.getD_some, Ssz.zeroRoot]
      rw [ih built (Nat.le_refl built)]

theorem zero_subtree_recursive (depth : Nat) :
    Ssz.zeroSubtree depth = Ssz.zeroRoot Ssz.combine Ssz.zeroChunk depth := by
  by_cases covered : depth ≤ Ssz.maxZeroDepth
  · have inside : depth < Ssz.zeroRoots.size := by
      simpa [Ssz.zeroRoots, zero_cache_size] using Nat.lt_succ_of_le covered
    have entry : Ssz.zeroRoots[depth]?.getD Ssz.zeroChunk =
        Ssz.zeroRoot Ssz.combine Ssz.zeroChunk depth :=
      zero_cache_entry Ssz.maxZeroDepth depth covered
    simpa [Ssz.zeroSubtree, Array.getElem?_eq_getElem inside] using entry
  · have absent : Ssz.zeroRoots[depth]? = none := Array.getElem?_eq_none (by
      simp only [Ssz.zeroRoots, zero_cache_size]
      omega)
    simp [Ssz.zeroSubtree, absent]

theorem subtreeAt_recursive (chunks : Array Ssz.Bytes) (depth start : Nat) :
    Ssz.subtreeAt chunks depth start = Ssz.subtreeRoot Ssz.combine depth
      (fun position => Ssz.padded Ssz.zeroChunk chunks (start + position)) := by
  induction depth generalizing start with
  | zero =>
    rw [Ssz.subtreeAt]
    split
    · rename_i past
      rw [zero_subtree_recursive]
      have absent : chunks[start]? = none := Array.getElem?_eq_none (by omega)
      simp [Ssz.subtreeRoot, Ssz.zeroRoot, Ssz.padded, absent]
    · simp [Ssz.subtreeRoot, Ssz.padded]
  | succ depth ih =>
    rw [Ssz.subtreeAt]
    split
    · rename_i past
      rw [zero_subtree_recursive]
      exact (Ssz.subtreeRoot_padded_past_data Ssz.combine Ssz.zeroChunk
        (depth + 1) chunks (by omega)).symm
    · rw [Ssz.subtreeRoot, ih start, ih (start + 2 ^ depth)]
      congr 2
      funext position
      congr 1
      omega

end NyxSszVerification
