import NyxSszVerification.Multiproof.Helpers

/-! Kernel lemmas for the pinned executable frontier, independent of upstream
proof modules that require the upstream Lean version. -/

namespace Ssz

theorem two_le_of_level_positive {index depth : Nat}
    (level : levelOf index = depth) (positive : 0 < depth) : 2 ≤ index := by
  by_contra small
  have cases : index = 0 ∨ index = 1 := by omega
  rcases cases with rfl | rfl <;> simp [levelOf] at level <;> omega

theorem gindexLength_ok {index depth : Nat} (measured : gindexLength index = .ok depth) :
    depth = index.log2 ∧ 0 < depth ∧ 1 ≤ index := by
  by_cases zero : index = 0
  · simp [zero, gindexLength, gindexDepth, Bind.bind, Except.bind] at measured
  by_cases root : index = 1
  · simp [root, gindexLength, gindexDepth, Bind.bind, Except.bind] at measured
  have lower : 2 ≤ index := by omega
  rw [NyxSszVerification.gindex_length_positive index lower] at measured
  have same : index.log2 = depth := Except.ok.inj measured
  exact ⟨same.symm, same ▸ NyxSszVerification.index_depth_positive index lower, by omega⟩

def claimPaths (indices : List Nat) : List Nat :=
  indices.flatMap fun index => (List.range index.log2).map fun step => index >>> step

theorem collectPathIndices_info {indices paths : List Nat}
    (collected : collectPathIndices indices = .ok paths) :
    paths = claimPaths indices ∧ ∀ index ∈ indices, 2 ≤ index := by
  induction indices generalizing paths with
  | nil => simpa [collectPathIndices, claimPaths] using collected.symm
  | cons index rest ih =>
    rw [collectPathIndices] at collected
    cases measured : gindexLength index with
    | error fault => simp [getPathIndices, measured, Bind.bind, Except.bind] at collected
    | ok depth =>
      obtain ⟨rfl, positive, _⟩ := gindexLength_ok measured
      cases rec : collectPathIndices rest with
      | error fault => simp [getPathIndices, measured, rec, Bind.bind, Except.bind,
          Pure.pure, Except.pure] at collected
      | ok remaining =>
        obtain ⟨shape, valid⟩ := ih rec
        simp [getPathIndices, measured, rec, Bind.bind, Except.bind, Pure.pure,
          Except.pure] at collected
        subst paths
        refine ⟨by rw [shape]; rfl, ?_⟩
        intro i member
        rcases List.mem_cons.mp member with rfl | member
        · exact two_le_of_level_positive rfl positive
        · exact valid i member

theorem getHelperIndices_frontier {indices helpers : List Nat}
    (built : getHelperIndices indices = .ok helpers) :
    indices ≠ [] ∧ (∀ index ∈ indices, 2 ≤ index) ∧
      ∀ index, index ∈ helpers ↔
        index ∈ (claimPaths indices).map gindexSibling ∧ index ∉ claimPaths indices := by
  unfold getHelperIndices at built
  cases accepted : rejectRelated indices with
  | error fault => simp [accepted, Bind.bind, Except.bind] at built
  | ok checked =>
    have nonempty : indices ≠ [] := by
      intro empty
      simp [empty, rejectRelated, throw, throwThe, MonadExceptOf.throw,
        Bind.bind, Except.bind] at accepted
    cases collected : collectPathIndices indices with
    | error fault => simp [accepted, collected, Bind.bind, Except.bind] at built
    | ok paths =>
      obtain ⟨shape, valid⟩ := collectPathIndices_info collected
      simp [accepted, collected, Bind.bind, Except.bind, Pure.pure, Except.pure] at built
      subst helpers
      refine ⟨nonempty, valid, ?_⟩
      intro index
      simp [List.mem_mergeSort, shape]

theorem path_shift_positive {index step : Nat} (named : 1 ≤ index)
    (below : step < index.log2) : 2 ≤ index >>> step := by
  have reaches := shiftRight_depth named
  have distance : step + 1 + (index.log2 - (step + 1)) = index.log2 := by omega
  have upper : 1 ≤ index >>> (step + 1) := by
    have small := Nat.shiftRight_le (index >>> (step + 1)) (index.log2 - (step + 1))
    rw [← Nat.shiftRight_add, distance, reaches] at small
    exact small
  rw [shiftRight_succ] at upper
  omega

theorem claimPaths_bounds {indices : List Nat} (valid : ∀ index ∈ indices, 2 ≤ index)
    {index : Nat} (member : index ∈ claimPaths indices) :
    2 ≤ index ∧ ∃ claim ∈ indices, index ≤ claim := by
  obtain ⟨claim, claimed, stepMember⟩ := List.mem_flatMap.mp member
  obtain ⟨step, inRange, rfl⟩ := List.mem_map.mp stepMember
  exact ⟨path_shift_positive (by have := valid claim claimed; omega)
    (List.mem_range.mp inRange), claim, claimed, Nat.shiftRight_le _ _⟩

theorem claimPaths_child {indices : List Nat} (nonempty : indices ≠ [])
    (valid : ∀ index ∈ indices, 2 ≤ index) {index : Nat}
    (inside : index = 1 ∨ index ∈ claimPaths indices) (unclaimed : index ∉ indices) :
    ∃ child ∈ claimPaths indices, child / 2 = index := by
  rcases inside with rfl | member
  · obtain ⟨claim, claimed⟩ := List.exists_mem_of_ne_nil indices nonempty
    have named : 1 ≤ claim := by have := valid claim claimed; omega
    have deep := NyxSszVerification.index_depth_positive claim (valid claim claimed)
    refine ⟨claim >>> (claim.log2 - 1), ?_, ?_⟩
    · exact List.mem_flatMap.mpr ⟨claim, claimed,
        List.mem_map.mpr ⟨claim.log2 - 1, List.mem_range.mpr (by omega), rfl⟩⟩
    · rw [← shiftRight_succ, show claim.log2 - 1 + 1 = claim.log2 by omega,
        shiftRight_depth named]
  · obtain ⟨claim, claimed, stepMember⟩ := List.mem_flatMap.mp member
    obtain ⟨step, inRange, same⟩ := List.mem_map.mp stepMember
    have positive : 0 < step := by
      by_contra notPositive
      have zero : step = 0 := by omega
      simp only [zero, Nat.shiftRight_zero] at same
      exact unclaimed (same ▸ claimed)
    refine ⟨claim >>> (step - 1), ?_, ?_⟩
    · exact List.mem_flatMap.mpr ⟨claim, claimed,
        List.mem_map.mpr ⟨step - 1, List.mem_range.mpr
          (by have := List.mem_range.mp inRange; omega), rfl⟩⟩
    · rw [← shiftRight_succ, show step - 1 + 1 = step by omega, same]

theorem helperFrontier_children {indices helpers : List Nat}
    (built : getHelperIndices indices = .ok helpers) {index : Nat}
    (inside : index = 1 ∨ index ∈ claimPaths indices) (unclaimed : index ∉ indices) :
    (2 * index ∈ claimPaths indices ∨ 2 * index ∈ helpers) ∧
    (2 * index + 1 ∈ claimPaths indices ∨ 2 * index + 1 ∈ helpers) := by
  obtain ⟨nonempty, valid, shape⟩ := getHelperIndices_frontier built
  obtain ⟨child, member, parent⟩ := claimPaths_child nonempty valid inside unclaimed
  have sibling : gindexSibling child ∈ claimPaths indices ∨ gindexSibling child ∈ helpers := by
    by_cases onPath : gindexSibling child ∈ claimPaths indices
    · exact Or.inl onPath
    · exact Or.inr ((shape _).mpr ⟨List.mem_map.mpr ⟨child, member, rfl⟩, onPath⟩)
  rcases Nat.mod_two_eq_zero_or_one child with even | odd
  · obtain ⟨left, right⟩ := gindexSibling_even even
    rw [parent] at left right
    exact ⟨Or.inl (left ▸ member), right ▸ sibling⟩
  · obtain ⟨right, left⟩ := gindexSibling_odd odd
    rw [parent] at left right
    exact ⟨left ▸ sibling, Or.inl (right ▸ member)⟩

theorem levelOf_parent {index : Nat} (below : 2 ≤ index) :
    levelOf index = levelOf (index / 2) + 1 :=
  (Nat.log2_def index).trans (if_pos below)

theorem levelOf_sibling {index : Nat} (below : 2 ≤ index) :
    levelOf (gindexSibling index) = levelOf index := by
  have half := gindexSibling_half index
  have other : 2 ≤ gindexSibling index := by omega
  rw [levelOf_parent other, half, ← levelOf_parent below]

theorem levelOf_mono {left right : Nat} (positive : 1 ≤ left) (ordered : left ≤ right) :
    levelOf left ≤ levelOf right := by
  apply (Nat.le_log2 (by omega : right ≠ 0)).mpr
  exact Nat.le_trans (Nat.log2_self_le (by omega)) ordered

theorem claim_mem_paths {indices : List Nat} (valid : ∀ index ∈ indices, 2 ≤ index)
    {index : Nat} (claimed : index ∈ indices) : index ∈ claimPaths indices := by
  have positive := NyxSszVerification.index_depth_positive index (valid index claimed)
  exact List.mem_flatMap.mpr ⟨index, claimed,
    List.mem_map.mpr ⟨0, List.mem_range.mpr positive, by simp⟩⟩

theorem claimPaths_parent {indices : List Nat} (valid : ∀ index ∈ indices, 2 ≤ index)
    {index : Nat} (member : index ∈ claimPaths indices) :
    index / 2 = 1 ∨ index / 2 ∈ claimPaths indices := by
  obtain ⟨claim, claimed, stepMember⟩ := List.mem_flatMap.mp member
  obtain ⟨step, inRange, same⟩ := List.mem_map.mp stepMember
  rw [← same, ← shiftRight_succ]
  have below := List.mem_range.mp inRange
  by_cases last : step + 1 = claim.log2
  · exact Or.inl (by rw [last, shiftRight_depth (by have := valid claim claimed; omega)])
  · exact Or.inr (List.mem_flatMap.mpr ⟨claim, claimed,
      List.mem_map.mpr ⟨step + 1, List.mem_range.mpr (by omega), rfl⟩⟩)

theorem helperFrontier_sibling {indices helpers : List Nat}
    (built : getHelperIndices indices = .ok helpers) {index : Nat}
    (member : index ∈ claimPaths indices ∨ index ∈ helpers) :
    2 ≤ index ∧ (gindexSibling index ∈ claimPaths indices ∨ gindexSibling index ∈ helpers) ∧
      (index / 2 = 1 ∨ index / 2 ∈ claimPaths indices) := by
  obtain ⟨_, valid, shape⟩ := getHelperIndices_frontier built
  rcases member with path | helper
  · have positive := (claimPaths_bounds valid path).1
    refine ⟨positive, ?_, claimPaths_parent valid path⟩
    by_cases siblingPath : gindexSibling index ∈ claimPaths indices
    · exact Or.inl siblingPath
    · exact Or.inr ((shape _).mpr ⟨List.mem_map.mpr ⟨index, path, rfl⟩, siblingPath⟩)
  · obtain ⟨mapped, _⟩ := (shape index).mp helper
    obtain ⟨sibling, path, rfl⟩ := List.mem_map.mp mapped
    have positive := (claimPaths_bounds valid path).1
    have half := gindexSibling_half sibling
    refine ⟨by omega, ?_, ?_⟩
    · exact Or.inl (by simpa only [gindexSibling_sibling] using path)
    · rw [half]
      exact claimPaths_parent valid path

end Ssz
