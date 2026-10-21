import NyxSszVerification.Multiproof.Antichain

namespace Ssz

theorem nodeAt_exists {nodes : List (Nat × Bytes)} {index : Nat} {value : Bytes}
    (member : (index, value) ∈ nodes) : ∃ found, nodeAt nodes index = some found := by
  induction nodes with
  | nil => simp at member
  | cons pair rest ih =>
    rcases pair with ⟨at_, stored⟩
    by_cases same : at_ = index
    · subst at_
      exact ⟨stored, by simp [nodeAt]⟩
    · have tail : (index, value) ∈ rest := by simpa [same, Ne.symm same] using member
      obtain ⟨found, located⟩ := ih tail
      exact ⟨found, by simpa [nodeAt, same] using located⟩

theorem nodeAt_member {nodes : List (Nat × Bytes)} {index : Nat} {value : Bytes}
    (found : nodeAt nodes index = some value) : (index, value) ∈ nodes := by
  unfold nodeAt at found
  cases located : nodes.find? (fun pair => pair.1 == index) with
  | none => simp [located] at found
  | some pair =>
    have member := List.mem_of_find?_eq_some located
    have named := List.find?_some located
    simp only [beq_iff_eq] at named
    simp only [located, Option.map_some, Option.some.injEq] at found
    rw [← found, ← named]
    exact member

def SiblingsPresent (depth : Nat) (nodes pending : List (Nat × Bytes)) : Prop :=
  ∀ index value, (index, value) ∈ pending → levelOf index = depth →
    ∃ sibling, (gindexSibling index, sibling) ∈ nodes

theorem foldLevelNodes_complete {depth : Nat} {nodes pending : List (Nat × Bytes)}
    (covered : SiblingsPresent depth nodes pending) :
    ∃ parents kept, foldLevelNodes depth nodes pending = .ok (parents, kept) := by
  induction pending with
  | nil => exact ⟨[], [], rfl⟩
  | cons pair rest ih =>
    rcases pair with ⟨index, value⟩
    have tail : SiblingsPresent depth nodes rest :=
      fun i v member level => covered i v (by simp [member]) level
    obtain ⟨ps, ks, rec⟩ := ih tail
    by_cases atDepth : levelOf index = depth
    · obtain ⟨sibling, member⟩ := covered index value (by simp) atDepth
      obtain ⟨found, located⟩ := nodeAt_exists member
      rcases Nat.mod_two_eq_zero_or_one index with even | odd
      · obtain ⟨whole, siblingIndex⟩ := gindexSibling_even even
        have siblingIndex : gindexSibling index = index + 1 := by omega
        rw [siblingIndex] at located
        exact ⟨(gindexParent index, combine value found) :: ps, ks,
          by simp [foldLevelNodes, atDepth, even, located, rec,
            Bind.bind, Except.bind, Pure.pure, Except.pure]⟩
      · obtain ⟨whole, siblingIndex⟩ := gindexSibling_odd odd
        have siblingIndex : gindexSibling index = index - 1 := by omega
        rw [siblingIndex] at located
        exact ⟨ps, ks, by simp [foldLevelNodes, atDepth, odd, located, rec]⟩
    · exact ⟨ps, (index, value) :: ks,
        by simp [foldLevelNodes, atDepth, rec, Bind.bind, Except.bind, Pure.pure, Except.pure]⟩

theorem foldLevel_complete {depth : Nat} {nodes : List (Nat × Bytes)}
    (covered : SiblingsPresent depth nodes nodes) :
    ∃ result, foldLevel depth nodes = .ok result := by
  obtain ⟨parents, kept, built⟩ := foldLevelNodes_complete covered
  exact ⟨parents ++ kept,
    by simp [foldLevel, built, Bind.bind, Except.bind, Pure.pure, Except.pure]⟩

def FoldedIndex (depth child index : Nat) : Prop :=
  (levelOf child ≠ depth ∧ index = child) ∨
    (levelOf child = depth ∧ child % 2 = 0 ∧ index = gindexParent child)

theorem foldLevelNodes_indices {depth : Nat} {nodes pending : List (Nat × Bytes)}
    {parents kept : List (Nat × Bytes)}
    (built : foldLevelNodes depth nodes pending = .ok (parents, kept)) :
    ∀ index, index ∈ (parents ++ kept).map Prod.fst ↔
      ∃ child ∈ pending.map Prod.fst, FoldedIndex depth child index := by
  induction pending generalizing parents kept with
  | nil =>
    simp [foldLevelNodes] at built
    rcases built with ⟨rfl, rfl⟩
    simp
  | cons pair rest ih =>
    rcases pair with ⟨child, value⟩
    by_cases atDepth : levelOf child = depth
    · rcases Nat.mod_two_eq_zero_or_one child with even | odd
      · cases sibling : nodeAt nodes (child + 1) with
        | none => simp [foldLevelNodes, atDepth, even, sibling, throw] at built
        | some found =>
          cases rec : foldLevelNodes depth nodes rest with
          | error fault => simp [foldLevelNodes, atDepth, even, sibling, rec, Bind.bind, Except.bind] at built
          | ok result =>
            rcases result with ⟨ps, ks⟩
            simp [foldLevelNodes, atDepth, even, sibling, rec, Bind.bind, Except.bind,
              Pure.pure, Except.pure] at built
            rcases built with ⟨rfl, rfl⟩
            intro index
            simpa [FoldedIndex, atDepth, even, List.map_append, List.mem_append] using
              or_congr (Iff.rfl : (index = gindexParent child) ↔ _) (ih rec index)
      · cases sibling : nodeAt nodes (child - 1) with
        | none => simp [foldLevelNodes, atDepth, odd, sibling, throw] at built
        | some found =>
          have rebuilt : foldLevelNodes depth nodes rest = .ok (parents, kept) := by
            simpa [foldLevelNodes, atDepth, odd, sibling] using built
          intro index
          simpa [FoldedIndex, atDepth, odd] using ih rebuilt index
    · cases rec : foldLevelNodes depth nodes rest with
      | error fault => simp [foldLevelNodes, atDepth, rec, Bind.bind, Except.bind] at built
      | ok result =>
        rcases result with ⟨ps, ks⟩
        simp [foldLevelNodes, atDepth, rec, Bind.bind, Except.bind, Pure.pure, Except.pure] at built
        rcases built with ⟨rfl, rfl⟩
        intro index
        simpa [FoldedIndex, atDepth, List.map_append, List.mem_append,
          or_comm, or_left_comm, or_assoc] using
          or_congr (Iff.rfl : (index = child) ↔ _) (ih rec index)

theorem foldLevel_indices {depth : Nat} {nodes result : List (Nat × Bytes)}
    (built : foldLevel depth nodes = .ok result) :
    ∀ index, index ∈ result.map Prod.fst ↔
      ∃ child ∈ nodes.map Prod.fst, FoldedIndex depth child index := by
  unfold foldLevel at built
  cases rec : foldLevelNodes depth nodes nodes with
  | error fault => simp [rec, Bind.bind, Except.bind] at built
  | ok groups =>
    rcases groups with ⟨parents, kept⟩
    simp [rec, Bind.bind, Except.bind, Pure.pure, Except.pure] at built
    subst result
    exact foldLevelNodes_indices rec

def FrontierAt (indices helpers : List Nat) (depth : Nat) (nodes : List (Nat × Bytes)) : Prop :=
  (∀ index ∈ nodes.map Prod.fst, levelOf index ≤ depth ∧
    (index = 1 ∨ index ∈ claimPaths indices ∨ index ∈ helpers)) ∧
  (∀ index ∈ indices ++ helpers, levelOf index ≤ depth → index ∈ nodes.map Prod.fst) ∧
  (∀ index, (index = 1 ∨ index ∈ claimPaths indices) → levelOf index = depth →
    index ∈ nodes.map Prod.fst)

theorem FrontierAt.siblings {indices helpers : List Nat}
    (built : getHelperIndices indices = .ok helpers) {depth : Nat}
    {nodes : List (Nat × Bytes)} (frontier : FrontierAt indices helpers (depth + 1) nodes) :
    SiblingsPresent (depth + 1) nodes nodes := by
  intro index value member atDepth
  obtain ⟨_, support⟩ := frontier.1 index (List.mem_map.mpr ⟨(index, value), member, rfl⟩)
  have support : index ∈ claimPaths indices ∨ index ∈ helpers := by
    rcases support with root | support
    · subst index; have rootLevel : levelOf 1 = 0 := rfl; omega
    · exact support
  obtain ⟨positive, sibling, _⟩ := helperFrontier_sibling built support
  have sameDepth : levelOf (gindexSibling index) = depth + 1 :=
    (levelOf_sibling positive).trans atDepth
  have located : gindexSibling index ∈ nodes.map Prod.fst := by
    rcases sibling with path | helper
    · exact frontier.2.2 _ (Or.inr path) sameDepth
    · exact frontier.2.1 _ (List.mem_append.mpr (Or.inr helper)) (by omega)
  obtain ⟨pair, member, same⟩ := List.mem_map.mp located
  exact ⟨pair.2, by cases pair; simpa using same ▸ member⟩

theorem FrontierAt.fold {indices helpers : List Nat}
    (built : getHelperIndices indices = .ok helpers) {depth : Nat}
    {nodes result : List (Nat × Bytes)} (frontier : FrontierAt indices helpers (depth + 1) nodes)
    (folded : foldLevel (depth + 1) nodes = .ok result) :
    FrontierAt indices helpers depth result := by
  obtain ⟨nonempty, valid, _⟩ := getHelperIndices_frontier built
  have positions := foldLevel_indices folded
  refine ⟨?_, ?_, ?_⟩
  · intro index member
    obtain ⟨child, childMember, retained | joined⟩ := (positions index).mp member
    · obtain ⟨different, same⟩ := retained
      subst index
      obtain ⟨bounded, support⟩ := frontier.1 child childMember
      exact ⟨by omega, support⟩
    · obtain ⟨atDepth, _, same⟩ := joined
      subst index
      obtain ⟨_, support⟩ := frontier.1 child childMember
      have positive := two_le_of_level_positive atDepth (by omega)
      have support : child ∈ claimPaths indices ∨ child ∈ helpers := by
        rcases support with root | support
        · subst child; have : levelOf 1 = 0 := rfl; omega
        · exact support
      have parent := (helperFrontier_sibling built support).2.2
      have parentDepth := levelOf_parent positive
      exact ⟨by unfold gindexParent; omega, parent.elim Or.inl (fun path => Or.inr (Or.inl path))⟩
  · intro index member bounded
    apply (positions index).mpr
    exact ⟨index, frontier.2.1 index member (by omega), Or.inl ⟨by omega, rfl⟩⟩
  · intro index inside atDepth
    by_cases claimed : index ∈ indices
    · apply (positions index).mpr
      exact ⟨index, frontier.2.1 index (List.mem_append.mpr (Or.inl claimed)) (by omega),
        Or.inl ⟨by omega, rfl⟩⟩
    · obtain ⟨left, _⟩ := helperFrontier_children built inside claimed
      have positive : 1 ≤ index := by
        rcases inside with root | path
        · omega
        · have := (claimPaths_bounds valid path).1; omega
      have childDepth : levelOf (2 * index) = depth + 1 := by
        exact (Nat.log2_two_mul (by omega)).trans (congrArg (· + 1) atDepth)
      have childMember : 2 * index ∈ nodes.map Prod.fst := by
        rcases left with path | helper
        · exact frontier.2.2 _ (Or.inr path) childDepth
        · exact frontier.2.1 _ (List.mem_append.mpr (Or.inr helper)) (by omega)
      apply (positions index).mpr
      exact ⟨2 * index, childMember, Or.inr ⟨childDepth, by omega, by unfold gindexParent; omega⟩⟩

theorem FrontierAt.complete {indices helpers : List Nat}
    (built : getHelperIndices indices = .ok helpers) :
    ∀ depth nodes, FrontierAt indices helpers depth nodes →
      ∃ root, foldToRoot depth nodes = .ok root := by
  intro depth
  induction depth with
  | zero =>
    intro nodes frontier
    obtain ⟨pair, member, same⟩ := List.mem_map.mp (frontier.2.2 1 (Or.inl rfl) rfl)
    have rootMember : (1, pair.2) ∈ nodes := by cases pair; simpa using same ▸ member
    obtain ⟨root, found⟩ := nodeAt_exists rootMember
    exact ⟨root, by simp [foldToRoot, found]⟩
  | succ depth ih =>
    intro nodes frontier
    obtain ⟨result, folded⟩ := foldLevel_complete (frontier.siblings built)
    obtain ⟨root, reconstructed⟩ := ih result (frontier.fold built folded)
    exact ⟨root, by simp [foldToRoot, folded, reconstructed, Bind.bind, Except.bind]⟩

theorem frontierAt_initial {indices helpers : List Nat}
    (built : getHelperIndices indices = .ok helpers) {depth : Nat}
    {nodes : List (Nat × Bytes)} (positions : nodes.map Prod.fst = indices ++ helpers)
    (bounded : ∀ index ∈ indices ++ helpers, levelOf index ≤ depth) :
    FrontierAt indices helpers depth nodes := by
  obtain ⟨nonempty, valid, _⟩ := getHelperIndices_frontier built
  obtain ⟨claim, claimed⟩ := List.exists_mem_of_ne_nil indices nonempty
  have positive : 0 < depth := by
    have claimDepth := levelOf_parent (valid claim claimed)
    have claimBound := bounded claim (List.mem_append.mpr (Or.inl claimed))
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro index member
    rw [positions] at member
    refine ⟨bounded index member, ?_⟩
    rcases List.mem_append.mp member with requested | helper
    · exact Or.inr (Or.inl (claim_mem_paths valid requested))
    · exact Or.inr (Or.inr helper)
  · intro index member _
    rw [positions]
    exact member
  · intro index inside atDepth
    rw [positions]
    by_cases requested : index ∈ indices
    · exact List.mem_append.mpr (Or.inl requested)
    · obtain ⟨child, childPath, parent⟩ := claimPaths_child nonempty valid inside requested
      obtain ⟨childPositive, larger, largerClaimed, ordered⟩ := claimPaths_bounds valid childPath
      have parentDepth := levelOf_parent childPositive
      rw [parent, atDepth] at parentDepth
      have monotone := levelOf_mono (by omega) ordered
      have bound := bounded larger (List.mem_append.mpr (Or.inl largerClaimed))
      omega

theorem le_foldl_max (values : List Nat) (initial : Nat) : initial ≤ values.foldl max initial := by
  induction values generalizing initial with
  | nil => exact Nat.le_refl _
  | cons value rest ih => exact Nat.le_trans (Nat.le_max_left initial value) (ih (max initial value))

theorem member_le_foldl_max {values : List Nat} {value : Nat} (member : value ∈ values)
    (initial : Nat) : value ≤ values.foldl max initial := by
  induction values generalizing initial with
  | nil => simp at member
  | cons head rest ih =>
    rcases List.mem_cons.mp member with same | member
    · subst value
      exact Nat.le_trans (Nat.le_max_right initial head) (le_foldl_max rest (max initial head))
    · exact ih member (max initial head)

theorem calculateMultiMerkleRoot_complete {leaves proof : List Bytes} {indices helpers : List Nat}
    (built : getHelperIndices indices = .ok helpers)
    (leafCount : leaves.length = indices.length) (proofCount : proof.length = helpers.length) :
    ∃ root, calculateMultiMerkleRoot leaves proof indices = .ok root := by
  let nodes := indices.zip leaves ++ helpers.zip proof
  have positions : nodes.map Prod.fst = indices ++ helpers := by
    simp only [nodes, List.map_append, List.map_fst_zip (by omega : indices.length ≤ leaves.length),
      List.map_fst_zip (by omega : helpers.length ≤ proof.length)]
  let depth := (nodes.map fun pair => levelOf pair.1).foldl max 0
  have bounded : ∀ index ∈ indices ++ helpers, levelOf index ≤ depth := by
    intro index member
    rw [← positions] at member
    obtain ⟨pair, pairMember, same⟩ := List.mem_map.mp member
    exact member_le_foldl_max (List.mem_map.mpr ⟨pair, pairMember, congrArg levelOf same⟩) 0
  obtain ⟨root, reconstructed⟩ := (frontierAt_initial built positions bounded).complete built
  exact ⟨root, by simpa [calculateMultiMerkleRoot, leafCount, proofCount, built, nodes, depth,
    Bind.bind, Except.bind, Pure.pure, Except.pure] using reconstructed⟩

end Ssz
