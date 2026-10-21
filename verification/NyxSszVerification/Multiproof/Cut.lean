import NyxSszVerification.Multiproof.Fold

namespace Ssz

/-- A finite reconstruction stopping exactly at supplied frontier nodes. -/
def cutRoot (nodes : List (Nat × Bytes)) : Nat → Nat → Bytes
  | 0, index => (nodeAt nodes index).getD zeroChunk
  | height + 1, index => match nodeAt nodes index with
    | some value => value
    | none => combine (cutRoot nodes height (2 * index)) (cutRoot nodes height (2 * index + 1))

def cutNode (source : List (Nat × Bytes)) (height index : Nat) : Bytes :=
  cutRoot source (height - levelOf index) index

def ProofAntichain (nodes : List (Nat × Bytes)) : Prop :=
  ∀ i ∈ nodes.map Prod.fst, ∀ j ∈ nodes.map Prod.fst, ∀ step, i >>> step = j → i = j

def ProofSupported (source nodes : List (Nat × Bytes)) : Prop :=
  ∀ index ∈ nodes.map Prod.fst,
    ∃ original ∈ source.map Prod.fst, ∃ step, original >>> step = index

def NodesAgree (tree : Nat → Bytes) (nodes : List (Nat × Bytes)) : Prop :=
  ∀ index value, (index, value) ∈ nodes → value = tree index

theorem cutRoot_supplied (source : List (Nat × Bytes)) (height index : Nat)
    {value : Bytes} (found : nodeAt source index = some value) :
    cutRoot source height index = value := by
  cases height <;> simp [cutRoot, found]

theorem source_parent_absent {source : List (Nat × Bytes)}
    (separated : ProofAntichain source) {index : Nat}
    (supported : ∃ original ∈ source.map Prod.fst, ∃ step, original >>> step = index)
    (positive : 2 ≤ index) : nodeAt source (gindexParent index) = none := by
  cases found : nodeAt source (gindexParent index) with
  | none => rfl
  | some value =>
    obtain ⟨original, member, step, descended⟩ := supported
    have named : gindexParent index ∈ source.map Prod.fst :=
      List.mem_map.mpr ⟨_, nodeAt_member found, rfl⟩
    have ancestral : original >>> (step + 1) = gindexParent index := by
      rw [shiftRight_succ, descended]
      rfl
    have same := separated original member _ named _ ancestral
    have bounded := Nat.shiftRight_le original step
    unfold gindexParent at same
    omega

theorem cutNode_parent {source : List (Nat × Bytes)} {height index : Nat}
    (positive : 2 ≤ index) (bounded : levelOf index ≤ height) (even : index % 2 = 0)
    (absent : nodeAt source (gindexParent index) = none) :
    combine (cutNode source height index) (cutNode source height (index + 1)) =
      cutNode source height (gindexParent index) := by
  have parentDepth := levelOf_parent positive
  have siblingDepth : levelOf (index + 1) = levelOf index := by
    have pair := gindexSibling_even even
    have sibling : gindexSibling index = index + 1 := by omega
    rw [← sibling]
    exact levelOf_sibling positive
  have budget : height - levelOf (gindexParent index) = height - levelOf index + 1 := by
    change levelOf index = levelOf (gindexParent index) + 1 at parentDepth
    omega
  have left : 2 * gindexParent index = index := by unfold gindexParent; omega
  simp only [cutNode, budget, cutRoot, absent, left, siblingDepth]

theorem ProofSupported.fold {source nodes result : List (Nat × Bytes)} {depth : Nat}
    (supported : ProofSupported source nodes) (folded : foldLevel depth nodes = .ok result) :
    ProofSupported source result := by
  intro index member
  obtain ⟨child, childMember, unchanged | joined⟩ := (foldLevel_indices folded index).mp member
  · exact unchanged.2 ▸ supported child childMember
  · obtain ⟨original, originalMember, step, descended⟩ := supported child childMember
    refine ⟨original, originalMember, step + 1, ?_⟩
    rw [shiftRight_succ, descended]
    exact joined.2.2.symm

theorem nodeAt_agrees {tree : Nat → Bytes} {nodes : List (Nat × Bytes)}
    (agree : NodesAgree tree nodes) {index : Nat} {value : Bytes}
    (found : nodeAt nodes index = some value) : value = tree index :=
  agree index value (nodeAt_member found)

private theorem foldLevelNodes_local_agrees {tree : Nat → Bytes} {depth : Nat}
    {nodes pending : List (Nat × Bytes)}
    (parents : ∀ index value, (index, value) ∈ pending → levelOf index = depth →
      index % 2 = 0 → combine (tree index) (tree (index + 1)) = tree (gindexParent index))
    (allAgree : NodesAgree tree nodes) (pendingAgree : NodesAgree tree pending)
    {outParents outKept : List (Nat × Bytes)}
    (folded : foldLevelNodes depth nodes pending = .ok (outParents, outKept)) :
    NodesAgree tree (outParents ++ outKept) := by
  induction pending generalizing outParents outKept with
  | nil =>
    simp [foldLevelNodes] at folded
    rcases folded with ⟨rfl, rfl⟩
    simp [NodesAgree]
  | cons pair rest ih =>
    rcases pair with ⟨index, value⟩
    have head : value = tree index := pendingAgree index value (by simp)
    have tail : NodesAgree tree rest := fun i v member => pendingAgree i v (by simp [member])
    have remaining : ∀ i v, (i, v) ∈ rest → levelOf i = depth → i % 2 = 0 →
        combine (tree i) (tree (i + 1)) = tree (gindexParent i) :=
      fun i v member => parents i v (List.mem_cons_of_mem _ member)
    simp only [foldLevelNodes] at folded
    split at folded
    · cases rec : foldLevelNodes depth nodes rest with
      | error fault => simp [rec, Bind.bind, Except.bind] at folded
      | ok result =>
        rcases result with ⟨ps, ks⟩
        simp [rec, Bind.bind, Except.bind, Pure.pure, Except.pure] at folded
        rcases folded with ⟨rfl, rfl⟩
        have agrees := ih remaining tail rec
        intro i v member
        simp only [List.mem_append, List.mem_cons] at member
        rcases member with member | same | member
        · exact agrees i v (by simp [member])
        · cases same; exact head
        · exact agrees i v (by simp [member])
    · rename_i atDepth
      have atDepth : levelOf index = depth := by simpa using atDepth
      split at folded
      · rename_i even
        have even : index % 2 = 0 := by simpa using even
        cases sibling : nodeAt nodes (index + 1) with
        | none => simp [sibling, throw] at folded
        | some siblingValue =>
          have siblingAgrees := nodeAt_agrees allAgree sibling
          cases rec : foldLevelNodes depth nodes rest with
          | error fault => simp [sibling, rec, Bind.bind, Except.bind] at folded
          | ok result =>
            rcases result with ⟨ps, ks⟩
            simp [sibling, rec, Bind.bind, Except.bind, Pure.pure, Except.pure] at folded
            rcases folded with ⟨rfl, rfl⟩
            have agrees := ih remaining tail rec
            intro i v member
            simp only [List.mem_append, List.mem_cons] at member
            rcases member with (same | member) | member
            · cases same
              rw [head, siblingAgrees]
              exact parents index value List.mem_cons_self atDepth even
            · exact agrees i v (by simp [member])
            · exact agrees i v (by simp [member])
      · split at folded
        · simp [throw] at folded
        · exact ih remaining tail folded

theorem foldLevel_cut {source nodes result : List (Nat × Bytes)} {height depth : Nat}
    (separated : ProofAntichain source) (supported : ProofSupported source nodes)
    (positive : 0 < depth) (bounded : depth ≤ height)
    (agree : NodesAgree (cutNode source height) nodes)
    (folded : foldLevel depth nodes = .ok result) :
    NodesAgree (cutNode source height) result := by
  unfold foldLevel at folded
  cases rec : foldLevelNodes depth nodes nodes with
  | error fault => simp [rec, Bind.bind, Except.bind] at folded
  | ok pair =>
    rcases pair with ⟨parents, kept⟩
    simp [rec, Bind.bind, Except.bind, Pure.pure, Except.pure] at folded
    subst result
    apply foldLevelNodes_local_agrees (tree := cutNode source height) _ agree agree rec
    intro index value member atDepth even
    have low := two_le_of_level_positive atDepth positive
    apply cutNode_parent low (by omega) even
    exact source_parent_absent separated (supported index (List.mem_map.mpr ⟨_, member, rfl⟩)) low

theorem foldToRoot_cut {source : List (Nat × Bytes)} {height : Nat}
    (separated : ProofAntichain source) :
    ∀ depth, depth ≤ height → ∀ nodes, ProofSupported source nodes →
      NodesAgree (cutNode source height) nodes → ∀ root,
      foldToRoot depth nodes = .ok root → root = cutRoot source height 1 := by
  intro depth
  induction depth with
  | zero =>
    intro _ nodes _ agree root built
    simp only [foldToRoot] at built
    cases found : nodeAt nodes 1 with
    | none => simp [found] at built
    | some value =>
      simp [found] at built
      subst root
      simpa [cutNode, show levelOf 1 = 0 from rfl] using nodeAt_agrees agree found
  | succ depth ih =>
    intro bounded nodes supported agree root built
    simp only [foldToRoot] at built
    cases folded : foldLevel (depth + 1) nodes with
    | error fault => simp [folded, Bind.bind, Except.bind] at built
    | ok result =>
      simp only [folded, Bind.bind, Except.bind] at built
      exact ih (by omega) result (supported.fold folded)
        (foldLevel_cut separated supported (by omega) bounded agree folded) root built

theorem nodeAt_of_unique {nodes : List (Nat × Bytes)}
    (unique : (nodes.map Prod.fst).Nodup) {index : Nat} {value : Bytes}
    (member : (index, value) ∈ nodes) : nodeAt nodes index = some value := by
  induction nodes with
  | nil => simp at member
  | cons pair rest ih =>
    rcases pair with ⟨key, node⟩
    simp only [List.map_cons, List.nodup_cons] at unique
    rcases List.mem_cons.mp member with equal | later
    · cases equal; simp [nodeAt]
    · have unequal : key ≠ index := by
        intro equal
        exact unique.1 (equal ▸ List.mem_map.mpr ⟨(index, value), later, rfl⟩)
      simpa [nodeAt, unequal] using ih unique.2 later

theorem foldToRoot_eq_cutRoot {nodes : List (Nat × Bytes)} {height depth : Nat}
    (separated : ProofAntichain nodes) (unique : (nodes.map Prod.fst).Nodup)
    (bounded : depth ≤ height) {root : Bytes} (built : foldToRoot depth nodes = .ok root) :
    root = cutRoot nodes height 1 := by
  apply foldToRoot_cut separated depth bounded nodes _ _ root built
  · exact fun index member => ⟨index, member, 0, by simp⟩
  · intro index value member
    dsimp only [cutNode]
    exact (cutRoot_supplied nodes _ _ (nodeAt_of_unique unique member)).symm

theorem foldl_max_le (values : List Nat) (initial bound : Nat) (small : initial ≤ bound)
    (allSmall : ∀ value ∈ values, value ≤ bound) : values.foldl max initial ≤ bound := by
  induction values generalizing initial with
  | nil => exact small
  | cons head rest ih =>
    apply ih (max initial head) (max_le small (allSmall head (by simp)))
    exact fun value member => allSmall value (by simp [member])

theorem calculateMultiMerkleRoot_cut {leaves proof : List Bytes} {indices helpers : List Nat}
    (built : getHelperIndices indices = .ok helpers)
    (leafCount : leaves.length = indices.length) (proofCount : proof.length = helpers.length)
    (height : Nat) (bounded : ∀ index ∈ indices ++ helpers, levelOf index ≤ height) :
    calculateMultiMerkleRoot leaves proof indices =
      .ok (cutRoot (indices.zip leaves ++ helpers.zip proof) height 1) := by
  let nodes := indices.zip leaves ++ helpers.zip proof
  have positions : nodes.map Prod.fst = indices ++ helpers := by
    simp only [nodes, List.map_append, List.map_fst_zip (by omega : indices.length ≤ leaves.length),
      List.map_fst_zip (by omega : helpers.length ≤ proof.length)]
  obtain ⟨root, reconstructed⟩ := calculateMultiMerkleRoot_complete built leafCount proofCount
  have folded : foldToRoot ((nodes.map fun pair => levelOf pair.1).foldl max 0) nodes = .ok root := by
    simpa [calculateMultiMerkleRoot, leafCount, proofCount, built, nodes,
      Bind.bind, Except.bind, Pure.pure, Except.pure] using reconstructed
  have depthBound : (nodes.map fun pair => levelOf pair.1).foldl max 0 ≤ height := by
    apply foldl_max_le _ _ _ (Nat.zero_le _)
    intro value member
    obtain ⟨pair, pairMember, same⟩ := List.mem_map.mp member
    rw [← same]
    apply bounded pair.1
    rw [← positions]
    exact List.mem_map.mpr ⟨pair, pairMember, rfl⟩
  have rootEq := foldToRoot_eq_cutRoot (nodes := nodes)
    (by intro i hi j hj step shifted; rw [positions] at hi hj;
        exact getHelperIndices_antichain built i hi j hj step shifted)
    (by rw [positions]; exact getHelperIndices_all_nodup built) depthBound folded
  simpa only [rootEq] using reconstructed

end Ssz
