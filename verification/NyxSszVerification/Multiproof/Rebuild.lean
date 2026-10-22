import NyxSszVerification.Multiproof.Lookup

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace NyxSszVerification

theorem nodeAt_append (left right : List (Nat × Ssz.Bytes)) (index : Nat) :
    Ssz.nodeAt (left ++ right) index =
      match Ssz.nodeAt left index with
      | some node => some node
      | none => Ssz.nodeAt right index := by
  unfold Ssz.nodeAt
  rw [List.find?_append]
  cases left.find? (fun pair => pair.1 == index) <;> simp

@[step] theorem multiproof_child_success (index : U128) (side : Bool)
    (fits : Ssz.gindexChild index.val side ≤ U128.max) :
    NyxSszRust.gindex.child index side ⦃ actual =>
      ∃ child : U128, actual = .Ok child ∧ child.val = Ssz.gindexChild index.val side ⦄ := by
  apply spec_mono (gindex_child_refines index side)
  intro actual agreement
  cases actual with
  | Ok child => exact ⟨child, rfl, agreement⟩
  | Err fault =>
    cases fault <;> simp_all [gindexResultAgrees]
    omega

@[step] theorem multiproof_rebuild_refines (leaves proof : Slice RustNode)
    (indices helpers : Slice U128) (index : U128) (remaining : U32)
    (leafCount : leaves.val.length = indices.val.length)
    (proofCount : proof.val.length = helpers.val.length)
    (small : remaining.val ≤ 127) (width : index.val < 2 ^ (128 - remaining.val)) :
    NyxSszRust.multiproof.rebuild leaves proof indices helpers index remaining ⦃ actual =>
      rootResultAgrees actual (.ok (Ssz.cutRoot
        (frontierNodes indices.val leaves.val ++ frontierNodes helpers.val proof.val)
        remaining.val index.val)) ⦄ := by
  generalize numberEq : remaining.val = number
  induction number using Nat.strong_induction_on generalizing remaining index with
  | h number ih =>
    rw [NyxSszRust.multiproof.rebuild.eq_def]
    apply spec_bind (multiproof_node_at_refines indices leaves index leafCount)
    intro supplied suppliedEq
    cases supplied with
    | some node =>
      have found : Ssz.nodeAt (frontierNodes indices.val leaves.val ++
          frontierNodes helpers.val proof.val) index.val = some (bytesToSpec node.val) := by
        rw [nodeAt_append, ← suppliedEq]
        rfl
      simp only [spec_ok, rootResultAgrees, Ssz.cutRoot_supplied _ _ _ found]
    | none =>
      apply spec_bind (multiproof_node_at_refines helpers proof index proofCount)
      intro auxiliary auxiliaryEq
      cases auxiliary with
      | some node =>
        have found : Ssz.nodeAt (frontierNodes indices.val leaves.val ++
            frontierNodes helpers.val proof.val) index.val = some (bytesToSpec node.val) := by
          rw [nodeAt_append, ← suppliedEq, ← auxiliaryEq]
          rfl
        simp only [spec_ok, rootResultAgrees, Ssz.cutRoot_supplied _ _ _ found]
      | none =>
        have absent : Ssz.nodeAt (frontierNodes indices.val leaves.val ++
            frontierNodes helpers.val proof.val) index.val = none := by
          rw [nodeAt_append, ← suppliedEq, ← auxiliaryEq]
          rfl
        by_cases zero : remaining = 0#u32
        · have value : remaining.val = 0 := by scalar_tac
          have numberZero : number = 0 := by omega
          simp [zero, numberZero, rootResultAgrees, Ssz.cutRoot, absent, bytesToSpec,
            byteToSpec, Ssz.zeroChunk, Ssz.bytesPerChunk]
          rfl
        · have positive : 0 < remaining.val := by scalar_tac
          have childBudget : 128 - (remaining.val - 1) = (128 - remaining.val) + 1 := by omega
          have childWidth (side : Bool) :
              Ssz.gindexChild index.val side < 2 ^ (128 - (remaining.val - 1)) := by
            rw [childBudget, Nat.pow_succ]
            cases side <;> simp only [Ssz.gindexChild, Bool.false_eq_true, ↓reduceIte] <;> omega
          have childFits (side : Bool) : Ssz.gindexChild index.val side ≤ U128.max := by
            have bigger : 2 ^ (128 - (remaining.val - 1)) ≤ 2 ^ 128 :=
              Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
            have below := childWidth side
            scalar_tac
          simp only [if_neg zero]
          apply spec_bind (multiproof_child_success index false (childFits false))
          intro leftResult leftInfo
          obtain ⟨leftIndex, leftEq, leftValue⟩ := leftInfo
          simp only [leftEq, core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]
          apply spec_bind (multiproof_child_success index true (childFits true))
          intro rightResult rightInfo
          obtain ⟨rightIndex, rightEq, rightValue⟩ := rightInfo
          simp only [rightEq, bind_tc_ok]
          step as ⟨next, nextValue, _⟩
          have nextSmall : next.val ≤ 127 := by omega
          have smaller : next.val < number := by omega
          have leftWidth : leftIndex.val < 2 ^ (128 - next.val) := by
            rw [nextValue, leftValue]
            exact childWidth false
          have rightWidth : rightIndex.val < 2 ^ (128 - next.val) := by
            rw [nextValue, rightValue]
            exact childWidth true
          apply spec_bind (ih next.val smaller leftIndex next nextSmall leftWidth rfl)
          intro leftRoot leftAgreement
          cases leftRoot with
          | Err fault => simp [rootResultAgrees] at leftAgreement
          | Ok leftNode =>
            simp only [bind_tc_ok]
            apply spec_bind (ih next.val smaller rightIndex next nextSmall rightWidth rfl)
            intro rightRoot rightAgreement
            cases rightRoot with
            | Err fault => simp [rootResultAgrees] at rightAgreement
            | Ok rightNode =>
              simp only [bind_tc_ok]
              step as ⟨root, rootAgreement⟩
              simp only [rootResultAgrees] at leftAgreement rightAgreement
              have succEq : number = next.val + 1 := by omega
              simp only [rootResultAgrees, succEq, Ssz.cutRoot, absent]
              simpa only [leftAgreement, rightAgreement, leftValue, rightValue,
                Ssz.gindexChild, Bool.false_eq_true, ↓reduceIte, Nat.mul_comm, Nat.add_zero] using rootAgreement

end NyxSszVerification
