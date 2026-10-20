import NyxSszRust.CollectionTree
import NyxSszVerification.Codec.Law
import NyxSszVerification.Collections
import NyxSszVerification.Loop
import NyxSszVerification.Merkle.Nodes

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxHeartbeats 2000000

namespace NyxSszVerification

def collectionRootEach (shape : Ssz.Desc) (values : List Ssz.Value) : Except Ssz.Err (List Ssz.Bytes) :=
  values.mapM (Ssz.hashTreeRoot shape)

@[simp] theorem collectionRootEach_nil (shape : Ssz.Desc) : collectionRootEach shape [] = .ok [] := rfl

@[simp] theorem collectionRootEach_cons (shape : Ssz.Desc) (value : Ssz.Value) (rest : List Ssz.Value) :
    collectionRootEach shape (value :: rest) = do
      let root ← Ssz.hashTreeRoot shape value
      let roots ← collectionRootEach shape rest
      return root :: roots := by
  simp [collectionRootEach, List.mapM_cons, Functor.map, Except.map]

def collectionRootsAgrees
    (actual : core.result.Result (alloc.vec.Vec RustNode) NyxSszRust.error.CodecError)
    (expected : Except Ssz.Err (List Ssz.Bytes)) : Prop :=
  match actual, expected with
  | .Ok parts, .ok data => proofNodes parts.val = data
  | .Err kind, .error fault => codecFaultAgrees kind fault
  | _, _ => False

@[local step] theorem collection_root_child {T State : Type}
    (child : NyxSszRust.codec.Ssz T State) (shape : Ssz.Desc) (observe : T → Ssz.Value)
    (law : CodecLaw child shape observe) (valid : shape.wellFormed = .ok ()) (value : T) :
    child.hash_tree_root value ⦃ actual => codecRootAgrees actual (Ssz.hashTreeRoot shape (observe value)) ⦄ := by
  simpa [checkedHashTreeRoot, valid, Bind.bind, Except.bind] using law.root value

@[step] theorem collection_root_elements_loop_refines {T State : Type}
    (child : NyxSszRust.codec.Ssz T State) (shape : Ssz.Desc) (observe : T → Ssz.Value)
    (law : CodecLaw child shape observe) (valid : shape.wellFormed = .ok ())
    (values : Slice T) (roots : alloc.vec.Vec RustNode) (index : Usize)
    (within : index.val ≤ values.val.length) (length : roots.val.length = index.val) :
    NyxSszRust.collection_tree.root_elements_loop child values roots index ⦃ actual =>
      collectionRootsAgrees actual
        ((collectionRootEach shape ((values.val.drop index.val).map observe)).map
          (proofNodes roots.val ++ ·)) ⦄ := by
  let expected := (collectionRootEach shape ((values.val.drop index.val).map observe)).map
    (proofNodes roots.val ++ ·)
  unfold NyxSszRust.collection_tree.root_elements_loop
  apply loop_total
    (invariant := fun state : alloc.vec.Vec RustNode × Usize =>
      state.2.val ≤ values.val.length ∧ state.1.val.length = state.2.val ∧
      (collectionRootEach shape ((values.val.drop state.2.val).map observe)).map
        (proofNodes state.1.val ++ ·) = expected)
    (measure := fun state => values.val.length - state.2.val)
  · rintro ⟨nextRoots, nextIndex⟩ ⟨inBounds, rootLength, model⟩
    by_cases active : nextIndex.val < values.val.length
    · unfold NyxSszRust.collection_tree.root_elements_loop.body
      step*
      · have result : r = .Ok val := by cases r <;> simp_all
        have head : Ssz.hashTreeRoot shape (observe (values.val[nextIndex.val])) =
            .ok (bytesToSpec val.val) := by
          rw [result, t_post2] at r_post
          cases output : Ssz.hashTreeRoot shape (observe (values.val[nextIndex.val])) <;>
            simp_all [codecRootAgrees]
        refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
        · simp only [roots1_post, List.length_append, List.length_singleton, rootLength, index1_post]
        · rw [List.drop_eq_getElem_cons active, List.map_cons, collectionRootEach_cons, head] at model
          cases tailResult : collectionRootEach shape ((values.val.map observe).drop (nextIndex.val + 1)) <;>
            simpa [roots1_post, index1_post, Except.map, Bind.bind, Except.bind,
              Pure.pure, Except.pure, proofNodes, List.map_append, List.append_assoc, tailResult] using model
      · have result : r = .Err r1 := by cases r <;> simp_all
        obtain ⟨fault, head, agrees⟩ : ∃ fault,
            Ssz.hashTreeRoot shape (observe (values.val[nextIndex.val])) = .error fault ∧
            codecFaultAgrees r1 fault := by
          rw [result, t_post2] at r_post
          cases output : Ssz.hashTreeRoot shape (observe (values.val[nextIndex.val])) <;>
            simp_all [codecRootAgrees]
        rw [List.drop_eq_getElem_cons active, List.map_cons, collectionRootEach_cons, head] at model
        simp only [Bind.bind, Except.bind, Except.map] at model
        change collectionRootsAgrees _ expected
        rw [← model, r1_post3, ← r1_post2]
        exact agrees
    · unfold NyxSszRust.collection_tree.root_elements_loop.body
      step*
      have atEnd : nextIndex.val = values.val.length := by scalar_tac
      change collectionRootsAgrees _ expected
      rw [← model]
      simp [atEnd, collectionRootsAgrees, Except.map]
  · exact ⟨within, length, rfl⟩

@[step] theorem collection_root_elements_refines {T State : Type}
    (child : NyxSszRust.codec.Ssz T State) (shape : Ssz.Desc) (observe : T → Ssz.Value)
    (law : CodecLaw child shape observe) (valid : shape.wellFormed = .ok ()) (values : Slice T) :
    NyxSszRust.collection_tree.root_elements child values ⦃ actual =>
      collectionRootsAgrees actual (collectionRootEach shape (values.val.map observe)) ⦄ := by
  apply spec_mono (collection_root_elements_loop_refines child shape observe law valid values
    (alloc.vec.Vec.new _) 0#usize (by simp) (by simp))
  intro actual correct
  simpa only [UScalar.ofNatCore_val_eq, List.drop_zero, alloc.vec.Vec.new,
    proofNodes, List.map_nil, List.nil_append, show (fun x : List Ssz.Bytes => x) = id from rfl,
    Except.map_id, id_eq] using correct

end NyxSszVerification
