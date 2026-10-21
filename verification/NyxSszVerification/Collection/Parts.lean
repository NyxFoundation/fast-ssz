import NyxSszRust.CollectionWire
import NyxSszVerification.Codec.Law
import NyxSszVerification.Collections
import NyxSszVerification.Loop

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace NyxSszVerification

def collectionPartsAgrees
    (actual : core.result.Result (alloc.vec.Vec (alloc.vec.Vec U8)) NyxSszRust.error.CodecError)
    (expected : Except Ssz.Err (List Ssz.Bytes)) : Prop :=
  match actual, expected with
  | .Ok parts, .ok data => parts.val.map (fun part => bytesToSpec part.val) = data
  | .Err kind, .error fault => codecFaultAgrees kind fault
  | _, _ => False

@[local step] theorem collection_encode_child {T State : Type}
    (child : NyxSszRust.codec.Ssz T State) (shape : Ssz.Desc) (observe : T → Ssz.Value)
    (law : CodecLaw child shape observe) (valid : shape.wellFormed = .ok ()) (value : T) :
    child.encode value ⦃ actual => codecEncodingAgrees actual (Ssz.serialize shape (observe value)) ⦄ := by
  simpa [checkedSerialize, valid, Bind.bind, Except.bind] using law.encode value

@[step] theorem collection_encode_parts_loop_refines {T State : Type}
    (child : NyxSszRust.codec.Ssz T State) (shape : Ssz.Desc) (observe : T → Ssz.Value)
    (law : CodecLaw child shape observe) (valid : shape.wellFormed = .ok ())
    (values : Slice T) (parts : alloc.vec.Vec (alloc.vec.Vec U8)) (index : Usize)
    (within : index.val ≤ values.val.length) (length : parts.val.length = index.val) :
    NyxSszRust.collection_wire.encode_parts_loop child values parts index ⦃ actual =>
      collectionPartsAgrees actual
        ((Ssz.serializeEach shape ((values.val.drop index.val).map observe)).map
          (parts.val.map (fun part => bytesToSpec part.val) ++ ·)) ⦄ := by
  let expected := (Ssz.serializeEach shape ((values.val.drop index.val).map observe)).map
    (parts.val.map (fun part => bytesToSpec part.val) ++ ·)
  unfold NyxSszRust.collection_wire.encode_parts_loop
  apply loop_total
    (invariant := fun state : alloc.vec.Vec (alloc.vec.Vec U8) × Usize =>
      state.2.val ≤ values.val.length ∧ state.1.val.length = state.2.val ∧
      (Ssz.serializeEach shape ((values.val.drop state.2.val).map observe)).map
        (state.1.val.map (fun part => bytesToSpec part.val) ++ ·) = expected)
    (measure := fun state => values.val.length - state.2.val)
  · rintro ⟨nextParts, nextIndex⟩ ⟨inBounds, partLength, model⟩
    by_cases active : nextIndex.val < values.val.length
    · unfold NyxSszRust.collection_wire.encode_parts_loop.body
      step*
      · have result : r = .Ok val := by cases r <;> simp_all
        have head : Ssz.serialize shape (observe (values.val[nextIndex.val])) =
            .ok (bytesToSpec val.val) := by
          rw [result, t_post2] at r_post
          cases output : Ssz.serialize shape (observe (values.val[nextIndex.val])) <;>
            simp_all [codecEncodingAgrees]
        refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
        · simp only [parts1_post, List.length_append, List.length_singleton, partLength, index1_post]
        · rw [List.drop_eq_getElem_cons active, List.map_cons, Ssz.serializeEach, head] at model
          cases tailResult : Ssz.serializeEach shape
              ((values.val.map observe).drop (nextIndex.val + 1)) <;>
            simpa [parts1_post, index1_post, Except.map, Bind.bind, Except.bind,
              Pure.pure, Except.pure, List.map_append, List.append_assoc, tailResult] using model
      · have result : r = .Err r1 := by cases r <;> simp_all
        obtain ⟨fault, head, agrees⟩ : ∃ fault,
            Ssz.serialize shape (observe (values.val[nextIndex.val])) = .error fault ∧
            codecFaultAgrees r1 fault := by
          rw [result, t_post2] at r_post
          cases output : Ssz.serialize shape (observe (values.val[nextIndex.val])) <;>
            simp_all [codecEncodingAgrees]
        rw [List.drop_eq_getElem_cons active, List.map_cons, Ssz.serializeEach, head] at model
        simp only [Bind.bind, Except.bind, Except.map] at model
        change collectionPartsAgrees _ expected
        rw [← model, r1_post3, ← r1_post2]
        exact agrees
    · unfold NyxSszRust.collection_wire.encode_parts_loop.body
      step*
      have atEnd : nextIndex.val = values.val.length := by scalar_tac
      change collectionPartsAgrees _ expected
      rw [← model]
      simp [atEnd, Ssz.serializeEach, collectionPartsAgrees, Except.map]
  · exact ⟨within, length, rfl⟩

@[step] theorem collection_encode_parts_refines {T State : Type}
    (child : NyxSszRust.codec.Ssz T State) (shape : Ssz.Desc) (observe : T → Ssz.Value)
    (law : CodecLaw child shape observe) (valid : shape.wellFormed = .ok ()) (values : Slice T) :
    NyxSszRust.collection_wire.encode_parts child values ⦃ actual =>
      collectionPartsAgrees actual (Ssz.serializeEach shape (values.val.map observe)) ⦄ := by
  apply spec_mono (collection_encode_parts_loop_refines child shape observe law valid values
    (alloc.vec.Vec.new _) 0#usize (by simp) (by simp))
  intro actual correct
  simpa only [UScalar.ofNatCore_val_eq, List.drop_zero, alloc.vec.Vec.new,
    List.map_nil, List.nil_append, show (fun x : List Ssz.Bytes => x) = id from rfl,
    Except.map_id, id_eq] using correct

end NyxSszVerification
