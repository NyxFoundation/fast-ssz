import NyxSszRust.CollectionWire
import NyxSszVerification.Codec.Law
import NyxSszVerification.Collections
import NyxSszVerification.Loop

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace NyxSszVerification

/-- None is successful reference collection with at least one inaccessible body. -/
def collectionStoredAgrees (parts : alloc.vec.Vec (alloc.vec.Vec U8))
    (oversized : Bool) (data : List Ssz.Bytes) : Prop :=
  if oversized then ∃ part ∈ data, Usize.max < part.size
  else parts.val.map (fun part => bytesToSpec part.val) = data

def collectionPartsAgrees
    (actual : core.result.Result (Option (alloc.vec.Vec (alloc.vec.Vec U8))) NyxSszRust.error.CodecError)
    (expected : Except Ssz.Err (List Ssz.Bytes)) : Prop :=
  match actual, expected with
  | .Ok (some parts), .ok data => parts.val.map (fun part => bytesToSpec part.val) = data
  | .Ok none, .ok data => ∃ part ∈ data, Usize.max < part.size
  | .Err kind, .error fault => codecFaultAgrees kind fault
  | _, _ => False

@[local step] theorem collection_encode_child {T State : Type}
    (child : NyxSszRust.codec.Ssz T State) (shape : Ssz.Desc) (observe : T → Ssz.Value)
    (law : CodecLaw child shape observe) (valid : shape.wellFormed = .ok ()) (value : T) :
    child.encode value ⦃ actual => codecEncodingAgrees actual (Ssz.serialize shape (observe value)) ⦄ := by
  simpa [checkedSerialize, valid, Bind.bind, Except.bind] using law.encode value

theorem collection_parts_extend {T : Type} (shape : Ssz.Desc) (observe : T → Ssz.Value)
    (values : Slice T) (index : Usize) (prior : List Ssz.Bytes) (bytes : Ssz.Bytes)
    (active : index.val < values.val.length)
    (head : Ssz.serialize shape (observe values.val[index.val]) = .ok bytes) :
    (Ssz.serializeEach shape ((values.val.drop index.val).map observe)).map (prior ++ ·) =
      (Ssz.serializeEach shape ((values.val.drop (index.val + 1)).map observe)).map
        ((prior ++ [bytes]) ++ ·) := by
  rw [List.drop_eq_getElem_cons active, List.map_cons, Ssz.serializeEach, head]
  cases tail : Ssz.serializeEach shape ((values.val.drop (index.val + 1)).map observe) <;>
    simp [Except.map, Bind.bind, Except.bind, Pure.pure, Except.pure, List.append_assoc]

theorem collection_stored_push (parts : alloc.vec.Vec (alloc.vec.Vec U8))
    (oversized : Bool) (prior : List Ssz.Bytes) (part : alloc.vec.Vec U8)
    (output : alloc.vec.Vec (alloc.vec.Vec U8)) (same : output.val = parts.val ++ [part])
    (stored : collectionStoredAgrees parts oversized prior) :
    collectionStoredAgrees output oversized (prior ++ [bytesToSpec part.val]) := by
  cases oversized <;> simp_all [collectionStoredAgrees, List.map_append]

@[step] theorem collection_encode_parts_loop_refines {T State : Type}
    (child : NyxSszRust.codec.Ssz T State) (shape : Ssz.Desc) (observe : T → Ssz.Value)
    (law : CodecLaw child shape observe) (valid : shape.wellFormed = .ok ())
    (values : Slice T) (parts : alloc.vec.Vec (alloc.vec.Vec U8)) (oversized : Bool) (index : Usize)
    (prior : List Ssz.Bytes) (within : index.val ≤ values.val.length)
    (length : parts.val.length ≤ index.val) (stored : collectionStoredAgrees parts oversized prior) :
    NyxSszRust.collection_wire.encode_parts_loop child values parts oversized index ⦃ actual =>
      collectionPartsAgrees actual
        ((Ssz.serializeEach shape ((values.val.drop index.val).map observe)).map (prior ++ ·)) ⦄ := by
  let expected := (Ssz.serializeEach shape ((values.val.drop index.val).map observe)).map (prior ++ ·)
  unfold NyxSszRust.collection_wire.encode_parts_loop
  apply loop_total
    (invariant := fun state : alloc.vec.Vec (alloc.vec.Vec U8) × Bool × Usize =>
      state.2.2.val ≤ values.val.length ∧ state.1.val.length ≤ state.2.2.val ∧
      ∃ prior, collectionStoredAgrees state.1 state.2.1 prior ∧
        (Ssz.serializeEach shape ((values.val.drop state.2.2.val).map observe)).map (prior ++ ·) = expected)
    (measure := fun state => values.val.length - state.2.2.val)
  · rintro ⟨nextParts, nextOversized, nextIndex⟩ ⟨inBounds, partLength, prior, stored, model⟩
    dsimp only at inBounds partLength stored model
    unfold NyxSszRust.collection_wire.encode_parts_loop.body
    by_cases active : nextIndex.val < values.val.length
    · have activeScalar : nextIndex < Slice.len values := by scalar_tac
      simp only [activeScalar, if_true]
      step
      apply spec_bind (collection_encode_child child shape observe law valid _)
      intro result correct
      cases result with
      | Ok part =>
        have head : Ssz.serialize shape (observe values.val[nextIndex.val]) = .ok (bytesToSpec part.val) := by
          cases encoded : Ssz.serialize shape (observe values.val[nextIndex.val]) <;>
            simp_all [codecEncodingAgrees]
        step*
        refine ⟨by scalar_tac, by simp [parts1_post, index1_post]; omega,
          ⟨prior ++ [bytesToSpec part.val], ?_, ?_⟩, by scalar_tac⟩
        · exact collection_stored_push nextParts nextOversized prior part _ parts1_post stored
        · simpa [index1_post] using (collection_parts_extend shape observe values nextIndex prior _ active head).symm.trans model
      | Err error =>
        by_cases native : error = .NativeOutputOverflow
        · subst error
          obtain ⟨body, head, large⟩ : ∃ body,
              Ssz.serialize shape (observe values.val[nextIndex.val]) = .ok body ∧ Usize.max < body.size := by
            cases encoded : Ssz.serialize shape (observe values.val[nextIndex.val]) <;>
              simp_all [codecEncodingAgrees, codecFaultAgrees]
          step*
          refine ⟨by scalar_tac, by scalar_tac, ⟨prior ++ [body], ?_, ?_⟩, by scalar_tac⟩
          · exact ⟨body, by simp, large⟩
          · simpa [index1_post] using (collection_parts_extend shape observe values nextIndex prior _ active head).symm.trans model
        · obtain ⟨fault, head, agrees⟩ : ∃ fault,
              Ssz.serialize shape (observe values.val[nextIndex.val]) = .error fault ∧ codecFaultAgrees error fault := by
            cases encoded : Ssz.serialize shape (observe values.val[nextIndex.val]) <;>
              cases error <;> simp_all [codecEncodingAgrees]
          rw [List.drop_eq_getElem_cons active, List.map_cons, Ssz.serializeEach, head] at model
          simp only [Bind.bind, Except.bind, Except.map] at model
          cases error <;> try contradiction
          all_goals
            simp only [spec_ok]
            change collectionPartsAgrees _ expected
            rw [← model]
            exact agrees
    · have atEnd : nextIndex.val = values.val.length := by omega
      have inactive : ¬nextIndex < Slice.len values := by scalar_tac
      simp only [inactive, if_false]
      rw [atEnd] at model
      simp only [List.drop_length, List.map_nil, Ssz.serializeEach, Except.map,
        List.append_nil] at model
      cases nextOversized <;> simp only [Bool.false_eq_true, if_false, if_true] <;>
        change collectionPartsAgrees _ expected
      all_goals rw [← model]; exact stored
  · exact ⟨within, length, prior, stored, rfl⟩

@[step] theorem collection_encode_parts_refines {T State : Type}
    (child : NyxSszRust.codec.Ssz T State) (shape : Ssz.Desc) (observe : T → Ssz.Value)
    (law : CodecLaw child shape observe) (valid : shape.wellFormed = .ok ()) (values : Slice T) :
    NyxSszRust.collection_wire.encode_parts child values ⦃ actual =>
      collectionPartsAgrees actual (Ssz.serializeEach shape (values.val.map observe)) ⦄ := by
  apply spec_mono (collection_encode_parts_loop_refines child shape observe law valid values
    (alloc.vec.Vec.new _) false 0#usize [] (by simp) (by simp) (by simp [collectionStoredAgrees]))
  intro actual correct
  simpa only [UScalar.ofNatCore_val_eq, List.drop_zero, List.nil_append,
    show (fun x : List Ssz.Bytes => x) = id from rfl, Except.map_id, id_eq] using correct

end NyxSszVerification
