import NyxSszVerification.Codec.Elements.Loop
import NyxSszVerification.Codec.Elements.Wire

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace NyxSszVerification

/-- Wire conformance and exact retention of completed values and nested error state. -/
theorem decode_elements_refines {T State : Type} (codecInst : NyxSszRust.codec.Ssz T State)
    (shape : Ssz.Desc) (observe : T → Ssz.Value) (law : CodecLaw codecInst shape observe)
    (view : NyxSszRust.sequence.SequenceView) (valid : sequenceViewValid view) :
    NyxSszRust.codec.decode_elements codecInst view ⦃ actual =>
      decodeRangesModel codecInst view.input view.ranges.val [] =
        RustM.ok (sequenceResultToLists actual) ∧
      sequenceListsAgrees observe (sequenceResultToLists actual)
        (checkedDeserializeEach shape (rangeBodies view.input view.ranges.val)) ⦄ := by
  apply spec_mono (decode_elements_retains codecInst shape observe law view valid)
  intro actual retained
  refine ⟨retained, ?_⟩
  have protocol := decode_ranges_model_wire codecInst shape observe law
    view.input view.ranges.val valid []
  rw [retained] at protocol
  change sequenceListsAgrees observe (sequenceResultToLists actual)
    (Except.map id (checkedDeserializeEach shape (rangeBodies view.input view.ranges.val))) at protocol
  rw [Except.map_id] at protocol
  exact protocol

/-- On a valid element declaration the wire observation is the pinned reference helper. -/
theorem decode_elements_reference {T State : Type} (codecInst : NyxSszRust.codec.Ssz T State)
    (shape : Ssz.Desc) (observe : T → Ssz.Value) (law : CodecLaw codecInst shape observe)
    (validShape : shape.wellFormed = .ok ())
    (view : NyxSszRust.sequence.SequenceView) (valid : sequenceViewValid view) :
    NyxSszRust.codec.decode_elements codecInst view ⦃ actual =>
      sequenceListsAgrees observe (sequenceResultToLists actual)
        (Ssz.deserializeEach shape (rangeBodies view.input view.ranges.val)) ⦄ := by
  apply spec_mono (decode_elements_refines codecInst shape observe law view valid)
  intro actual correct
  simpa only [checked_each_reference shape validShape] using correct.2

end NyxSszVerification
