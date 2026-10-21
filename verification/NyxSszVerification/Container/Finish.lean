import NyxSszVerification.Container.Bounds

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace NyxSszVerification

theorem finish_ranges_loop_refines
    (widths : Slice WidthMetadata) (fields : List Ssz.Desc)
    (truth : containerMetadata widths.val fields)
    (slots : Slice NyxSszRust.sequence.BodyRange) (spans : Slice Usize)
    (data : Ssz.Bytes) (scope : Usize) (expected : List (Nat × Nat))
    (sized : slots.val.length = widths.val.length)
    (output : alloc.vec.Vec NyxSszRust.sequence.BodyRange) (index body : Usize)
    (within : index.val ≤ widths.val.length) (bodyWithin : body.val ≤ spans.val.length)
    (outputLength : output.val.length = index.val) (position : Nat)
    (raw : (rangeValues slots.val).drop index.val =
      frontRanges (fields.drop index.val) data position)
    (read : Ssz.offsetSpans (frontOffsets (fields.drop index.val) data position) scope.val =
      .ok (offsetValues (spans.val.drop body.val)))
    (model : rangeValues output.val ++ containerBounds (fields.drop index.val) data position
      (offsetValues (spans.val.drop body.val)) = expected) :
    NyxSszRust.container.finish_ranges_loop widths slots spans output index body ⦃ actual =>
      rangeValues actual.val = expected ⦄ := by
  unfold NyxSszRust.container.finish_ranges_loop
  apply loop_total
    (invariant := fun state : alloc.vec.Vec NyxSszRust.sequence.BodyRange × Usize × Usize =>
      state.2.1.val ≤ widths.val.length ∧ state.2.2.val ≤ spans.val.length ∧
      state.1.val.length = state.2.1.val ∧ ∃ nextPosition : Nat,
      (rangeValues slots.val).drop state.2.1.val =
        frontRanges (fields.drop state.2.1.val) data nextPosition ∧
      Ssz.offsetSpans (frontOffsets (fields.drop state.2.1.val) data nextPosition) scope.val =
        .ok (offsetValues (spans.val.drop state.2.2.val)) ∧
      rangeValues state.1.val ++ containerBounds (fields.drop state.2.1.val) data nextPosition
        (offsetValues (spans.val.drop state.2.2.val)) = expected)
    (measure := fun state => widths.val.length - state.2.1.val)
  · rintro ⟨ranges, nextIndex, nextBody⟩
      ⟨inside, bodyInside, lengthEq, nextPosition, rawEq, readEq, modelEq⟩
    dsimp only at inside bodyInside lengthEq rawEq readEq modelEq ⊢
    by_cases active : nextIndex.val < widths.val.length
    · have fieldInside : nextIndex.val < fields.length := by rw [← truth.1]; exact active
      have slotInside : nextIndex.val < slots.val.length := by omega
      have agrees := metadata_at widths.val fields truth nextIndex.val active
      rw [List.drop_eq_getElem_cons fieldInside] at rawEq readEq modelEq
      rw [← rangeValues_drop, List.drop_eq_getElem_cons slotInside] at rawEq
      cases fixed : fields[nextIndex.val].fixedSize
      all_goals simp only [frontRanges, frontOffsets, containerBounds, fixed,
        rangeValues, List.map_cons] at rawEq readEq modelEq
      · obtain ⟨slotEq, tailEq⟩ := List.cons.inj rawEq
        have spanLength := (offset_spans_bounds readEq).1
        have spanInside : nextBody.val < spans.val.length := by
          simp only [offsetValues_length, List.length_drop, List.length_cons] at spanLength
          omega
        rw [List.drop_eq_getElem_cons spanInside, offsetValues, List.map_cons] at readEq modelEq
        obtain ⟨tailRead, safe⟩ := offset_spans_cons readEq
        have scalarSafe : slots.val[nextIndex.val].start.val + spans.val[nextBody.val].val ≤ Usize.max := by
          have := congrArg Prod.fst slotEq
          dsimp only at this
          rw [this]
          scalar_tac
        have declared := codec_width_none _ (by simpa only [fixed] using agrees)
        unfold NyxSszRust.container.finish_ranges_loop.body
        step*
        simp only [r_post2, declared]
        step*
        subst_vars
        simp_all
        refine ⟨⟨nextPosition + 4, tailEq, ?_, ?_⟩, by omega⟩
        · simpa [offsetValues, List.map_drop] using tailRead
        · simpa [rangeValues, offsetValues, List.map_drop] using modelEq
      · rename_i width
        obtain ⟨slotEq, tailEq⟩ := List.cons.inj rawEq
        have bounded : width ≤ Usize.max := by
          have endEq := congrArg Prod.snd slotEq
          dsimp only at endEq
          scalar_tac
        obtain ⟨child, declared, childWidth⟩ := metadata_fixed _ width
          (by simpa only [fixed] using agrees) bounded
        unfold NyxSszRust.container.finish_ranges_loop.body
        step*
        simp only [r_post2, declared]
        step*
        subst_vars
        simp_all
        exact ⟨⟨nextPosition + child.val, tailEq, readEq, modelEq⟩, by omega⟩
    · have ending : nextIndex.val = fields.length := by have := truth.1; omega
      unfold NyxSszRust.container.finish_ranges_loop.body
      step*
      simpa [ending, containerBounds] using modelEq
  · exact ⟨within, bodyWithin, outputLength, position, raw, read, model⟩

theorem finish_ranges_refines
    (widths : Slice WidthMetadata) (fields : List Ssz.Desc)
    (truth : containerMetadata widths.val fields)
    (slots : Slice NyxSszRust.sequence.BodyRange) (spans : Slice Usize)
    (data : Ssz.Bytes) (scope : Usize)
    (raw : rangeValues slots.val = frontRanges fields data 0)
    (read : Ssz.offsetSpans (frontOffsets fields data 0) scope.val = .ok (offsetValues spans.val)) :
    NyxSszRust.container.finish_ranges widths slots spans ⦃ actual =>
      rangeValues actual.val = containerBounds fields data 0 (offsetValues spans.val) ⦄ := by
  have sized := congrArg List.length raw
  simp only [rangeValues_length, frontRanges_length] at sized
  unfold NyxSszRust.container.finish_ranges
  apply finish_ranges_loop_refines widths fields truth slots spans data scope _
    (sized.trans truth.1.symm) _ _ _ (by simp) (by simp) (by simp) 0
  · simpa using raw
  · simpa using read
  · simp [rangeValues]

end NyxSszVerification
