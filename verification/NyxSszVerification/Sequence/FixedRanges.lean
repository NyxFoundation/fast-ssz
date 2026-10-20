import NyxSszVerification.Sequence.Ranges

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxHeartbeats 2000000

namespace NyxSszVerification

def fixedBounds (width count : Nat) : List (Nat × Nat) :=
  (List.range count).map fun index => (index * width, (index + 1) * width)

@[simp] theorem fixedBounds_length (width count : Nat) : (fixedBounds width count).length = count := by
  simp [fixedBounds]

theorem fixedBounds_at (width count index : Nat) (inside : index < count) :
    (fixedBounds width count)[index]'(by simpa using inside) =
      (index * width, (index + 1) * width) := by simp [fixedBounds]

@[step] theorem fixed_ranges_loop_refines (width count : Usize)
    (output : alloc.vec.Vec NyxSszRust.sequence.BodyRange) (index : Usize)
    (budget : count.val * width.val ≤ Usize.max) (within : index.val ≤ count.val)
    (data : rangeValues output.val = (fixedBounds width.val count.val).take index.val) :
    NyxSszRust.sequence.fixed_ranges_loop width count output index ⦃ result =>
      rangeValues result.val = fixedBounds width.val count.val ⦄ := by
  let expected := fixedBounds width.val count.val
  have fullLength : expected.length = count.val := by simp [expected]
  unfold NyxSszRust.sequence.fixed_ranges_loop
  apply loop_total
    (invariant := fun state : alloc.vec.Vec NyxSszRust.sequence.BodyRange × Usize =>
      state.2.val ≤ count.val ∧ rangeValues state.1.val = expected.take state.2.val)
    (measure := fun state => count.val - state.2.val)
  · rintro ⟨nextOutput, nextIndex⟩ ⟨inBounds, values⟩
    have outputLength : nextOutput.val.length = nextIndex.val := by
      have same := congrArg List.length values
      simpa [fullLength, Nat.min_eq_left inBounds] using same
    by_cases active : nextIndex.val < count.val
    · have endBound : nextIndex.val * width.val + width.val ≤ Usize.max := by
        have bound := Nat.mul_le_mul_right width.val (Nat.succ_le_iff.mpr active)
        simp only [Nat.succ_mul] at bound
        omega
      unfold NyxSszRust.sequence.fixed_ranges_loop.body
      step*
      have inside : nextIndex.val < expected.length := by omega
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [ranges1_post, rangeValues_append, rangeValues_singleton, values,
        index1_post, List.take_succ_eq_append_getElem inside,
        fixedBounds_at width.val count.val nextIndex.val active]
      simp only [start_post, end_post, Nat.add_mul, Nat.one_mul]
    · unfold NyxSszRust.sequence.fixed_ranges_loop.body
      step*
      have atEnd : nextIndex.val = count.val := by scalar_tac
      have finished : expected.take nextIndex.val = expected := List.take_of_length_le (by omega)
      rw [finished] at values
      exact values
  · exact ⟨within, data⟩

@[step] theorem fixed_ranges_refines (width count : Usize)
    (budget : count.val * width.val ≤ Usize.max) :
    NyxSszRust.sequence.fixed_ranges width count ⦃ result =>
      rangeValues result.val = fixedBounds width.val count.val ⦄ := by
  unfold NyxSszRust.sequence.fixed_ranges
  step*
  simp [rangeValues]

end NyxSszVerification
