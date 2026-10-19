import NyxSszVerification.Sequence.Reference

open Aeneas Aeneas.Std

namespace NyxSszVerification

/-- Successful numeric validation makes every complete body interval safe. -/
theorem offset_spans_bounds {offsets spans : List Nat} {scope : Nat}
    (read : Ssz.offsetSpans offsets scope = .ok spans) :
    spans.length = offsets.length ∧
      ∀ index, index < offsets.length → offsets[index]! + spans[index]! ≤ scope := by
  induction offsets, scope using Ssz.offsetSpans.induct generalizing spans with
  | case1 => cases read; simp
  | case2 start scope bad => simp [Ssz.offsetSpans, bad] at read
  | case3 start scope good =>
    simp [Ssz.offsetSpans, good] at read
    subst spans
    constructor
    · rfl
    · intro index inside
      have zero : index = 0 := by simpa using inside
      subst index
      simp only [List.getElem!_cons_zero]
      omega
  | case4 start next rest scope bad => simp [Ssz.offsetSpans, bad] at read
  | case5 start next rest scope good ih =>
    cases suffix : Ssz.offsetSpans (next :: rest) scope with
    | error fault => simp [Ssz.offsetSpans, good, suffix, Bind.bind, Except.bind] at read
    | ok more =>
      simp [Ssz.offsetSpans, good, suffix, Bind.bind, Except.bind, pure, Except.pure] at read
      subst spans
      obtain ⟨sized, safe⟩ := ih suffix
      have nextBound := safe 0 (by simp)
      simp only [List.getElem!_cons_zero] at nextBound
      constructor
      · simp [sized]
      · intro index inside
        cases index with
        | zero => simp only [List.getElem!_cons_zero]; omega
        | succ index => simpa using safe index (by simpa using inside)

end NyxSszVerification
