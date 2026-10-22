import NyxSszVerification.Multiproof.Paths

open Aeneas Aeneas.Std

namespace NyxSszVerification

/-- The reference keeps the first occurrence, never an invented index. -/
theorem multiproof_dedup_info (indices : List Nat) :
    List.Sublist indices.eraseDups indices ∧ indices.eraseDups.Nodup := by
  cases indices with
  | nil => simp
  | cons head rest =>
    rw [List.eraseDups_cons]
    have filtered := multiproof_dedup_info (rest.filter fun item => !item == head)
    constructor
    · exact List.Sublist.cons_cons _ (filtered.1.trans List.filter_sublist)
    · rw [List.nodup_cons]
      exact ⟨by simp, filtered.2⟩
termination_by indices.length
decreasing_by
  have bound := List.length_filter_le (fun item => !item == head) rest
  simp_all

theorem multiproof_dedup_eq (indices : List Nat) (unique : indices.Nodup) :
    indices.eraseDups = indices := by
  induction indices with
  | nil => rfl
  | cons head rest ih =>
    rw [List.nodup_cons] at unique
    rw [List.eraseDups_cons]
    have filterEq : rest.filter (fun item => !item == head) = rest := by
      apply List.filter_eq_self.mpr
      intro item member
      have different : item ≠ head := by intro same; exact unique.1 (same ▸ member)
      simp [different]
    rw [filterEq, ih unique.2]

theorem multiproof_dedup_length (indices : List Nat) :
    indices.eraseDups.length = indices.length ↔ indices.Nodup := by
  constructor
  · intro same
    obtain ⟨sublist, unique⟩ := multiproof_dedup_info indices
    rw [sublist.eq_of_length same] at unique
    exact unique
  · intro unique
    rw [multiproof_dedup_eq indices unique]

theorem multiproof_nodup_values (indices : List U128) :
    (indices.map UScalar.val).Nodup ↔ indices.Nodup := by
  constructor
  · exact List.Nodup.of_map UScalar.val
  · intro unique
    exact unique.map (fun _ _ same => UScalar.eq_of_val_eq same)

end NyxSszVerification
