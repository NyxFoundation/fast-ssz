import NyxSszVerification.Multiproof.Helpers

open Aeneas Aeneas.Std

namespace NyxSszVerification

theorem chooseHelpers_le (paths : List Nat) (upper : Nat) (pending : List Nat)
    (best bound : Nat) :
    chooseHelpers paths upper pending best ≤ bound ↔
      best ≤ bound ∧ ∀ node ∈ pending,
        Ssz.gindexSibling node ≤ upper → Ssz.gindexSibling node ∉ paths →
          Ssz.gindexSibling node ≤ bound := by
  induction pending generalizing best with
  | nil => simp [chooseHelpers]
  | cons node rest ih =>
    simp only [chooseHelpers, List.foldl_cons]
    rw [show List.foldl (chooseSibling paths upper) (chooseSibling paths upper best node) rest =
      chooseHelpers paths upper rest (chooseSibling paths upper best node) from rfl, ih]
    simp only [chooseSibling]
    split <;> simp_all

theorem select_le (indices : List U128) (upper bound : Nat) :
    chooseHelpers (pathsOf indices) upper (pathsOf indices) 0 ≤ bound ↔
      ∀ helper ∈ canonicalHelpers indices, helper ≤ upper → helper ≤ bound := by
  rw [chooseHelpers_le]
  simp only [Nat.zero_le, true_and, canonicalHelpers_mem]
  constructor
  · intro bounded helper member below
    obtain ⟨siblings, outside⟩ := member
    obtain ⟨node, path, rfl⟩ := List.mem_map.mp siblings
    exact bounded node path below outside
  · intro bounded node path below outside
    exact bounded _ ⟨List.mem_map.mpr ⟨node, path, rfl⟩, outside⟩ below

theorem select_head (indices : List U128) (upper : Nat) :
    chooseHelpers (pathsOf indices) upper (pathsOf indices) 0 =
      ((canonicalHelpers indices).filter fun helper => helper ≤ upper).headD 0 := by
  let pending := (canonicalHelpers indices).filter fun helper => helper ≤ upper
  have ordered : pending.Pairwise (fun left right => right < left) :=
    (canonicalHelpers_sorted indices).filter _
  change chooseHelpers (pathsOf indices) upper (pathsOf indices) 0 = pending.headD 0
  cases equation : pending with
  | nil =>
    apply Nat.eq_zero_of_le_zero
    apply (select_le indices upper 0).mpr
    intro helper member below
    have inside : helper ∈ pending := List.mem_filter.mpr ⟨member, by simpa using below⟩
    simp [equation] at inside
  | cons head rest =>
    have member : head ∈ canonicalHelpers indices ∧ head ≤ upper := by
      have inside : head ∈ pending := by simp [equation]
      simpa only [pending, List.mem_filter, decide_eq_true_eq] using inside
    have lower : head ≤ chooseHelpers (pathsOf indices) upper (pathsOf indices) 0 := by
      exact ((select_le indices upper _).mp (Nat.le_refl _)) head member.1 member.2
    have higher : chooseHelpers (pathsOf indices) upper (pathsOf indices) 0 ≤ head := by
      apply (select_le indices upper head).mpr
      intro helper supplied below
      have inside : helper ∈ pending := List.mem_filter.mpr ⟨supplied, by simpa using below⟩
      rw [equation, List.mem_cons] at inside
      rcases inside with rfl | later
      · rfl
      · have := (List.pairwise_cons.mp (equation ▸ ordered)).1 helper later
        omega
    exact Nat.le_antisymm higher lower

theorem descending_filter_tail (values : List Nat) (upper head : Nat) (tail : List Nat)
    (ordered : values.Pairwise (fun left right => right < left))
    (positive : 0 < head)
    (pending : values.filter (fun helper => helper ≤ upper) = head :: tail) :
    values.filter (fun helper => helper ≤ head - 1) = tail := by
  have headBound : head ≤ upper := by
    have member : head ∈ values.filter (fun helper => helper ≤ upper) := by rw [pending]; simp
    exact of_decide_eq_true (List.mem_filter.mp member).2
  have merged : values.filter (fun helper => helper ≤ head - 1) =
      (values.filter (fun helper => helper ≤ upper)).filter (fun helper => helper ≤ head - 1) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro helper _
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega
  rw [merged, pending]
  have tailSmall : ∀ helper ∈ tail, helper ≤ head - 1 := by
    have filtered := ordered.filter (fun helper => helper ≤ upper)
    rw [pending, List.pairwise_cons] at filtered
    intro helper member
    have := filtered.1 helper member
    omega
  simp only [List.filter_cons, show ¬head ≤ head - 1 by omega, decide_false, Bool.false_eq_true,
    if_false]
  exact List.filter_eq_self.mpr (fun helper member => by simpa using tailSmall helper member)

end NyxSszVerification
