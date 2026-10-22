import NyxSszVerification.Collection.Parts

open Aeneas Aeneas.Std

namespace NyxSszVerification

/-- Both inline and offset-bearing sequences include every child's full size. -/
theorem collection_uniform_budget (parts : List Ssz.Bytes) (fixed : Bool) :
    Ssz.headWidth ((parts.map fun _ => fixed).zip parts) +
      Ssz.bodyWidth ((parts.map fun _ => fixed).zip parts) =
    (if fixed then 0 else parts.length * 4) + (parts.map _root_.Array.size).sum := by
  induction parts with
  | nil => cases fixed <;> rfl
  | cons part rest ih =>
    cases fixed <;> simp_all [Ssz.headWidth, Ssz.bodyWidth, Ssz.bytesPerOffset] <;> omega

/-- Native-inaccessible success becomes a genuine sequence offset-budget refusal,
only after serializeEach has checked every later child's protocol outcome. -/
theorem collection_assemble_native (parts : List Ssz.Bytes) (fixed : Bool)
    (large : ∃ part ∈ parts, Usize.max < part.size) :
    ∃ fault, Ssz.assemble (parts.map fun _ => fixed) parts = .error fault ∧
      codecFaultAgrees .SizeOverflow fault := by
  obtain ⟨part, member, oversized⟩ := large
  have sumBound : part.size ≤ (parts.map _root_.Array.size).sum :=
    List.le_sum_of_mem (List.mem_map.mpr ⟨part, member, rfl⟩)
  have platform := Usize.bounds_eq
  have totalBound : 4294967296 ≤ Ssz.headWidth ((parts.map fun _ => fixed).zip parts) +
      Ssz.bodyWidth ((parts.map fun _ => fixed).zip parts) := by
    rw [collection_uniform_budget]
    scalar_tac
  refine ⟨.offsetOverflow (Ssz.headWidth ((parts.map fun _ => fixed).zip parts) +
    Ssz.bodyWidth ((parts.map fun _ => fixed).zip parts)), ?_, trivial⟩
  simp only [Ssz.assemble, show 2 ^ (8 * Ssz.bytesPerOffset) = 4294967296 from rfl,
    ge_iff_le, totalBound, if_true, Bind.bind, Except.bind,
    MonadExcept.throw, throwThe, MonadExceptOf.throw]

end NyxSszVerification
