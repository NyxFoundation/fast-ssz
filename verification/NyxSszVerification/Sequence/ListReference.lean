import NyxSszVerification.Sequence.Vector

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace NyxSszVerification

theorem read_offsets_first (data : Ssz.Bytes) (count : Nat) (positive : 0 < count) :
    (Ssz.readOffsets data count)[0]! = Ssz.readUint data 0 4 := by
  simp [Ssz.readOffsets, positive, Ssz.bytesPerOffset]

theorem variable_list_vector_slices (element : Ssz.Desc) (isVariable : element.fixedSize = none)
    (data : Ssz.Bytes) (limit : Option Nat)
    (envelope : data.size < 4294967296)
    (header : 4 ≤ Ssz.readUint data 0 4)
    (aligned : Ssz.readUint data 0 4 % 4 = 0)
    (bounded : Ssz.readUint data 0 4 ≤ data.size)
    (capacity : ∀ cap, limit = some cap → Ssz.readUint data 0 4 / 4 ≤ cap) :
    Ssz.listSlices element limit data =
      Ssz.vectorSlices element (Ssz.readUint data 0 4 / 4) data := by
  let first := Ssz.readUint data 0 4
  have positive : 0 < first / 4 := by omega
  have product : first / 4 * 4 = first := by omega
  have budget : first / 4 * 4 ≤ data.size := by omega
  have notHuge : ¬4294967296 ≤ data.size := by omega
  have nonempty : data.size ≠ 0 := by omega
  have notSmall : ¬data.size < 4 := by omega
  have notBelow : ¬first < 4 := by omega
  have notPast : ¬first > data.size := by omega
  rw [variable_vector_slices_form element isVariable data _ _ envelope budget (by omega) rfl]
  simp only [read_offsets_first _ _ positive, product, ne_eq]
  cases limit with
  | none =>
    cases read : Ssz.offsetSpans (Ssz.readOffsets data (first / 4)) data.size <;>
      simp [Ssz.listSlices, isVariable, Ssz.bytesPerOffset, notHuge, nonempty,
        notSmall, notBelow, notPast, aligned, read, first, Except.map,
        Bind.bind, Except.bind, pure, Except.pure]
  | some cap =>
    have within := capacity cap rfl
    have notOver : ¬first / 4 > cap := by omega
    cases read : Ssz.offsetSpans (Ssz.readOffsets data (first / 4)) data.size <;>
      simp [Ssz.listSlices, isVariable, Ssz.bytesPerOffset, notHuge, nonempty,
        notSmall, notBelow, notPast, aligned, read, first, notOver, Except.map,
        Bind.bind, Except.bind, pure, Except.pure]

end NyxSszVerification
