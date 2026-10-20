import NyxSszVerification.Sequence.Vector
import NyxSszVerification.Sequence.List

open Aeneas Aeneas.Std

namespace NyxSszVerification

/-- The successful sequence decoder creates exactly one value for each body. -/
theorem collection_deserialize_each_count (shape : Ssz.Desc) (parts : List Ssz.Bytes)
    (values : List Ssz.Value) (read : Ssz.deserializeEach shape parts = .ok values) :
    values.length = parts.length := by
  induction parts generalizing values with
  | nil => simp [Ssz.deserializeEach] at read; simp [← read]
  | cons part parts ih =>
    cases first : Ssz.deserialize shape part with
    | error fault => simp [Ssz.deserializeEach, first, Bind.bind, Except.bind] at read
    | ok value =>
      cases rest : Ssz.deserializeEach shape parts with
      | error fault => simp [Ssz.deserializeEach, first, rest, Bind.bind, Except.bind] at read
      | ok tail =>
        simp [Ssz.deserializeEach, first, rest, Bind.bind, Except.bind, Pure.pure, Except.pure] at read
        subst values
        simp [ih tail rest]

/-- The pinned vector slicing helper produces exactly the declared number of bodies. -/
theorem collection_vector_slices_count (shape : Ssz.Desc) (count : Nat) (data : Ssz.Bytes)
    (parts : List Ssz.Bytes) (read : Ssz.vectorSlices shape count data = .ok parts) :
    parts.length = count := by
  simp [Ssz.vectorSlices, Bind.bind, Except.bind, Pure.pure, Except.pure,
    MonadExcept.throw, throwThe, MonadExceptOf.throw] at read
  repeat' split at read
  all_goals simp_all
  all_goals try (subst parts; simp_all)
  rename_i widths spans
  have sized := (offset_spans_bounds spans).1
  simp only [read_offsets_length] at sized
  simp_all

/-- The pinned list slicing helper checks the element count before returning bodies. -/
theorem collection_list_slices_count (shape : Ssz.Desc) (limit : Nat) (data : Ssz.Bytes)
    (parts : List Ssz.Bytes) (read : Ssz.listSlices shape (some limit) data = .ok parts) :
    parts.length ≤ limit := by
  simp [Ssz.listSlices, Bind.bind, Except.bind, Pure.pure, Except.pure,
    MonadExcept.throw, throwThe, MonadExceptOf.throw] at read
  repeat' split at read
  all_goals simp_all
  all_goals try (subst parts; simp_all [Ssz.readOffsets])

end NyxSszVerification
