import NyxSszVerification.Collection.Pack
import NyxSszVerification.Collection.Capacity
import NyxSszVerification.Representation.Integers

open Aeneas Aeneas.Std

set_option maxHeartbeats 2000000

namespace NyxSszVerification

theorem collection_basic_width_bound (shape : Ssz.Desc)
    (valid : shape.wellFormed = .ok ()) (basic : shape.isBasic = true) :
    shape.itemLength ≤ 32 := by
  cases shape <;> simp only [Ssz.Desc.isBasic, Bool.false_eq_true] at basic
  · simp [Ssz.Desc.itemLength]
  · rename_i width
    simp [Ssz.Desc.wellFormed] at valid
    simp only [Ssz.Desc.itemLength]
    omega

theorem collection_basic_serialize_size (shape : Ssz.Desc) (basic : shape.isBasic = true)
    (value : Ssz.Value) (bytes : Ssz.Bytes) (wrote : Ssz.serialize shape value = .ok bytes) :
    bytes.size = shape.itemLength := by
  cases shape <;> simp only [Ssz.Desc.isBasic, Bool.false_eq_true] at basic
  · cases value <;> simp only [Ssz.serialize] at wrote
    all_goals try contradiction
    cases wrote
    simp [Ssz.Desc.itemLength]
  · cases value <;> simp only [Ssz.serialize] at wrote
    all_goals try contradiction
    split at wrote
    · cases wrote
      simp [Ssz.uintBytes_size, Ssz.Desc.itemLength]
    · contradiction

theorem collection_basic_parts_native (shape : Ssz.Desc)
    (valid : shape.wellFormed = .ok ()) (basic : shape.isBasic = true)
    (values : List Ssz.Value) (parts : List Ssz.Bytes)
    (wrote : Ssz.serializeEach shape values = .ok parts) :
    ¬ ∃ part ∈ parts, Usize.max < part.size := by
  have width := collection_basic_width_bound shape valid basic
  have platform := Usize.bounds_eq
  induction values generalizing parts with
  | nil => simp [Ssz.serializeEach] at wrote; subst parts; simp
  | cons value values ih =>
    cases head : Ssz.serialize shape value with
    | error fault => simp [Ssz.serializeEach, head, Bind.bind, Except.bind] at wrote
    | ok bytes =>
      cases tail : Ssz.serializeEach shape values with
      | error fault => simp [Ssz.serializeEach, head, tail, Bind.bind, Except.bind] at wrote
      | ok rest =>
        simp [Ssz.serializeEach, head, tail, Bind.bind, Except.bind, Pure.pure, Except.pure] at wrote
        subst parts
        have size := collection_basic_serialize_size shape basic value bytes head
        have bounded : bytes.size ≤ Usize.max := by scalar_tac
        simpa only [List.mem_cons, exists_eq_or_imp, Nat.not_lt.mpr bounded, false_or] using ih rest tail

theorem collection_basic_parts_size (shape : Ssz.Desc) (basic : shape.isBasic = true)
    (values : List Ssz.Value) (parts : List Ssz.Bytes)
    (wrote : Ssz.serializeEach shape values = .ok parts) :
    (parts.map _root_.Array.size).sum = values.length * shape.itemLength := by
  induction values generalizing parts with
  | nil => simp [Ssz.serializeEach] at wrote; subst parts; simp
  | cons value values ih =>
    cases head : Ssz.serialize shape value with
    | error fault => simp [Ssz.serializeEach, head, Bind.bind, Except.bind] at wrote
    | ok bytes =>
      cases tail : Ssz.serializeEach shape values with
      | error fault => simp [Ssz.serializeEach, head, tail, Bind.bind, Except.bind] at wrote
      | ok rest =>
        simp [Ssz.serializeEach, head, tail, Bind.bind, Except.bind, Pure.pure, Except.pure] at wrote
        subst parts
        simp only [List.map_cons, List.sum_cons, List.length_cons,
          collection_basic_serialize_size shape basic value bytes head, ih rest tail]
        simp only [Nat.add_mul, Nat.one_mul]
        omega

/-- Packing a basic sequence allocates at most one node per stored element. -/
theorem collection_basic_parts_bound (shape : Ssz.Desc)
    (basic : shape.isBasic = true)
    (values : List Ssz.Value) (parts : List (alloc.vec.Vec U8))
    (wrote : Ssz.serializeEach shape values = .ok (parts.map fun part => bytesToSpec part.val)) :
    collectionBodySize parts = values.length * shape.itemLength := by
  have size := collection_basic_parts_size shape basic values _ wrote
  simpa [List.map_map, Function.comp_def, collectionBodySize] using size

theorem collection_fold_parts (parts : List (alloc.vec.Vec U8)) (initial : Ssz.Bytes) :
    (parts.map fun part => bytesToSpec part.val).foldl (· ++ ·) initial =
      initial ++ bytesToSpec (collectionBodyBytes parts) := by
  induction parts generalizing initial with
  | nil => simp [bytesToSpec]
  | cons part rest ih =>
    simp only [List.map_cons, List.foldl_cons, ih, collectionBodyBytes_cons]
    simp [bytesToSpec]

@[simp] theorem collection_pack_elements (parts : List (alloc.vec.Vec U8)) :
    Ssz.packElements (parts.map fun part => bytesToSpec part.val) =
      Ssz.packBytes (bytesToSpec (collectionBodyBytes parts)) := by
  simp [Ssz.packElements, collection_fold_parts]

end NyxSszVerification
