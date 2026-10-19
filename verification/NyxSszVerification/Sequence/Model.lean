import NyxSszRust.Sequence
import NyxSszVerification.Codec.Law
import NyxSszVerification.Loop

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace NyxSszVerification

def offsetValues (values : List Usize) : List Nat := values.map fun value => value.val

def offsetSuffix (values : List Usize) (scope index : Nat) (held : List Nat) :
    Except Ssz.Err (List Nat) :=
  (Ssz.offsetSpans (offsetValues (values.drop index)) scope).map (held ++ ·)

def offsetSpansAgree
    (actual : core.result.Result (alloc.vec.Vec Usize) NyxSszRust.error.CodecError)
    (expected : Except Ssz.Err (List Nat)) : Prop :=
  match actual, expected with
  | .Ok values, .ok expected => offsetValues values.val = expected
  | .Err error, .error fault => codecFaultAgrees error fault
  | _, _ => False

@[simp] theorem offsetValues_append (left right : List Usize) :
    offsetValues (left ++ right) = offsetValues left ++ offsetValues right := by
  simp [offsetValues]

@[simp] theorem offsetValues_singleton (value : Usize) : offsetValues [value] = [value.val] := rfl

@[simp] theorem offset_suffix_done (values : List Usize) (scope : Nat) (held : List Nat) :
    offsetSuffix values scope values.length held = .ok held := by
  simp [offsetSuffix, offsetValues, Ssz.offsetSpans, Except.map]

theorem offset_suffix_unordered (values : List Usize) (scope index : Nat) (held : List Nat)
    (inside : index + 1 < values.length)
    (unordered : values[index + 1].val < values[index].val) :
    offsetSuffix values scope index held = .error .offsetUnordered := by
  have first : index < values.length := by omega
  unfold offsetSuffix offsetValues
  rw [List.drop_eq_getElem_cons first, List.drop_eq_getElem_cons inside]
  simp only [List.map_cons, Ssz.offsetSpans, unordered, ↓reduceIte, Except.map]

theorem offset_suffix_next (values : List Usize) (scope index : Nat) (held : List Nat)
    (inside : index + 1 < values.length)
    (ordered : values[index].val ≤ values[index + 1].val) :
    offsetSuffix values scope index held =
      offsetSuffix values scope (index + 1)
        (held ++ [values[index + 1].val - values[index].val]) := by
  have first : index < values.length := by omega
  unfold offsetSuffix offsetValues
  rw [List.drop_eq_getElem_cons first, List.drop_eq_getElem_cons inside]
  simp only [List.map_cons, Ssz.offsetSpans, Nat.not_lt.mpr ordered, ↓reduceIte]
  cases result : Ssz.offsetSpans
      (values[index + 1].val :: (values.drop (index + 1 + 1)).map fun value => value.val) scope <;>
    simp [Except.map, List.append_assoc]

theorem offset_suffix_last (values : List Usize) (scope index : Nat) (held : List Nat)
    (last : index + 1 = values.length) :
    offsetSuffix values scope index held =
      if scope < values[index].val then .error .offsetPastScope
      else .ok (held ++ [scope - values[index].val]) := by
  have inside : index < values.length := by omega
  unfold offsetSuffix offsetValues
  rw [List.drop_eq_getElem_cons inside, last, List.drop_length]
  by_cases past : scope < values[index].val <;> simp [Ssz.offsetSpans, past, Except.map]

end NyxSszVerification
