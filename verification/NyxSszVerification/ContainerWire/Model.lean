import NyxSszRust.ContainerWire
import NyxSszVerification.Collection.Assemble

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace NyxSszVerification

def containerSlots (slots : List (Bool × alloc.vec.Vec U8)) : List (Bool × Ssz.Bytes) :=
  slots.map fun (fixed, part) => (fixed, bytesToSpec part.val)

def containerHeadSize (slots : List (Bool × alloc.vec.Vec U8)) : Nat :=
  Ssz.headWidth (containerSlots slots)

def containerBodySize (slots : List (Bool × alloc.vec.Vec U8)) : Nat :=
  Ssz.bodyWidth (containerSlots slots)

@[simp] theorem containerSlots_nil : containerSlots [] = [] := rfl
@[simp] theorem containerSlots_cons (fixed : Bool) (part : alloc.vec.Vec U8)
    (rest : List (Bool × alloc.vec.Vec U8)) :
    containerSlots ((fixed, part) :: rest) = (fixed, bytesToSpec part.val) :: containerSlots rest := rfl

@[simp] theorem containerHeadSize_nil : containerHeadSize [] = 0 := rfl
@[simp] theorem containerBodySize_nil : containerBodySize [] = 0 := rfl

@[simp] theorem containerHeadSize_cons (fixed : Bool) (part : alloc.vec.Vec U8)
    (rest : List (Bool × alloc.vec.Vec U8)) :
    containerHeadSize ((fixed, part) :: rest) =
      (if fixed then part.val.length else 4) + containerHeadSize rest := by
  cases fixed <;> simp [containerHeadSize, Ssz.headWidth, Ssz.bytesPerOffset]

@[simp] theorem containerBodySize_cons (fixed : Bool) (part : alloc.vec.Vec U8)
    (rest : List (Bool × alloc.vec.Vec U8)) :
    containerBodySize ((fixed, part) :: rest) =
      (if fixed then 0 else part.val.length) + containerBodySize rest := by
  cases fixed <;> simp [containerBodySize, Ssz.bodyWidth]

@[simp] theorem container_slots_zip (slots : List (Bool × alloc.vec.Vec U8)) :
    (slots.map Prod.fst).zip (slots.map fun part => bytesToSpec part.2.val) = containerSlots slots := by
  induction slots with
  | nil => rfl
  | cons slot rest ih => cases slot; simp [containerSlots, ih]

def containerSizeAgrees
    (actual : core.result.Result (Usize × Usize) NyxSszRust.error.CodecError)
    (leading body : Nat) : Prop :=
  match actual with
  | .Ok (head, tail) => head.val = leading ∧ tail.val = body ∧ leading + body < 4294967296
  | .Err .SizeOverflow => 4294967296 ≤ leading + body
  | _ => False

end NyxSszVerification
