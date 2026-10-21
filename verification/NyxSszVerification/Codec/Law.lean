import NyxSszRust.Codec
import NyxSszVerification.Bytes
import NyxSszVerification.TypeInfo.Model
import Ssz.Codec.Root

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace NyxSszVerification

/-- Unmapped faults cannot count as conformance. -/
def codecFaultAgrees : NyxSszRust.error.CodecError → Ssz.Err → Prop
  | .InvalidLength, .scope _ _ => True
  | .InvalidBoolean, .notABit _ => True
  | .InvalidIntegerWidth, .uintWidth _ => True
  | .EmptyVector, .vectorEmpty => True
  | .SizeOverflow, .offsetOverflow _ => True
  | .OffsetUnordered, .offsetUnordered => True
  | .OffsetPastScope, .offsetPastScope => True
  | .ScopeTooSmall, .scopeTooSmall _ _ => True
  | .ScopeWidthless, .scopeWidthless => True
  | .ScopeUndivided, .scopeUndivided _ _ => True
  | .FirstOffset, .firstOffset _ _ => True
  | .OffsetBelowTable, .offsetBelowTable => True
  | .OffsetUnaligned, .offsetUnaligned => True
  | .OverLimit, .overLimit _ _ => True
  | .PaddingBits, .paddingBits => True
  | .EmptyEncoding, .emptyEncoding => True
  | .NoDelimiter, .noDelimiter => True
  | .TrailingZeros, .trailingZeros => True
  | _, _ => False

def codecEncodingAgrees
    (actual : core.result.Result (alloc.vec.Vec U8) NyxSszRust.error.CodecError)
    (expected : Except Ssz.Err Ssz.Bytes) : Prop :=
  match actual, expected with
  | .Ok bytes, .ok data => bytesToSpec bytes.val = data
  | .Err error, .error fault => codecFaultAgrees error fault
  | _, _ => False

def codecDecodingAgrees {T State : Type} (observe : T → Ssz.Value)
    (actual : core.result.Result T (NyxSszRust.error.DecodeFailure State))
    (expected : Except Ssz.Err Ssz.Value) : Prop :=
  match actual, expected with
  | .Ok value, .ok expected => observe value = expected
  | .Err failure, .error fault => codecFaultAgrees failure.kind fault
  | _, _ => False

def codecRootAgrees
    (actual : core.result.Result (Array U8 32#usize) NyxSszRust.error.CodecError)
    (expected : Except Ssz.Err Ssz.Bytes) : Prop :=
  match actual, expected with
  | .Ok root, .ok bytes => bytesToSpec root.val = bytes
  | .Err error, .error fault => codecFaultAgrees error fault
  | _, _ => False

/-- Metadata reports overflow instead of conflating it with variable layout. -/
def codecWidthAgrees
    (actual : core.result.Result (Option Usize) NyxSszRust.error.CodecError)
    (expected : Option Nat) : Prop :=
  match actual, expected with
  | .Ok none, none => True
  | .Ok (some width), some expected => width.val = expected
  | .Err .SizeOverflow, some expected => Usize.max < expected
  | _, _ => False

def codecValidityAgrees
    (actual : core.result.Result Unit NyxSszRust.error.CodecError)
    (expected : Except Ssz.Err Unit) : Prop :=
  match actual, expected with
  | .Ok (), .ok () => True
  | .Err error, .error fault => codecFaultAgrees error fault
  | _, _ => False

def checkedHashTreeRoot (shape : Ssz.Desc) (value : Ssz.Value) : Except Ssz.Err Ssz.Bytes := do
  shape.wellFormed
  Ssz.hashTreeRoot shape value

/-- A caller-supplied dictionary is not presumed lawful. Library instances prove this predicate. -/
structure CodecLaw {T State : Type} (codecInst : NyxSszRust.codec.Ssz T State)
    (shape : Ssz.Desc) (observe : T → Ssz.Value) : Prop where
  declaration : codecInst.TYPE ⦃ actual => typeDescriptorToSpec actual = shape ⦄
  encode : ∀ value, codecInst.encode value ⦃ actual =>
    codecEncodingAgrees actual (checkedSerialize shape (observe value)) ⦄
  decode : ∀ bytes, codecInst.decode bytes ⦃ actual =>
    codecDecodingAgrees observe actual (checkedDeserialize shape (bytesToSpec bytes.val)) ⦄
  root : ∀ value, codecInst.hash_tree_root value ⦃ actual =>
    codecRootAgrees actual (checkedHashTreeRoot shape (observe value)) ⦄

theorem codec_encode_refines {T State : Type} (codecInst : NyxSszRust.codec.Ssz T State)
    (shape : Ssz.Desc) (observe : T → Ssz.Value) (law : CodecLaw codecInst shape observe) (value : T) :
    NyxSszRust.codec.encode codecInst value ⦃ actual =>
      codecEncodingAgrees actual (checkedSerialize shape (observe value)) ⦄ := by
  exact law.encode value

theorem codec_decode_refines {T State : Type} (codecInst : NyxSszRust.codec.Ssz T State)
    (shape : Ssz.Desc) (observe : T → Ssz.Value) (law : CodecLaw codecInst shape observe)
    (bytes : Slice U8) :
    NyxSszRust.codec.decode codecInst bytes ⦃ actual =>
      codecDecodingAgrees observe actual (checkedDeserialize shape (bytesToSpec bytes.val)) ⦄ := by
  exact law.decode bytes

theorem codec_hash_tree_root_refines {T State : Type} (codecInst : NyxSszRust.codec.Ssz T State)
    (shape : Ssz.Desc) (observe : T → Ssz.Value) (law : CodecLaw codecInst shape observe) (value : T) :
    NyxSszRust.codec.hash_tree_root codecInst value ⦃ actual =>
      codecRootAgrees actual (checkedHashTreeRoot shape (observe value)) ⦄ := by
  exact law.root value

/-- Dispatch forwards the exact result, including arbitrary owned failure state. -/
theorem codec_decode_preserves_result {T State : Type} (codecInst : NyxSszRust.codec.Ssz T State)
    (bytes : Slice U8) : NyxSszRust.codec.decode codecInst bytes = codecInst.decode bytes := rfl

/-- A terminating unit-state codec cannot retain or discard an element on failure. -/
theorem codec_unit_decode_state_empty {T : Type} (codecInst : NyxSszRust.codec.Ssz T Unit)
    (shape : Ssz.Desc) (observe : T → Ssz.Value) (law : CodecLaw codecInst shape observe)
    (bytes : Slice U8) : NyxSszRust.codec.decode codecInst bytes ⦃ actual =>
      match actual with
      | .Ok _ => True
      | .Err failure => failure.state = () ⦄ := by
  apply spec_mono (law.decode bytes)
  intro actual _
  cases actual with
  | Ok value => trivial
  | Err failure => exact Subsingleton.elim _ _

end NyxSszVerification
