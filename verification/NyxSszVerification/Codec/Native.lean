import NyxSszVerification.Codec.Law
import NyxSszVerification.Representation.Bytes

open Aeneas Aeneas.Std

namespace NyxSszVerification

/-- Representable reference successes cannot be refused, and bytes remain exact. -/
theorem codec_encoding_representable
    (actual : core.result.Result (alloc.vec.Vec U8) NyxSszRust.error.CodecError)
    (data : Ssz.Bytes) (fits : data.size ≤ Usize.max) :
    codecEncodingAgrees actual (.ok data) ↔
      ∃ bytes, actual = .Ok bytes ∧ bytesToSpec bytes.val = data := by
  cases actual with
  | Ok bytes => simp [codecEncodingAgrees]
  | Err kind => cases kind <;> simp [codecEncodingAgrees, Nat.not_lt.mpr fits]

/-- Above native capacity, exactly the distinct native refusal conforms. -/
theorem codec_encoding_oversized
    (actual : core.result.Result (alloc.vec.Vec U8) NyxSszRust.error.CodecError)
    (data : Ssz.Bytes) (large : Usize.max < data.size) :
    codecEncodingAgrees actual (.ok data) ↔ actual = .Err .NativeOutputOverflow := by
  cases actual with
  | Ok bytes =>
    have impossible : bytesToSpec bytes.val ≠ data := by
      intro same
      have size := congrArg _root_.Array.size same
      simp only [bytesToSpec_size] at size
      have bound := bytes.property
      omega
    simp [codecEncodingAgrees, impossible]
  | Err kind => cases kind <;> simp [codecEncodingAgrees, large]

/-- Protocol errors retain exactly their old fault relation, never a native marker. -/
theorem codec_encoding_reference_error
    (actual : core.result.Result (alloc.vec.Vec U8) NyxSszRust.error.CodecError) (fault : Ssz.Err) :
    codecEncodingAgrees actual (.error fault) ↔
      ∃ kind, actual = .Err kind ∧ codecFaultAgrees kind fault := by
  cases actual <;> simp [codecEncodingAgrees]

@[simp] theorem codec_native_fault_excluded (fault : Ssz.Err) :
    ¬ codecFaultAgrees .NativeOutputOverflow fault := by cases fault <;> simp [codecFaultAgrees]

@[simp] theorem codec_native_encoding_error_excluded (fault : Ssz.Err) :
    ¬ codecEncodingAgrees (.Err .NativeOutputOverflow) (.error fault) := by
  exact codec_native_fault_excluded fault

@[simp] theorem codec_native_decode_excluded {T State : Type} (observe : T → Ssz.Value)
    (state : State) (expected : Except Ssz.Err Ssz.Value) :
    ¬ codecDecodingAgrees observe (.Err ⟨.NativeOutputOverflow, state⟩) expected := by
  cases expected <;> simp [codecDecodingAgrees]

@[simp] theorem codec_native_root_excluded (expected : Except Ssz.Err Ssz.Bytes) :
    ¬ codecRootAgrees (.Err .NativeOutputOverflow) expected := by
  cases expected <;> simp [codecRootAgrees]

@[simp] theorem codec_native_width_excluded (expected : Option Nat) :
    ¬ codecWidthAgrees (.Err .NativeOutputOverflow) expected := by
  cases expected <;> simp [codecWidthAgrees]

@[simp] theorem codec_native_validity_excluded (expected : Except Ssz.Err Unit) :
    ¬ codecValidityAgrees (.Err .NativeOutputOverflow) expected := by
  cases expected <;> simp [codecValidityAgrees]

/-- Prefixing the selector has a natural size, with no union offset envelope. -/
theorem compatible_union_prefix_size (selector : Nat) (body : Ssz.Bytes) :
    (#[UInt8.ofNat selector] ++ body).size = body.size + 1 := by simp; omega

/-- The pinned serializer really succeeds on a MAX-byte opaque union body. -/
theorem compatible_union_native_boundary (body : Ssz.Bytes) (size : body.size = Usize.max) :
    checkedSerialize (.compatibleUnion [1] [.byteVector Usize.max]) (.union 1 (.bytes body)) =
      .ok (#[1] ++ body) ∧ Usize.max < (#[1] ++ body).size := by
  have platform := Usize.bounds_eq
  have positive : Usize.max ≠ 0 := by scalar_tac
  constructor
  · simp [checkedSerialize, Ssz.Desc.wellFormed, Ssz.serialize, Ssz.lookupOption, size,
      positive, Ssz.firstDuplicate, Ssz.minSelector, Ssz.maxSelector,
      Ssz.Desc.allWellFormed, Ssz.Desc.optionsCompatible, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · simp [size]

/-- The union prefix crosses native capacity exactly at the MAX-byte body. -/
theorem compatible_union_native_iff (selector : Nat) (body : Ssz.Bytes) :
    codecEncodingAgrees (.Err .NativeOutputOverflow) (.ok (#[UInt8.ofNat selector] ++ body)) ↔
      Usize.max ≤ body.size := by
  simp only [codecEncodingAgrees, compatible_union_prefix_size]
  omega

/-- A symbolic witness, not evaluation/allocation of a giant buffer. -/
theorem compatible_union_native_exists :
    ∃ body : Ssz.Bytes, body.size = Usize.max ∧
      checkedSerialize (.compatibleUnion [1] [.byteVector Usize.max]) (.union 1 (.bytes body)) =
        .ok (#[1] ++ body) ∧
      codecEncodingAgrees (.Err .NativeOutputOverflow) (.ok (#[1] ++ body)) := by
  let body : Ssz.Bytes := _root_.Array.replicate Usize.max 0
  have size : body.size = Usize.max := by simp [body]
  have boundary := compatible_union_native_boundary body size
  exact ⟨body, size, boundary.1, boundary.2⟩

end NyxSszVerification
