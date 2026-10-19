import NyxSszVerification.Codec.Law
import NyxSszVerification.Codec.Buffer
import NyxSszVerification.Unsigned
import NyxSszVerification.Boolean

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxHeartbeats 2000000

namespace NyxSszVerification

def scalarFaultAgrees : NyxSszRust.scalar.ScalarError → Ssz.Err → Prop
  | .InvalidLength, .scope _ _ => True
  | .InvalidBoolean, .notABit _ => True
  | _, _ => False

def scalarDecodingAgrees {T : Type} (observe : T → Ssz.Value)
    (actual : core.result.Result T NyxSszRust.scalar.ScalarError)
    (expected : Except Ssz.Err Ssz.Value) : Prop :=
  match actual, expected with
  | .Ok value, .ok expected => observe value = expected
  | .Err error, .error fault => scalarFaultAgrees error fault
  | _, _ => False

theorem uint_scalar_agrees {T : Type} (observe : T → Nat)
    (actual : core.result.Result T NyxSszRust.scalar.ScalarError)
    (expected : Except Ssz.Err Ssz.Value) (agrees : uintResultAgrees observe actual expected) :
    scalarDecodingAgrees (fun value => .uint (observe value)) actual expected := by
  cases actual with
  | Ok value =>
    cases expected with
    | ok value => cases value <;> simp_all [uintResultAgrees, scalarDecodingAgrees]
    | error fault => simp_all [uintResultAgrees]
  | Err error =>
    cases error <;> cases expected with
    | ok value => simp_all [uintResultAgrees]
    | error fault => cases fault <;>
        simp_all [uintResultAgrees, scalarDecodingAgrees, scalarFaultAgrees]

@[simp] theorem codec_except_throw {T : Type} (fault : Ssz.Err) :
    (throw fault : Except Ssz.Err T) = .error fault := rfl

theorem boolean_scalar_agrees (data : Ssz.Bytes) :
    scalarDecodingAgrees Ssz.Value.bool (booleanResult (Ssz.deserialize .bool data))
      (Ssz.deserialize .bool data) := by
  by_cases width : data.size = 1
  · have bound : 0 < data.size := by omega
    by_cases zero : data[0] = 0
    · simp [Ssz.deserialize, width, zero, booleanResult, scalarDecodingAgrees,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
    · by_cases one : data[0] = 1
      · simp [Ssz.deserialize, width, one, booleanResult, scalarDecodingAgrees,
          Bind.bind, Except.bind, Pure.pure, Except.pure]
      · simp [Ssz.deserialize, width, booleanResult, scalarDecodingAgrees,
          scalarFaultAgrees, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · simp [Ssz.deserialize, width, booleanResult, scalarDecodingAgrees,
      scalarFaultAgrees, Bind.bind, Except.bind]

theorem encode_adapter {count : Usize} {shape : Ssz.Desc} {value : Ssz.Value}
    {encoded : RustM (Array U8 count)}
    (valid : shape.wellFormed = .ok ())
    (encoding : encoded ⦃ result => Ssz.serialize shape value = .ok (bytesToSpec result.val) ⦄) :
    (do let array ← encoded
        let output ← NyxSszRust.codec.fixed_bytes array
        RustM.ok (core.result.Result.Ok output)) ⦃ actual =>
      codecEncodingAgrees actual (checkedSerialize shape value) ⦄ := by
  apply spec_bind encoding
  intro array correct
  apply spec_bind (fixed_bytes_refines array)
  intro output same
  simp [codecEncodingAgrees, checkedSerialize, valid, correct, same, Bind.bind, Except.bind]

theorem decode_adapter {T : Type} {observe : T → Ssz.Value} {expected : Except Ssz.Err Ssz.Value}
    {decoded : RustM (core.result.Result T NyxSszRust.scalar.ScalarError)}
    (decoding : decoded ⦃ actual => scalarDecodingAgrees observe actual expected ⦄) :
    (do let result ← decoded
        match result with
        | .Ok value => RustM.ok (core.result.Result.Ok value)
        | .Err error =>
          let mapped ← NyxSszRust.codec.scalar_error error
          RustM.ok (core.result.Result.Err
            ({ kind := mapped, state := () } : NyxSszRust.error.DecodeFailure Unit))) ⦃ actual =>
      codecDecodingAgrees observe actual expected ⦄ := by
  apply spec_bind decoding
  intro actual agrees
  cases actual with
  | Ok value => cases expected <;> simp_all [codecDecodingAgrees, scalarDecodingAgrees]
  | Err error =>
    cases error <;> cases expected with
    | ok value => simp_all [scalarDecodingAgrees]
    | error fault =>
      cases fault <;>
        simp_all [NyxSszRust.codec.scalar_error, codecDecodingAgrees, scalarDecodingAgrees,
          codecFaultAgrees, scalarFaultAgrees, Bind.bind]

theorem root_adapter {shape : Ssz.Desc} {value : Ssz.Value}
    {hashed : RustM (Array U8 32#usize)} (valid : shape.wellFormed = .ok ())
    (hashing : hashed ⦃ result => Ssz.hashTreeRoot shape value = .ok (bytesToSpec result.val) ⦄) :
    (do let root ← hashed; RustM.ok (core.result.Result.Ok root)) ⦃ actual =>
      codecRootAgrees actual (checkedHashTreeRoot shape value) ⦄ := by
  apply spec_bind hashing
  intro root correct
  simp [codecRootAgrees, checkedHashTreeRoot, valid, correct, Bind.bind, Except.bind]

end NyxSszVerification
