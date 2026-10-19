import FastSszVerification.Sequence.ByteSlices

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace FastSszVerification

def progressiveByteDecodingAgrees
    (actual : core.result.Result (Slice U8) FastSszRust.bytes.ByteError)
    (expected : Except Ssz.Err Ssz.Value) : Prop :=
  match actual, expected with
  | .Ok output, .ok (.seq values) => byteValues output.val = values
  | .Err error, .error fault => byteFaultAgrees error fault
  | _, _ => False

theorem serialize_progressive_bytes (bytes : List U8) (limit : Option Nat) :
    checkedSerialize (.progressiveList (.uint 1) limit) (.seq (byteValues bytes)) = (do
      Ssz.boundCheck limit bytes.length
      if bytes.length ≥ 2 ^ 32 then .error (.offsetOverflow bytes.length)
      else .ok (bytesToSpec bytes)) := by
  simp [checkedSerialize, Ssz.Desc.wellFormed, Ssz.serialize, serialize_byteSequence,
    Bind.bind, Except.bind]

theorem deserialize_progressive_bytes (bytes : List U8) (limit : Option Nat) :
    checkedDeserialize (.progressiveList (.uint 1) limit) (bytesToSpec bytes) =
      if bytes.length ≥ 2 ^ 32 then .error (.offsetOverflow bytes.length)
      else (do
        Ssz.boundCheck limit bytes.length
        pure (.seq (byteValues bytes))) := by
  cases limit <;> by_cases over : bytes.length ≥ 2 ^ 32
  all_goals simp_all [checkedDeserialize, Ssz.Desc.wellFormed, Ssz.deserialize,
    listSlices_bytes, Ssz.boundCheck, Bind.bind, Except.bind, Pure.pure, Except.pure]
  all_goals split_ifs <;> simp_all [deserialize_byteParts]

@[step] theorem encode_progressive_byte_list_refines (bytes : Slice U8) (limit : Option Usize) :
    FastSszRust.bytes.encode_progressive_byte_list bytes limit ⦃ actual =>
      byteEncodingAgrees actual (checkedSerialize (.progressiveList (.uint 1) (limit.map (fun cap => cap.val)))
        (.seq (byteValues bytes.val))) ⦄ := by
  cases chosen : limit
  all_goals simp_all [FastSszRust.bytes.encode_progressive_byte_list,
    FastSszRust.bytes.check_progressive_bound, FastSszRust.bytes.check_sequence_width,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    lift, serialize_progressive_bytes, Ssz.boundCheck,
    byteEncodingAgrees, byteFaultAgrees, Bind.bind, Except.bind, U32.rMax]
  all_goals split_ifs <;> simp_all
  all_goals omega

@[step] theorem decode_progressive_byte_list_refines (bytes : Slice U8) (limit : Option Usize) :
    FastSszRust.bytes.decode_progressive_byte_list bytes limit ⦃ actual =>
      progressiveByteDecodingAgrees actual (checkedDeserialize
        (.progressiveList (.uint 1) (limit.map (fun cap => cap.val))) (bytesToSpec bytes.val)) ⦄ := by
  cases chosen : limit
  all_goals simp_all [FastSszRust.bytes.decode_progressive_byte_list,
    FastSszRust.bytes.check_sequence_width, FastSszRust.bytes.check_progressive_bound,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    lift, deserialize_progressive_bytes, Ssz.boundCheck,
    progressiveByteDecodingAgrees, byteFaultAgrees, Bind.bind, Except.bind, Pure.pure, Except.pure,
    U32.rMax]
  all_goals split_ifs <;> simp_all
  all_goals omega

end FastSszVerification
