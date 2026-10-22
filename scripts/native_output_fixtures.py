"""Real Lean/kernel fixtures for the exact native-output observation boundary."""

PREFIX = """open Aeneas Aeneas.Std Aeneas.Std.WP
open NyxSszVerification
"""


def native_output_success():
    return PREFIX + """
example : ∃ body : Ssz.Bytes, body.size = Usize.max ∧
    checkedSerialize (.compatibleUnion [1] [.byteVector Usize.max]) (.union 1 (.bytes body)) =
      .ok (#[1] ++ body) ∧
    codecEncodingAgrees (.Err .NativeOutputOverflow) (.ok (#[1] ++ body)) :=
  compatible_union_native_exists

example (data : Ssz.Bytes) (fits : data.size ≤ Usize.max) :
    ¬ codecEncodingAgrees (.Err .NativeOutputOverflow) (.ok data) := by
  simp [codecEncodingAgrees, Nat.not_lt.mpr fits]

example (fault : Ssz.Err) :
    ¬ codecEncodingAgrees (.Err .NativeOutputOverflow) (.error fault) := by simp
"""


def native_output_rejection_cases():
    return {
        "FakeNativeBool": (PREFIX + """
def fakeNativeBool : NyxSszRust.codec.Ssz Bool Unit :=
  { NyxSszRust.Bool.Insts.Nyx_sszCodecSszTuple with
    encode := fun _ => RustM.ok (.Err .NativeOutputOverflow) }

example : CodecLaw fakeNativeBool .bool Ssz.Value.bool := by
  constructor
  · exact bool_codec_refines.declaration
  · intro value
    simp [fakeNativeBool, codecEncodingAgrees, checkedSerialize,
      Ssz.Desc.wellFormed, Ssz.serialize, Bind.bind, Except.bind, spec_ok]
  · exact bool_codec_refines.decode
  · exact bool_codec_refines.root
""", "unsolved goals"),
        "NativeHidesProtocolFault": (PREFIX + """
example : codecEncodingAgrees (.Err .NativeOutputOverflow) (.error (.offsetOverflow 4294967296)) := by
  simp [codecEncodingAgrees, codecFaultAgrees]
""", "unsolved goals"),
        "NativeDecodeFault": (PREFIX + """
example : codecDecodingAgrees Ssz.Value.bool
    (.Err (NyxSszRust.error.DecodeFailure.mk .NativeOutputOverflow ())) (.error (.scope 1 0)) := by
  simp [codecDecodingAgrees, codecFaultAgrees]
""", "unsolved goals"),
        "NativeRootFault": (PREFIX + """
example : codecRootAgrees (.Err .NativeOutputOverflow) (.error (.offsetOverflow 4294967296)) := by
  simp [codecRootAgrees, codecFaultAgrees]
""", "unsolved goals"),
    }
