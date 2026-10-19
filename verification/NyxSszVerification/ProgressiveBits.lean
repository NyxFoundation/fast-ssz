import NyxSszVerification.Bitlist
import NyxSszVerification.ProgressiveBits.View

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxRecDepth 4096
set_option maxHeartbeats 200000

namespace NyxSszVerification

def progressiveBitDecodingAgrees :
    core.result.Result NyxSszRust.bitfield.BitListView NyxSszRust.bitfield.BitfieldError →
      Except Ssz.Err Ssz.Value → Prop
  | .Ok view, .ok (.bits bits) => canonicalBitListView view ∧ viewBits view = bits
  | .Err actual, .error expected => bitFaultAgrees actual expected
  | _, _ => False

theorem encode_progressive_bit_list_refines (bits : Slice Bool) (limit : Option Usize) :
    NyxSszRust.bitfield.encode_progressive_bit_list bits limit ⦃ actual =>
      bitEncodingAgrees actual (checkedSerialize (.progressiveBitList (limit.map (fun cap => cap.val)))
        (.bits (bitsToSpec bits.val))) ⦄ := by
  have bitCountBound : bits.val.length ≤ Usize.max := by have shape := bits.property; scalar_tac
  unfold NyxSszRust.bitfield.encode_progressive_bit_list
  cases chosen : limit
  all_goals step*
  all_goals simp_all [checkedSerialize, Ssz.Desc.wellFormed, Ssz.serialize, Ssz.boundCheck,
    bitEncodingAgrees, bitFaultAgrees, Bind.bind, Except.bind, Pure.pure, Except.pure]
  all_goals split_ifs <;> simp_all

set_option maxHeartbeats 2000000 in
theorem decode_progressive_bit_list_refines (bytes : Slice U8) (limit : Option Usize) :
    NyxSszRust.bitfield.decode_progressive_bit_list bytes limit ⦃ actual =>
      progressiveBitDecodingAgrees actual (checkedDeserialize
        (.progressiveBitList (limit.map (fun cap => cap.val))) (bytesToSpec bytes.val)) ⦄ := by
  unfold NyxSszRust.bitfield.decode_progressive_bit_list
  step*
  all_goals have lastLookup := bytesToSpec_getElem_bang bytes.val (bytes.val.length - 1)
  all_goals simp_all [checkedDeserialize, Ssz.Desc.wellFormed, Ssz.deserialize, Ssz.unpackDelimited,
    progressiveBitDecodingAgrees, bitFaultAgrees, canonicalBitListView, viewBits, delimitedLength,
    Bind.bind, Except.bind, Pure.pure, Except.pure, MonadExcept.throw, throwThe, MonadExceptOf.throw]
  all_goals have lastInRange : bytes.val.length - 1 < bytes.val.length := by omega
  all_goals simp_all
  all_goals try split_ifs
  all_goals simp_all
  all_goals omega

end NyxSszVerification
