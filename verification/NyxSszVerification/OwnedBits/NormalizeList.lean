import NyxSszVerification.OwnedBits.Copy
import NyxSszVerification.OwnedBits.ListPacking
import NyxSszVerification.OwnedBits.FromBits

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace NyxSszVerification

@[step] theorem owned_normalize_list_storage (bytes : Slice U8) (limit : Option Usize) :
    NyxSszRust.bit_storage.normalize_list bytes limit ⦃ actual =>
      match actual with
      | .Ok output => output.val = ownedNormalizedList bytes.val ∧
          ∀ cap, limit = some cap → delimitedLength bytes.val ≤ cap.val
      | .Err error => error = .OverLimit ∧ ∃ cap, limit = some cap ∧ cap.val < delimitedLength bytes.val ⦄ := by
  unfold NyxSszRust.bit_storage.normalize_list
  cases chosen : limit
  all_goals step*
  all_goals simp_all [ownedNormalizedList]
  all_goals
    have nonempty : 0 < bytes.val.length := by cases h : bytes.val <;> simp_all
    have inside : bytes.val.length - 1 < bytes.val.length := by omega
    simp_all

@[step] theorem owned_normalize_list_refines (bytes : Slice U8) (limit : Option Usize) :
    NyxSszRust.bit_storage.normalize_list bytes limit ⦃ actual =>
      codecEncodingAgrees actual
        (checkedSerialize (.progressiveBitList (limit.map fun cap => cap.val)) (.bits (ownedListBits bytes.val))) ⦄ := by
  apply spec_mono (owned_normalize_list_storage bytes limit)
  intro actual agrees
  cases actual with
  | Ok output =>
    rcases agrees with ⟨data, within⟩
    have packed := ownedNormalizedList_pack bytes.val
    cases limit <;> simp_all [codecEncodingAgrees, checkedSerialize, Ssz.Desc.wellFormed,
      Ssz.serialize, Ssz.boundCheck, Bind.bind, Except.bind, Pure.pure, Except.pure]
  | Err error =>
    rcases agrees with ⟨rfl, cap, rfl, over⟩
    simp [codecEncodingAgrees, codecFaultAgrees, checkedSerialize, Ssz.Desc.wellFormed,
      Ssz.serialize, Ssz.boundCheck, Nat.not_le.mpr over,
      Bind.bind, Except.bind]

end NyxSszVerification
