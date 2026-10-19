import FastSszVerification.Merkleize.Depth
import FastSszVerification.Merkleize.Subtree

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxRecDepth 4096
set_option maxHeartbeats 200000

namespace FastSszVerification

def merkleizeAgrees : core.result.Result RustNode FastSszRust.merkle.MerkleizeError →
    Except Ssz.Err Ssz.Bytes → Prop
  | .Ok root, .ok expected => bytesToSpec root.val = expected
  | .Err .LimitTooSmall, .error (.merkleizeLimit _ _) => True
  | _, _ => False

theorem merkleize_refines (chunks : Slice RustNode) (limit : Option Usize) :
    FastSszRust.merkle.merkleize chunks limit ⦃ actual =>
      merkleizeAgrees actual (Ssz.merkleizeBounded (proofNodes chunks.val).toArray
        (limit.map (fun capacity => capacity.val))) ⦄ := by
  have room := depthFor_machine_bound (limit.getD (Slice.len chunks))
  cases chosen : limit
  all_goals simp only [chosen, Option.getD_none, Option.getD_some] at room
  all_goals unfold FastSszRust.merkle.merkleize
  all_goals step*
  all_goals simp_all [merkleizeAgrees, Ssz.merkleizeBounded, subtreeAt_nodeTree,
    Bind.bind, Except.bind, Pure.pure, Except.pure,
    MonadExcept.throw, throwThe, MonadExceptOf.throw]
  all_goals split_ifs <;> simp_all
  all_goals omega

end FastSszVerification
