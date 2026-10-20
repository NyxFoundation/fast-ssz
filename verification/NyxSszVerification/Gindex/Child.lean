import NyxSszVerification.Gindex.Arithmetic

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace NyxSszVerification

@[step] theorem gindex_child_refines (index : U128) (rightSide : Bool) :
    NyxSszRust.gindex.child index rightSide ⦃ actual =>
      gindexResultAgrees UScalar.val U128.max actual (.ok (Ssz.gindexChild index.val rightSide)) ⦄ := by
  cases side : rightSide <;> unfold NyxSszRust.gindex.child <;> step*
  all_goals simp_all [gindexResultAgrees, Ssz.gindexChild]
  all_goals step*


end NyxSszVerification
