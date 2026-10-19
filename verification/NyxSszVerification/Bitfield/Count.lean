import NyxSszRust.Core

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace NyxSszVerification

@[step] theorem div_ceil_eight (length : Usize) :
    NyxSszRust.core.num.Usize.div_ceil length 8#usize ⦃ result =>
      result.val = (length.val + 7) / 8 ⦄ := by
  unfold NyxSszRust.core.num.Usize.div_ceil
  step*

end NyxSszVerification
