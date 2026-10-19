import FastSszRust.Core

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace FastSszVerification

@[step] theorem div_ceil_eight (length : Usize) :
    FastSszRust.core.num.Usize.div_ceil length 8#usize ⦃ result =>
      result.val = (length.val + 7) / 8 ⦄ := by
  unfold FastSszRust.core.num.Usize.div_ceil
  step*

end FastSszVerification
