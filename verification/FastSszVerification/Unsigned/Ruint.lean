import FastSszRust.Ruint

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace FastSszVerification

abbrev RustU256 := FastSszRust.ruint.Uint 256#usize 4#usize

@[step] theorem div_ceil_256_64 :
    FastSszRust.core.num.Usize.div_ceil 256#usize 64#usize ⦃ result => result = 4#usize ⦄ := by
  unfold FastSszRust.core.num.Usize.div_ceil
  step*

@[step] theorem u256_limb_count :
    FastSszRust.ruint.Uint.LIMBS_1 256#usize 4#usize ⦃ result => result = 4#usize ⦄ := by
  unfold FastSszRust.ruint.Uint.LIMBS_1 FastSszRust.ruint.nlimbs
  step*

@[step] theorem u256_mask :
    FastSszRust.ruint.Uint.MASK 256#usize 4#usize ⦃ result => result = core.num.U64.MAX ⦄ := by
  unfold FastSszRust.ruint.Uint.MASK FastSszRust.ruint.mask
  step*

@[step] theorem u256_should_mask :
    FastSszRust.ruint.Uint.SHOULD_MASK 256#usize 4#usize ⦃ result => result = false ⦄ := by
  unfold FastSszRust.ruint.Uint.SHOULD_MASK
  step*

@[step] theorem u256_as_limbs (value : RustU256) :
    FastSszRust.ruint.Uint.as_limbs value ⦃ limbs => limbs = value.limbs ⦄ := by
  simp [FastSszRust.ruint.Uint.as_limbs]

@[step] theorem u256_from_limbs (limbs : Array U64 4#usize) :
    FastSszRust.ruint.Uint.from_limbs 256#usize limbs ⦃ value => value.limbs = limbs ⦄ := by
  unfold FastSszRust.ruint.Uint.from_limbs
  step*

end FastSszVerification
