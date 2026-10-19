import NyxSszRust.Ruint

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace NyxSszVerification

abbrev RustU256 := NyxSszRust.ruint.Uint 256#usize 4#usize

@[step] theorem div_ceil_256_64 :
    NyxSszRust.core.num.Usize.div_ceil 256#usize 64#usize ⦃ result => result = 4#usize ⦄ := by
  unfold NyxSszRust.core.num.Usize.div_ceil
  step*

@[step] theorem u256_limb_count :
    NyxSszRust.ruint.Uint.LIMBS_1 256#usize 4#usize ⦃ result => result = 4#usize ⦄ := by
  unfold NyxSszRust.ruint.Uint.LIMBS_1 NyxSszRust.ruint.nlimbs
  step*

@[step] theorem u256_mask :
    NyxSszRust.ruint.Uint.MASK 256#usize 4#usize ⦃ result => result = core.num.U64.MAX ⦄ := by
  unfold NyxSszRust.ruint.Uint.MASK NyxSszRust.ruint.mask
  step*

@[step] theorem u256_should_mask :
    NyxSszRust.ruint.Uint.SHOULD_MASK 256#usize 4#usize ⦃ result => result = false ⦄ := by
  unfold NyxSszRust.ruint.Uint.SHOULD_MASK
  step*

@[step] theorem u256_as_limbs (value : RustU256) :
    NyxSszRust.ruint.Uint.as_limbs value ⦃ limbs => limbs = value.limbs ⦄ := by
  simp [NyxSszRust.ruint.Uint.as_limbs]

@[step] theorem u256_from_limbs (limbs : Array U64 4#usize) :
    NyxSszRust.ruint.Uint.from_limbs 256#usize limbs ⦃ value => value.limbs = limbs ⦄ := by
  unfold NyxSszRust.ruint.Uint.from_limbs
  step*

end NyxSszVerification
