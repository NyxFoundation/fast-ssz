import FastSszVerification.Representation

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace FastSszVerification

theorem bytesToSpec_injective : Function.Injective bytesToSpec := by
  intro left right same
  apply (List.map_inj_right byteToSpec_injective).mp
  have lists := congrArg _root_.Array.toList same
  simpa [bytesToSpec] using lists

theorem bytesToSpec_array_size {n : Usize} (bytes : Array U8 n) :
    (bytesToSpec bytes.val).size = n.val := by
  simp [bytesToSpec]

@[step] theorem byte_array_eq_refines {n : Usize} (left right : Array U8 n) :
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 left right ⦃ result =>
      result ↔ bytesToSpec left.val = bytesToSpec right.val ⦄ := by
  have element : ∀ x y, core.cmp.PartialEqU8.ne x y ⦃ result => result ↔ ¬ x = y ⦄ := by
    intro x y
    simp
  change core.slice.cmp.PartialEqSlice.eq core.cmp.PartialEqU8
    left.to_slice right.to_slice ⦃ result =>
      result ↔ bytesToSpec left.val = bytesToSpec right.val ⦄
  apply spec_mono (core.slice.cmp.PartialEqSlice.eq_homo_spec
    core.cmp.PartialEqU8 left.to_slice right.to_slice element)
  intro result equal
  simpa only [Slice.eq_iff, Array.val_to_slice, bytesToSpec_injective.eq_iff] using equal

end FastSszVerification
