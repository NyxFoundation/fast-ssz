import Aeneas

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace NyxSszVerification

theorem loop_total {State Output : Type} (body : State → RustM (ControlFlow State Output))
    (invariant : State → Prop) (measure : State → Nat) (post : Output → Prop)
    (iteration : ∀ state, invariant state → body state ⦃ flow =>
      match flow with
      | .cont next => invariant next ∧ measure next < measure state
      | .done output => post output ⦄)
    (initial : State) (valid : invariant initial) :
    loop body initial ⦃ post ⦄ := by
  generalize equation : measure initial = remaining
  induction remaining using Nat.strong_induction_on generalizing initial with
  | h remaining ih =>
    have observed := iteration initial valid
    rw [loop.eq_1]
    cases execution : body initial with
    | fail error =>
      rw [execution] at observed
      simp at observed
    | div =>
      rw [execution] at observed
      simp at observed
    | ok flow =>
      rw [execution] at observed
      simp only [spec_ok] at observed
      cases flow with
      | done output => simpa using observed
      | cont next => exact ih (measure next) (by omega) next observed.1 rfl

end NyxSszVerification
