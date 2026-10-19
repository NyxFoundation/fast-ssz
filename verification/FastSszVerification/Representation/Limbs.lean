import FastSszVerification.Representation.Integers
import Mathlib.Tactic.IntervalCases

open Aeneas Aeneas.Std

namespace FastSszVerification

theorem little_endian_append (lowWidth highWidth : Nat)
    (low : BitVec (8 * lowWidth)) (high : BitVec (8 * highWidth)) :
    (high ++ low).toLEBytes = low.toLEBytes ++ high.toLEBytes := by
  have lowLength : low.toLEBytes.length = lowWidth := by rw [BitVec.toLEBytes_length]; omega
  have highLength : high.toLEBytes.length = highWidth := by rw [BitVec.toLEBytes_length]; omega
  apply List.ext_getElem
  · simp only [BitVec.toLEBytes_length, List.length_append, lowLength, highLength]
    omega
  intro index whole joined
  apply (Byte.eq_iff _ _).mpr
  intro bit inside
  have position : 8 * index + bit < 8 * highWidth + 8 * lowWidth := by
    simp only [List.length_append, lowLength, highLength] at joined
    omega
  rw [BitVec.toLEBytes_getElem_testBit _ index bit whole ⟨inside, position⟩,
    BitVec.getElem_append]
  by_cases within : index < lowWidth
  · have lowPosition : 8 * index + bit < 8 * lowWidth := by omega
    rw [dif_pos lowPosition, List.getElem_append_left (by omega)]
    exact (BitVec.toLEBytes_getElem_testBit low index bit (by omega) ⟨inside, lowPosition⟩).symm
  · have outside : ¬ 8 * index + bit < 8 * lowWidth := by omega
    have difference : 8 * index + bit - 8 * lowWidth = 8 * (index - lowWidth) + bit := by omega
    rw [dif_neg outside, List.getElem_append_right (by omega)]
    simp only [lowLength, difference]
    exact (BitVec.toLEBytes_getElem_testBit high (index - lowWidth) bit (by omega)
      ⟨inside, by omega⟩).symm

theorem list_eight_eta {α : Type} [Inhabited α] (values : List α) (sized : values.length = 8) :
    [values[0]!, values[1]!, values[2]!, values[3]!, values[4]!, values[5]!,
      values[6]!, values[7]!] = values := by
  apply List.ext_getElem
  · simp [sized]
  intro index left right
  have bound : index < 8 := by omega
  interval_cases index <;> simp only [List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals
    symm
    exact List.Inhabited_getElem_eq_getElem! _ _ right

theorem list_indices_eta {α : Type} [Inhabited α] (values : List α) (count : Nat)
    (sized : values.length = count) :
    (List.range count).map (fun index => values[index]!) = values := by
  apply List.ext_getElem
  · simp [sized]
  intro index left right
  simp only [List.getElem_map, List.getElem_range]
  exact (List.Inhabited_getElem_eq_getElem! _ _ right).symm

theorem list_thirtytwo_eta {α : Type} [Inhabited α] (values : List α)
    (sized : values.length = 32) :
    [values[0]!, values[1]!, values[2]!, values[3]!, values[4]!, values[5]!, values[6]!, values[7]!,
      values[8]!, values[9]!, values[10]!, values[11]!, values[12]!, values[13]!, values[14]!, values[15]!,
      values[16]!, values[17]!, values[18]!, values[19]!, values[20]!, values[21]!, values[22]!, values[23]!,
      values[24]!, values[25]!, values[26]!, values[27]!, values[28]!, values[29]!, values[30]!, values[31]!] =
        values := by
  change (List.range 32).map (fun index => values[index]!) = values
  exact list_indices_eta values 32 sized

end FastSszVerification
