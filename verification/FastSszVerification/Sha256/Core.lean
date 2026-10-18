import FastSszVerification.Representation
import FastSszRust.Sha256
import Ssz.Merkle.Tree
import Mathlib.Tactic.IntervalCases

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace FastSszVerification

/-- Identical 32-bit words in the Rust model and reference. -/
def wordToSpec (value : U32) : UInt32 := ⟨value.bv⟩

def wordFromSpec (value : UInt32) : U32 := ⟨value.toBitVec⟩

@[simp] theorem wordToSpec_fromSpec (value : UInt32) :
    wordToSpec (wordFromSpec value) = value := rfl

@[simp] theorem wordFromSpec_toSpec (value : U32) :
    wordFromSpec (wordToSpec value) = value := rfl

@[simp] theorem sigma0_refines (value : U32) :
    FastSszRust.sha256.sigma0 value =
      RustM.ok (wordFromSpec (Ssz.Sha256.sigma0 (wordToSpec value))) := by
  simp [FastSszRust.sha256.sigma0, Ssz.Sha256.sigma0,
    Ssz.Sha256.rotr, wordFromSpec, wordToSpec]
  rfl

@[simp] theorem sigma1_refines (value : U32) :
    FastSszRust.sha256.sigma1 value =
      RustM.ok (wordFromSpec (Ssz.Sha256.sigma1 (wordToSpec value))) := by
  simp [FastSszRust.sha256.sigma1, Ssz.Sha256.sigma1,
    Ssz.Sha256.rotr, wordFromSpec, wordToSpec]
  rfl

@[simp] theorem bigSigma0_refines (value : U32) :
    FastSszRust.sha256.big_sigma0 value =
      RustM.ok (wordFromSpec (Ssz.Sha256.bigSigma0 (wordToSpec value))) := by
  simp [FastSszRust.sha256.big_sigma0, Ssz.Sha256.bigSigma0,
    Ssz.Sha256.rotr, wordFromSpec, wordToSpec]
  rfl

@[simp] theorem bigSigma1_refines (value : U32) :
    FastSszRust.sha256.big_sigma1 value =
      RustM.ok (wordFromSpec (Ssz.Sha256.bigSigma1 (wordToSpec value))) := by
  simp [FastSszRust.sha256.big_sigma1, Ssz.Sha256.bigSigma1,
    Ssz.Sha256.rotr, wordFromSpec, wordToSpec]
  rfl

@[simp] theorem choose_refines (x y z : U32) :
    FastSszRust.sha256.choose x y z = RustM.ok
      (wordFromSpec (Ssz.Sha256.choose (wordToSpec x) (wordToSpec y) (wordToSpec z))) := by
  rfl

@[simp] theorem majority_refines (x y z : U32) :
    FastSszRust.sha256.majority x y z = RustM.ok
      (wordFromSpec (Ssz.Sha256.majority (wordToSpec x) (wordToSpec y) (wordToSpec z))) := by
  rfl

def stateToSpec (state : FastSszRust.sha256.State) : Vector UInt32 8 :=
  #v[wordToSpec state.a, wordToSpec state.b, wordToSpec state.c, wordToSpec state.d,
     wordToSpec state.e, wordToSpec state.f, wordToSpec state.g, wordToSpec state.h]

@[step] theorem round_refines (state : FastSszRust.sha256.State) (constant message : U32) :
    FastSszRust.sha256.round state constant message ⦃ result =>
      stateToSpec result = Ssz.Sha256.round (stateToSpec state)
        (wordToSpec constant) (wordToSpec message) ⦄ := by
  simp only [FastSszRust.sha256.round, bigSigma1_refines, bigSigma0_refines,
    choose_refines, majority_refines, lift, bind_tc_ok, spec_ok]
  rfl

def wordsToSpec {n : Usize} (words : Array U32 n) : Vector UInt32 n.val :=
  ⟨(words.val.map wordToSpec).toArray, by simp⟩

@[simp] theorem wordsToSpec_get {n : Usize} (words : Array U32 n)
    (index : Nat) (bound : index < n.val) :
    (wordsToSpec words)[index] =
      wordToSpec (words.val[index]'(by simpa only [Array.length_eq] using bound)) := by
  simp [wordsToSpec]

theorem roundConstants_refine :
    wordsToSpec FastSszRust.sha256.ROUND_CONSTANTS = Ssz.Sha256.roundConstants := by
  unfold wordsToSpec FastSszRust.sha256.ROUND_CONSTANTS Ssz.Sha256.roundConstants
  decide

@[simp] theorem roundConstant_get (index : Nat) (bound : index < 64) :
    wordToSpec (FastSszRust.sha256.ROUND_CONSTANTS.val[index]'(by simpa using bound)) =
      Ssz.Sha256.roundConstants[index] := by
  have same := congrArg (fun values : Vector UInt32 64 => values[index]) roundConstants_refine
  exact (wordsToSpec_get FastSszRust.sha256.ROUND_CONSTANTS index bound).symm.trans same

@[step] theorem round_at_refines (state : FastSszRust.sha256.State)
    (words : Array U32 64#usize) (index : Usize) (bound : index.val < 64) :
    FastSszRust.sha256.round_at state words index ⦃ result =>
      stateToSpec result = Ssz.Sha256.round (stateToSpec state)
        Ssz.Sha256.roundConstants[index.val] (wordsToSpec words)[index.val] ⦄ := by
  unfold FastSszRust.sha256.round_at
  step*
  simp_all only [wordsToSpec_get, roundConstant_get]

def referenceRounds (state : Vector UInt32 8) (words : Vector UInt32 64) : Vector UInt32 8 :=
  (List.finRange 64).foldl
    (fun current index => Ssz.Sha256.round current
      Ssz.Sha256.roundConstants[index] words[index]) state

@[step] theorem rounds_refine (state : FastSszRust.sha256.State)
    (words : Array U32 64#usize) :
    FastSszRust.sha256.rounds state words ⦃ result =>
      stateToSpec result = referenceRounds (stateToSpec state) (wordsToSpec words) ⦄ := by
  unfold FastSszRust.sha256.rounds
  step*
  simp_all only [referenceRounds, List.finRange, List.ofFn,
    Fin.foldr, Fin.foldr.loop, List.foldl, Fin.getElem_fin]
  rfl

@[simp] theorem wordToSpec_add (x y : U32) :
    wordToSpec (core.num.U32.wrapping_add x y) = wordToSpec x + wordToSpec y := rfl

@[step] theorem sigma0_spec (value : U32) :
    FastSszRust.sha256.sigma0 value ⦃ result =>
      wordToSpec result = Ssz.Sha256.sigma0 (wordToSpec value) ⦄ := by
  simp only [sigma0_refines, spec_ok, wordToSpec_fromSpec]

@[step] theorem sigma1_spec (value : U32) :
    FastSszRust.sha256.sigma1 value ⦃ result =>
      wordToSpec result = Ssz.Sha256.sigma1 (wordToSpec value) ⦄ := by
  simp only [sigma1_refines, spec_ok, wordToSpec_fromSpec]

@[simp] theorem wordsToSpec_set {n : Usize} (words : Array U32 n) (index : Usize)
    (value : U32) (bound : index.val < n.val) :
    wordsToSpec (words.set index value) =
      (wordsToSpec words).set index.val (wordToSpec value) bound := by
  apply Vector.toArray_inj.mp
  apply _root_.Array.toList_inj.mp
  simp [wordsToSpec, Array.set]

def extendWords (words : Vector UInt32 64) (index : Nat)
    (lower : 16 ≤ index) (upper : index < 64) : Vector UInt32 64 :=
  words.set index (words[index - 16]'(by omega) +
    Ssz.Sha256.sigma0 (words[index - 15]'(by omega)) + words[index - 7]'(by omega) +
    Ssz.Sha256.sigma1 (words[index - 2]'(by omega))) upper

@[step] theorem extend_schedule_refines (words : Array U32 64#usize) (index : Usize)
    (lower : 16 ≤ index.val) (upper : index.val < 64) :
    FastSszRust.sha256.extend_schedule words index ⦃ result =>
      wordsToSpec result = extendWords (wordsToSpec words) index.val lower upper ⦄ := by
  unfold FastSszRust.sha256.extend_schedule
  step*
  rw [result_post, wordsToSpec_set words index _ upper]
  unfold extendWords
  simp_all only [wordToSpec_add]
  have g16 := wordsToSpec_get words (index.val - 16) (by scalar_tac)
  have g15 := wordsToSpec_get words (index.val - 15) (by scalar_tac)
  have g7 := wordsToSpec_get words (index.val - 7) (by scalar_tac)
  have g2 := wordsToSpec_get words (index.val - 2) (by scalar_tac)
  have contents := congrArg₂ (fun x y : UInt32 => x + Ssz.Sha256.sigma1 y)
    (congrArg₂ (· + ·)
      (congrArg₂ (fun x y : UInt32 => x + Ssz.Sha256.sigma0 y) g16.symm g15.symm)
      g7.symm) g2.symm
  exact congrArg (fun value => (wordsToSpec words).set index.val value upper) contents

def initialWords (input : Vector UInt32 16) : Vector UInt32 64 :=
  ⟨input.toArray ++ _root_.Array.replicate 48 0, by simp⟩

@[step] theorem initial_schedule_refines (input : Array U32 16#usize) :
    FastSszRust.sha256.initial_schedule input ⦃ result =>
      wordsToSpec result = initialWords (wordsToSpec input) ⦄ := by
  unfold FastSszRust.sha256.initial_schedule
  step*
  apply Vector.toArray_inj.mp
  apply _root_.Array.toList_inj.mp
  simp_all [wordsToSpec, initialWords, Aeneas.Std.Array.set, Aeneas.Std.Array.repeat]
  have size : input.val.length = 16 := by scalar_tac
  apply List.ext_getElem
  · simp [size]
  · intro index leftBound rightBound
    have bound : index < 64 := by simpa using leftBound
    interval_cases index <;> simp [size, wordToSpec]

def fillPrefix (input : Vector UInt32 16) :
    (count : Nat) → count ≤ 48 → Vector UInt32 64
  | 0, _ => initialWords input
  | count + 1, bound =>
    extendWords (fillPrefix input count (by omega)) (count + 16) (by omega) (by omega)

def fillWords (input : Vector UInt32 16) : Vector UInt32 64 :=
  fillPrefix input 48 (by decide)

@[step] theorem schedule_refines (input : Array U32 16#usize) :
    FastSszRust.sha256.schedule input ⦃ result =>
      wordsToSpec result = fillWords (wordsToSpec input) ⦄ := by
  unfold FastSszRust.sha256.schedule
  step*
  simp_all only [fillWords, fillPrefix]

/-- The initial sixteen schedule words are the block words, without expansion. -/
theorem prefix_initial_get (input : Vector UInt32 16) (block : ByteArray) (start : Nat)
    (wordAgreement : ∀ index (bound : index < 16),
      input[index] = Ssz.Sha256.wordAt block (start + 4 * index))
    (count : Nat) (within : count ≤ 16) (index : Nat) (bound : index < count) :
    (Ssz.Sha256.schedulePrefix block start count)[index] = input[index]'(by omega) := by
  induction count generalizing index with
  | zero => omega
  | succ count ih =>
    have first : count < 16 := by omega
    rw [Ssz.Sha256.schedulePrefix, dif_pos first]
    by_cases earlier : index < count
    · rw [Vector.getElem_push_lt earlier]
      exact ih (by omega) index earlier
    · have same : index = count := by omega
      subst index
      rw [Vector.getElem_push_eq]
      exact (wordAgreement count first).symm

def PrefixMatches (words : Vector UInt32 64) (block : ByteArray) (start count : Nat) : Prop :=
  ∀ index (treeBound : index < 64) (readable : index < count),
    words[index] = (Ssz.Sha256.schedulePrefix block start count)[index]

theorem initialWords_get (input : Vector UInt32 16) (index : Nat) (bound : index < 16) :
    (initialWords input)[index]'(by omega) = input[index] := by
  simp [initialWords, bound]

theorem extend_prefix_matches (words : Vector UInt32 64) (block : ByteArray)
    (start count : Nat) (lower : 16 ≤ count) (upper : count < 64)
    (before : PrefixMatches words block start count) :
    PrefixMatches (extendWords words count lower upper) block start (count + 1) := by
  intro index treeBound readable
  by_cases same : index = count
  · subst index
    rw [extendWords, Vector.getElem_set_self]
    rw [Ssz.Sha256.schedulePrefix, dif_neg (by omega), Vector.getElem_push_eq]
    rw [before (count - 16) (by omega) (by omega),
      before (count - 15) (by omega) (by omega),
      before (count - 7) (by omega) (by omega),
      before (count - 2) (by omega) (by omega)]
  · have earlier : index < count := by omega
    rw [extendWords, Vector.getElem_set_ne upper treeBound (Ne.symm same)]
    rw [Ssz.Sha256.schedulePrefix, dif_neg (by omega), Vector.getElem_push_lt earlier]
    exact before index treeBound earlier

theorem fillPrefix_matches (input : Vector UInt32 16) (block : ByteArray) (start : Nat)
    (wordAgreement : ∀ index (bound : index < 16),
      input[index] = Ssz.Sha256.wordAt block (start + 4 * index))
    (count : Nat) (within : count ≤ 48) :
    PrefixMatches (fillPrefix input count within) block start (count + 16) := by
  induction count with
  | zero =>
    intro index treeBound readable
    rw [fillPrefix, initialWords_get input index readable]
    exact (prefix_initial_get input block start wordAgreement 16 (by decide) index readable).symm
  | succ count ih =>
    rw [fillPrefix]
    have previous := ih (by omega)
    have next := extend_prefix_matches (fillPrefix input count (by omega)) block start
      (count + 16) (by omega) (by omega) previous
    exact next

theorem fillWords_eq_schedule (input : Vector UInt32 16) (block : ByteArray) (start : Nat)
    (wordAgreement : ∀ index (bound : index < 16),
      input[index] = Ssz.Sha256.wordAt block (start + 4 * index)) :
    fillWords input = Ssz.Sha256.schedule block start := by
  apply Vector.ext
  intro index bound
  exact fillPrefix_matches input block start wordAgreement 48 (by decide) index bound bound

theorem state_add (initial working : FastSszRust.sha256.State) :
    stateToSpec {
      a := core.num.U32.wrapping_add initial.a working.a,
      b := core.num.U32.wrapping_add initial.b working.b,
      c := core.num.U32.wrapping_add initial.c working.c,
      d := core.num.U32.wrapping_add initial.d working.d,
      e := core.num.U32.wrapping_add initial.e working.e,
      f := core.num.U32.wrapping_add initial.f working.f,
      g := core.num.U32.wrapping_add initial.g working.g,
      h := core.num.U32.wrapping_add initial.h working.h } =
      (stateToSpec initial).zipWith (· + ·) (stateToSpec working) := by
  apply Vector.ext
  intro index bound
  interval_cases index <;> simp [stateToSpec]

def referenceCompress (state : Vector UInt32 8) (input : Vector UInt32 16) : Vector UInt32 8 :=
  state.zipWith (· + ·) (referenceRounds state (fillWords input))

@[step] theorem compress_refines (state : FastSszRust.sha256.State)
    (input : Array U32 16#usize) :
    FastSszRust.sha256.compress state input ⦃ result =>
      stateToSpec result = referenceCompress (stateToSpec state) (wordsToSpec input) ⦄ := by
  unfold FastSszRust.sha256.compress
  step*
  simp_all only [state_add, referenceCompress]

theorem referenceCompress_eq (state : Vector UInt32 8) (input : Vector UInt32 16)
    (block : ByteArray) (start : Nat)
    (wordAgreement : ∀ index (bound : index < 16),
      input[index] = Ssz.Sha256.wordAt block (start + 4 * index)) :
    referenceCompress state input = Ssz.Sha256.compress state block start := by
  unfold referenceCompress Ssz.Sha256.compress referenceRounds
  rw [fillWords_eq_schedule input block start wordAgreement]

@[step] theorem digest_refines (state : FastSszRust.sha256.State) :
    FastSszRust.sha256.digest state ⦃ result =>
      bytesToSpec result.val = (Ssz.Sha256.digest (stateToSpec state)).data ⦄ := by
  unfold FastSszRust.sha256.digest
  step*
  apply _root_.Array.ext
  · simp [bytesToSpec, Ssz.Sha256.digest]
  · intro index leftBound rightBound
    have bound : index < 32 := by simpa [bytesToSpec] using leftBound
    interval_cases index <;>
      simp_all [bytesToSpec, byteToSpec, wordToSpec, stateToSpec, Ssz.Sha256.digest,
        Aeneas.Std.Array.make, UScalar.cast] <;> rfl

end FastSszVerification
