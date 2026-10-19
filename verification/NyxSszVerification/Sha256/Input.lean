import NyxSszVerification.Sha256.Core

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace NyxSszVerification

def specWord (a b c d : UInt8) : UInt32 :=
  a.toUInt32 <<< 24 ||| b.toUInt32 <<< 16 ||| c.toUInt32 <<< 8 ||| d.toUInt32

@[simp] theorem word_refines (a b c d : U8) :
    NyxSszRust.sha256.word a b c d = RustM.ok (wordFromSpec
      (specWord (byteToSpec a) (byteToSpec b) (byteToSpec c) (byteToSpec d))) := by
  simp [NyxSszRust.sha256.word, lift, specWord, wordFromSpec, byteToSpec]
  rfl

@[step] theorem word_spec (a b c d : U8) :
    NyxSszRust.sha256.word a b c d ⦃ result =>
      wordToSpec result = specWord (byteToSpec a) (byteToSpec b) (byteToSpec c) (byteToSpec d) ⦄ := by
  simp only [word_refines, spec_ok, wordToSpec_fromSpec]

def nodeMessage (left right : Array U8 32#usize) : ByteArray :=
  ⟨bytesToSpec left.val ++ bytesToSpec right.val⟩

def nodeWords (left right : Array U8 32#usize) : Vector UInt32 16 :=
  Vector.ofFn fun index => Ssz.Sha256.wordAt (nodeMessage left right) (4 * index.val)

@[step] theorem input_words_refines (left right : Array U8 32#usize) :
    NyxSszRust.sha256.input_words left right ⦃ result =>
      wordsToSpec result = nodeWords left right ⦄ := by
  unfold NyxSszRust.sha256.input_words
  step*
  apply Vector.toArray_inj.mp
  apply _root_.Array.ext
  · simp [wordsToSpec, nodeWords]
  · intro index leftBound rightBound
    have bound : index < 16 := by simpa [nodeWords] using rightBound
    interval_cases index <;>
      simp_all [wordsToSpec, nodeWords, nodeMessage, bytesToSpec, Ssz.Sha256.wordAt,
        specWord, Aeneas.Std.Array.make, ByteArray.get!]

end NyxSszVerification
