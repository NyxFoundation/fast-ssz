import FastSszVerification.Sha256.Input

open Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace FastSszVerification

theorem nodeMessage_size (left right : Array U8 32#usize) :
    (nodeMessage left right).size = 64 := by
  simp [nodeMessage, bytesToSpec, ByteArray.size]

theorem pad_size64 (message : ByteArray) (size : message.size = 64) :
    (Ssz.Sha256.pad message).size = 128 := by
  change message.data.size = 64 at size
  simp [Ssz.Sha256.pad, Ssz.Sha256.paddingZeros, Ssz.Sha256.lengthBytes, ByteArray.size, size]

theorem hash_two_blocks (message : ByteArray) (size : message.size = 64) :
    Ssz.Sha256.hash message = Ssz.Sha256.digest
      (Ssz.Sha256.compress
        (Ssz.Sha256.compress Ssz.Sha256.initialState (Ssz.Sha256.pad message) 0)
        (Ssz.Sha256.pad message) 64) := by
  dsimp only [Ssz.Sha256.hash]
  rw [pad_size64 message size]
  rfl

theorem padded_get_prefix (message : ByteArray) (size : message.size = 64)
    (index : Nat) (bound : index < 64) :
    (Ssz.Sha256.pad message).get! index = message.get! index := by
  have dataSize : message.data.size = 64 := size
  have before : index < message.data.size := by rw [dataSize]; exact bound
  have paddedSize : (Ssz.Sha256.pad message).data.size = 128 := pad_size64 message size
  have padded : index < (Ssz.Sha256.pad message).data.size := by omega
  have b65 : index < 65 := by omega
  change (Ssz.Sha256.pad message).data[index]! = message.data[index]!
  rw [getElem!_pos (Ssz.Sha256.pad message).data index padded,
    getElem!_pos message.data index before]
  change message.data.size = 64 at size
  simp [Ssz.Sha256.pad, Ssz.Sha256.paddingZeros, Ssz.Sha256.lengthBytes,
    _root_.Array.getElem_push, ByteArray.size, size, bound, b65]

theorem padded_first_word (message : ByteArray) (size : message.size = 64)
    (index : Nat) (bound : index < 16) :
    Ssz.Sha256.wordAt (Ssz.Sha256.pad message) (4 * index) =
      Ssz.Sha256.wordAt message (4 * index) := by
  unfold Ssz.Sha256.wordAt
  rw [padded_get_prefix message size (4 * index) (by omega),
    padded_get_prefix message size (4 * index + 1) (by omega),
    padded_get_prefix message size (4 * index + 2) (by omega),
    padded_get_prefix message size (4 * index + 3) (by omega)]

def paddingWords : Vector UInt32 16 :=
  #v[0x80000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 512]

theorem padding_word_agrees (message : ByteArray) (size : message.size = 64)
    (index : Nat) (bound : index < 16) :
    paddingWords[index] = Ssz.Sha256.wordAt (Ssz.Sha256.pad message) (64 + 4 * index) := by
  change message.data.size = 64 at size
  interval_cases index <;>
    simp [paddingWords, Ssz.Sha256.wordAt, Ssz.Sha256.pad, Ssz.Sha256.paddingZeros,
      Ssz.Sha256.lengthBytes, ByteArray.get!, ByteArray.size, size,
      getElem!_pos, _root_.Array.getElem_push] <;> rfl

@[simp] theorem initial_state_refines :
    stateToSpec {
      a := 1779033703#u32, b := 3144134277#u32, c := 1013904242#u32, d := 2773480762#u32,
      e := 1359893119#u32, f := 2600822924#u32, g := 528734635#u32, h := 1541459225#u32 } =
      Ssz.Sha256.initialState := by
  rfl

@[simp] theorem padding_input_refines :
    wordsToSpec (Array.make 16#usize [2147483648#u32, 0#u32, 0#u32, 0#u32,
      0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32,
      0#u32, 0#u32, 0#u32, 512#u32]) = paddingWords := by
  decide

theorem node_words_agree (left right : Array U8 32#usize) (index : Nat) (bound : index < 16) :
    (nodeWords left right)[index] =
      Ssz.Sha256.wordAt (Ssz.Sha256.pad (nodeMessage left right)) (0 + 4 * index) := by
  rw [nodeWords, Vector.getElem_ofFn]
  simpa using (padded_first_word (nodeMessage left right) (nodeMessage_size left right) index bound).symm

@[step] theorem hash_pair_spec (left right : Array U8 32#usize) :
    FastSszRust.sha256.hash_pair left right ⦃ result =>
      bytesToSpec result.val = Ssz.combine (bytesToSpec left.val) (bytesToSpec right.val) ⦄ := by
  unfold FastSszRust.sha256.hash_pair
  step*
  have size := nodeMessage_size left right
  have firstEq := referenceCompress_eq Ssz.Sha256.initialState (nodeWords left right)
    (Ssz.Sha256.pad (nodeMessage left right)) 0 (node_words_agree left right)
  have secondEq := referenceCompress_eq
    (Ssz.Sha256.compress Ssz.Sha256.initialState (Ssz.Sha256.pad (nodeMessage left right)) 0)
    paddingWords (Ssz.Sha256.pad (nodeMessage left right)) 64
    (padding_word_agrees (nodeMessage left right) size)
  change _ = (Ssz.Sha256.hash (nodeMessage left right)).data
  rw [hash_two_blocks (nodeMessage left right) size]
  simp_all only [initial_state_refines, padding_input_refines]

/-- Every 512-bit input terminates and produces the exact upstream Merkle parent. -/
theorem hash_pair_refines (left right : Array U8 32#usize) :
    ∃ result, FastSszRust.sha256.hash_pair left right = RustM.ok result ∧
      bytesToSpec result.val = Ssz.combine (bytesToSpec left.val) (bytesToSpec right.val) := by
  exact spec_imp_exists (hash_pair_spec left right)

end FastSszVerification
