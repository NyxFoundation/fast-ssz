import Ssz.Merkle.Verify

/-! Executable regressions against the unchanged pinned SSZ implementation.
Run from verification: lake env lean --run ../tools/multiproof-oracle.lean -/

open Ssz

def explicitTree : Nat → Nat → Bytes
  | 0, index => Array.replicate 32 index.toUInt8
  | depth + 1, index => combine (explicitTree depth (2 * index))
      (explicitTree depth (2 * index + 1))

def require (label : String) (passed : Bool) : IO Unit :=
  unless passed do throw (IO.userError label)

def fault {T : Type} (result : Except Err T) : String :=
  match result with
  | .ok _ => "success"
  | .error (.notAGindex _) => "zero"
  | .error .rootHasNoBranch => "root"
  | .error .emptyRequest => "empty"
  | .error .repeatedIndex => "repeated"
  | .error (.nestedIndex _) => "nested"
  | .error (.leafCount _ _) => "leaves"
  | .error (.proofLength _ _) => "proof"
  | .error _ => "unexpected"

def checkErrors : IO Unit := do
  for (indices, expected) in
      [([], "empty"), ([0, 0], "repeated"), ([1, 1], "repeated"),
       ([0, 1], "zero"), ([1, 0], "root"), ([4, 2, 0], "nested"),
       ([0, 4, 2], "zero"), ([2, 4], "nested"), ([4, 1], "root")] do
    require s!"helper precedence {indices}" (fault (getHelperIndices indices) == expected)
    let leaves := indices.map fun _ => zeroChunk
    require s!"root precedence {indices}"
      (fault (calculateMultiMerkleRoot leaves [] indices) == expected)
  require "leaf-count precedence" (fault (calculateMultiMerkleRoot [] [] [0, 0]) == "leaves")
  require "short proof" (fault (calculateMultiMerkleRoot [zeroChunk] [] [2]) == "proof")
  require "long proof"
    (fault (calculateMultiMerkleRoot [zeroChunk, zeroChunk] [zeroChunk] [2, 3]) == "proof")

def sameSuccess {T : Type} [BEq T] (actual expected : Except Err T) : Bool :=
  match actual, expected with
  | .ok left, .ok right => left == right
  | _, _ => false

def checkTree : IO Unit := do
  let root := explicitTree 3 1
  let leaves := [explicitTree 0 8, explicitTree 0 10, explicitTree 0 14]
  let proof := [explicitTree 0 15, explicitTree 0 11, explicitTree 0 9, explicitTree 1 6]
  require "shared helpers" (sameSuccess (getHelperIndices [8, 10, 14]) (.ok [15, 11, 9, 6]))
  require "root reconstruction" (sameSuccess (calculateMultiMerkleRoot leaves proof [8, 10, 14]) (.ok root))
  require "acceptance" (sameSuccess (verifyMerkleMultiproof leaves proof [8, 10, 14] root) (.ok true))
  require "proof ordering" (sameSuccess (verifyMerkleMultiproof leaves proof.reverse [8, 10, 14] root) (.ok false))
  require "root mismatch" (sameSuccess (verifyMerkleMultiproof leaves proof [8, 10, 14] zeroChunk) (.ok false))
  require "sibling claims" (sameSuccess (getHelperIndices [2, 3]) (.ok []))
  require "sibling root"
    (sameSuccess (calculateMultiMerkleRoot [explicitTree 2 3, explicitTree 2 2] [] [3, 2]) (.ok root))
  require "mixed depths" (sameSuccess (calculateMultiMerkleRoot
    [explicitTree 1 4, explicitTree 1 5, explicitTree 2 3] [] [4, 5, 3]) (.ok root))

def checkDepths : IO Unit := do
  for depth in List.range 128 |>.drop 1 do
    let index := 2 ^ depth
    let proof := List.replicate depth zeroChunk
    require s!"depth {depth}"
      (sameSuccess (calculateMultiMerkleRoot [zeroChunk] proof [index])
        (calculateMerkleRoot zeroChunk proof index))
  for index in [2 ^ 128 - 1, 2 ^ 127 + 12345] do
    let proof := List.replicate 127 zeroChunk
    require s!"top-bit index {index}"
      (sameSuccess (calculateMultiMerkleRoot [zeroChunk] proof [index])
        (calculateMerkleRoot zeroChunk proof index))

def main : IO Unit := do
  checkErrors
  checkTree
  checkDepths
  IO.println "Pinned multiproof executable: precedence, explicit trees and 128-bit depths passed"
