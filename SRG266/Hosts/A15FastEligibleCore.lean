/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import Batteries.Data.ByteArray
import Mathlib.Data.Int.Basic

/-!
# Lightweight executable core of the A15 eligible-shell counter

This module isolates the byte pair-sum counter from the A15 geometry and the
large checked four-subset table.  Small evaluation certificates can therefore
use the early-exiting counter without loading either source of proof data.
-/

namespace SRG266

/-- Reduced coordinates shifted from `[-17,17]` to byte values in
`[0,34]`. -/
def a15ShiftedReducedCoordinateBytes (coordinates : List ℤ) : ByteArray :=
  coordinates.foldl (fun bytes z =>
    bytes.push (z + 17).toNat.toUInt8)
    (ByteArray.emptyWithCapacity 16)

/-- Add the pair sums `(i,j)` for every `i < j` to a byte histogram. -/
def a15AddPairSums (coordinates : ByteArray) (j : ℕ) :
    ℕ → ByteArray → ByteArray
  | 0, counts => counts
  | i + 1, counts =>
      let index :=
        (coordinates.get! i).toNat + (coordinates.get! j).toNat
      let counts := counts.set! index
        ((counts.get! index).toNat + 1).toUInt8
      a15AddPairSums coordinates j i counts

/-- Count completions `(k,l)` against all stored pairs `i < j < k`. -/
def a15CountPairCompletions
    (coordinates counts : ByteArray) (targetBase k : ℕ) :
    (l fuel : ℕ) → ℕ
  | _, 0 => 0
  | l, fuel + 1 =>
      let rightSum :=
        (coordinates.get! k).toNat + (coordinates.get! l).toNat
      let contribution :=
        if rightSum ≤ targetBase ∧ targetBase - rightSum ≤ 68 then
          (counts.get! (targetBase - rightSum)).toNat
        else
          0
      contribution +
        a15CountPairCompletions coordinates counts targetBase k
          (l + 1) fuel

/-- Count four-subsets having either target sum, stopping once the only
queried threshold, 74, has been reached. -/
def a15FastFourSumCountLoop
    (coordinates : ByteArray) (firstTargetBase secondTargetBase : ℕ) :
    (k fuel : ℕ) → ByteArray → ℕ → ℕ
  | _, 0, _, total => total
  | k, fuel + 1, counts, total =>
      if 74 ≤ total then total
      else
        let counts := a15AddPairSums coordinates (k - 1) (k - 1) counts
        let completionFuel := 15 - k
        let total :=
          total +
            a15CountPairCompletions coordinates counts firstTargetBase k
              (k + 1) completionFuel +
            a15CountPairCompletions coordinates counts secondTargetBase k
              (k + 1) completionFuel
        a15FastFourSumCountLoop coordinates firstTargetBase secondTargetBase
          (k + 1) fuel counts total

/-- Fast eligible-shell count on reduced coordinates. -/
def a15FastEligibleCountReduced
    (residue : ℤ) (coordinates : List ℤ) : ℕ :=
  let shifted := a15ShiftedReducedCoordinateBytes coordinates
  let zeroCounts : ByteArray := ⟨Array.replicate 69 0⟩
  let firstTargetBase := if residue = 0 then 83 else 81
  let secondTargetBase := if residue = 0 then 53 else 51
  a15FastFourSumCountLoop shifted firstTargetBase secondTargetBase
    2 13 zeroCounts 0

end SRG266
