/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.Int.Basic

/-!
# Lightweight executable core of the mined E7 norm search

This module contains only the eight-coordinate signed-magnitude recursion.
It deliberately imports neither E7 shell geometry nor the structural
completeness proof, so bounded output certificates have a small memory floor.
-/

namespace SRG266

def e7MinedNormCase (sq : ℕ) : Bool :=
  decide (sq = 8 ∨ sq = 16 ∨ sq = 24 ∨ sq = 32 ∨ sq = 40)

def e7MinedCommonParity (coordinates : List ℤ) : Bool :=
  coordinates.all fun z => z % 2 = coordinates.getD 0 0 % 2

/-- Necessary pruning for a remaining signed-magnitude path. -/
def e7MinedMagnitudeFeasible
    (m remaining : ℕ) (newSum : ℤ) (newSq : ℕ) : Bool :=
  let nextMagnitude := m - 1
  decide (
    newSq ≤ 40 ∧
    newSum.natAbs ≤ remaining * nextMagnitude)

/-- Canonical eight-coordinate recursion after division by five. -/
def e7MinedEnumerateByMagnitudeAux :
    (m remaining : ℕ) → (sum : ℤ) → (sq : ℕ) →
      List ℤ → List ℤ → List (List ℤ)
  | 0, remaining, sum, sq, negatives, positives =>
      if sum = 0 && e7MinedNormCase sq then
        let coordinates :=
          negatives ++ List.replicate remaining 0 ++ positives
        if e7MinedCommonParity coordinates then [coordinates] else []
      else
        []
  | m + 1, remaining, sum, sq, negatives, positives =>
      (List.range (remaining + 1)).flatMap fun negativeCount =>
        (List.range (remaining - negativeCount + 1)).flatMap fun positiveCount =>
          let used := negativeCount + positiveCount
          let newRemaining := remaining - used
          let signedMultiplicity : ℤ :=
            (positiveCount : ℤ) - negativeCount
          let newSum := sum + signedMultiplicity * (m + 1)
          let newSq := sq + used * (m + 1) ^ 2
          if e7MinedMagnitudeFeasible (m + 1) newRemaining newSum newSq then
            e7MinedEnumerateByMagnitudeAux m newRemaining newSum newSq
              (negatives ++
                List.replicate negativeCount (-((m + 1 : ℕ) : ℤ)))
              (List.replicate positiveCount ((m + 1 : ℕ) : ℤ) ++
                positives)
          else
            []

def e7MinedNormProfiles : List (List ℤ) :=
  e7MinedEnumerateByMagnitudeAux 6 8 0 0 [] []

end SRG266
