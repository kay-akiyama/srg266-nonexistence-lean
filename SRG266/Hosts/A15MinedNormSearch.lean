/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.Int.Basic

/-!
# Lightweight executable core of the mined A15 norm search

This module contains only the divided integer recursion. In particular, its
bounded output certificates do not import A15 shell geometry, centroid
certificates, or the structural completeness proof.
-/

namespace SRG266

/-- Necessary pruning conditions for the norm-48 magnitude recursion. -/
def a15SmallMagnitudeFeasible
    (m remaining : ℕ) (newSum : ℤ) (newSq : ℕ) : Bool :=
  let nextMagnitude := m - 1
  decide (
    newSq ≤ 48 ∧
    48 ≤ newSq + remaining * nextMagnitude ^ 2 ∧
    newSum.natAbs ≤ remaining * nextMagnitude)

/-- All coordinates have the same parity as the first coordinate. -/
def a15SmallCommonParity (coordinates : List ℤ) : Bool :=
  coordinates.all fun z => z % 2 = coordinates.getD 0 0 % 2

/-- Magnitude recursion for the divided centroid coordinates. -/
def a15SmallEnumerateByMagnitudeAux :
    (m remaining : ℕ) → (sum : ℤ) → (sq : ℕ) →
      List ℤ → List ℤ → List (List ℤ)
  | 0, remaining, sum, sq, negatives, positives =>
      if sum = 0 && sq = 48 then
        let coordinates :=
          negatives ++ List.replicate remaining 0 ++ positives
        if a15SmallCommonParity coordinates then [coordinates] else []
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
          if a15SmallMagnitudeFeasible (m + 1) newRemaining newSum newSq then
            a15SmallEnumerateByMagnitudeAux m newRemaining newSum newSq
              (negatives ++
                List.replicate negativeCount (-((m + 1 : ℕ) : ℤ)))
              (List.replicate positiveCount ((m + 1 : ℕ) : ℤ) ++ positives)
          else
            []

/-- The complete small norm-profile computation. -/
def a15SmallNormProfiles : List (List ℤ) :=
  a15SmallEnumerateByMagnitudeAux 6 16 0 0 [] []

end SRG266
