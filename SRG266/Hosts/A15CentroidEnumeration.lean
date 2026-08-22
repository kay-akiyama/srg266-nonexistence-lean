/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Hosts.A15ProjectorSoundness
import SRG266.Certificates.A15CentroidData
import SRG266.Hosts.A15FastEligibleCore
import SRG266.Hosts.A15ReducedProfile

/-!
# Native enumeration of canonical A15 centroid profiles

This module enumerates nondecreasing 16-coordinate vectors with common residue
modulo four, coordinate sum zero, and squared norm 4800.

The recursive search keeps only sound feasibility tests:

* the accumulated squared norm does not exceed 4800;
* the remaining nondecreasing coordinates can still have the required sum;
* the Cauchy bound permits the remaining squared norm.

At a complete profile Lean recomputes the eligible four-subset count and
retains exactly the profiles with at least 74 shell vectors.  The threshold is
forced by 220 occurrences of multiplicity at most three.
-/

open scoped BigOperators

namespace SRG266

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- All integers in `[-69,69]` with a prescribed residue modulo four. -/
def a15EnumerationValues (residue : ℤ) : Array ℤ :=
  ((List.range 139).map fun k => (k : ℤ) - 69).filter
    (fun z => z % 4 = residue) |>.toArray

/-- Sound feasibility tests after fixing the multiplicities of `±m`.
All remaining reduced coordinates have absolute value at most `m - 1`. -/
def a15MagnitudeFeasible
    (residue : ℤ) (m remaining : ℕ) (newSum : ℤ)
    (newSq : ℕ) : Bool :=
  let targetSum := a15ReducedTargetSum residue
  let targetSq := a15ReducedTargetSq residue
  let nextMagnitude := m - 1
  decide (
    newSq ≤ targetSq ∧
    targetSq ≤ newSq + remaining * nextMagnitude ^ 2 ∧
    (targetSum - newSum).natAbs ≤ remaining * nextMagnitude)

/-- Recursive search by absolute-value multiplicities.  Processing
magnitudes from 17 down to one reduces the search tree from about 24 million
prefixes to fewer than two million states while preserving a transparent
completeness proof. -/
def a15EnumerateByMagnitudeAux
    (residue : ℤ) :
    (m remaining : ℕ) → (sum : ℤ) → (sq : ℕ) →
      List ℤ → List ℤ → List (Array ℤ)
  | 0, remaining, sum, sq, negatives, positives =>
      if sum = a15ReducedTargetSum residue &&
          sq = a15ReducedTargetSq residue then
        let reduced :=
          negatives ++ List.replicate remaining 0 ++ positives
        let profile := a15ScaleReducedProfile residue reduced
        if decide (74 ≤
            a15FastEligibleCountReduced residue reduced) then
          [profile]
        else
          []
      else
        []
  | m + 1, remaining, sum, sq, negatives, positives =>
      (List.range (remaining + 1)).flatMap fun negativeCount =>
        let positiveBound :=
          if residue = 2 && m + 1 = 17 then 0
          else remaining - negativeCount
        (List.range (positiveBound + 1)).flatMap fun positiveCount =>
          let used := negativeCount + positiveCount
          let newRemaining := remaining - used
          let signedMultiplicity : ℤ :=
            (positiveCount : ℤ) - negativeCount
          let newSum := sum + signedMultiplicity * (m + 1)
          let newSq := sq + used * (m + 1) ^ 2
          if a15MagnitudeFeasible residue (m + 1) newRemaining
              newSum newSq then
            a15EnumerateByMagnitudeAux residue m newRemaining
              newSum newSq
              (negatives ++
                List.replicate negativeCount (-((m + 1 : ℕ) : ℤ)))
              (List.replicate positiveCount ((m + 1 : ℕ) : ℤ) ++
                positives)
          else
            []

def a15EnumeratedCandidateProfiles : List (Array ℤ) :=
  a15EnumerateByMagnitudeAux 0 17 16 0 0 [] [] ++
    a15EnumerateByMagnitudeAux 2 17 16 0 0 [] []

/-- The profile arrays already accompanied by checked separators or survivor
records. -/
def a15ListedCandidateProfiles : List (Array ℤ) :=
  a15GeneratedCentroidCertificates.map (fun certificate => certificate.d) ++
    a15GeneratedCentroidSurvivors.map (fun survivor => survivor.d)

end SRG266
