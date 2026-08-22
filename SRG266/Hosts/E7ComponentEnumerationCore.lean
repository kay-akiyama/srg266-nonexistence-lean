/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import Mathlib.Data.List.GetD
import Mathlib.Tactic

/-!
# Lightweight E7 component enumerator

This module contains the executable definitions and elementary profile
identities.  The signed-magnitude completeness proof remains in
`E7ComponentEnumeration`, so structural producers need not import it.
-/

namespace SRG266

set_option maxRecDepth 100000

def e7ComponentTargetSum (parity : ℕ) : ℤ :=
  if parity = 0 then 0 else -4

def e7ComponentTargetSq (parity : ℕ) : ℕ :=
  if parity = 0 then 300 else 302

def e7ScaleReducedProfile
    (parity : ℕ) (coordinates : List ℤ) : Array ℤ :=
  (coordinates.map fun z : ℤ => 2 * z + (parity : ℤ)).toArray

def e7ComponentEnumerationProfile (coordinates : Array ℤ) :
    Fin 8 → ℤ :=
  fun i => coordinates.getD i.1 0

namespace Lattice

theorem e7ScaleReducedProfile_size (parity : ℕ) (coordinates : List ℤ) :
    (e7ScaleReducedProfile parity coordinates).size = coordinates.length := by
  simp [e7ScaleReducedProfile]

/-- The profile of a scaled reduced coordinate list, coordinatewise. -/
theorem e7ComponentEnumerationProfile_scale_apply (parity : ℕ)
    (coordinates : List ℤ) (hlength : coordinates.length = 8) (i : Fin 8) :
    e7ComponentEnumerationProfile (e7ScaleReducedProfile parity coordinates) i =
      2 * coordinates.getD i.1 0 + parity := by
  unfold e7ComponentEnumerationProfile e7ScaleReducedProfile
  have hi : i.1 < coordinates.length := by
    rw [hlength]
    exact i.2
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
    List.getElem?_eq_getElem hi]
  simp only [Option.map_some, Option.getD_some]
  rw [List.getD_eq_getElem coordinates 0 hi]

end Lattice

/-- Necessary feasibility tests for the unused lower magnitudes. -/
def e7ComponentMagnitudeFeasible
    (parity m remaining : ℕ) (newSum : ℤ) (newSq : ℕ) : Bool :=
  let nextMagnitude := m - 1
  decide (
    newSq ≤ e7ComponentTargetSq parity ∧
    (e7ComponentTargetSum parity - newSum).natAbs ≤
      remaining * nextMagnitude)

def e7EnumerateComponentsByMagnitudeAux
    (parity : ℕ) :
    (m remaining : ℕ) → (sum : ℤ) → (sq : ℕ) →
      List ℤ → List ℤ → List (Array ℤ)
  | 0, remaining, sum, sq, negatives, positives =>
      if sum = e7ComponentTargetSum parity &&
          decide (sq ≤ e7ComponentTargetSq parity) then
        let reduced :=
          negatives ++ List.replicate remaining 0 ++ positives
        [e7ScaleReducedProfile parity reduced]
      else
        []
  | m + 1, remaining, sum, sq, negatives, positives =>
      (List.range (remaining + 1)).flatMap fun negativeCount =>
        let positiveBound :=
          if parity = 1 && m + 1 = 17 then 0
          else remaining - negativeCount
        (List.range (positiveBound + 1)).flatMap fun positiveCount =>
          let used := negativeCount + positiveCount
          let newRemaining := remaining - used
          let signedMultiplicity : ℤ :=
            (positiveCount : ℤ) - negativeCount
          let newSum := sum + signedMultiplicity * (m + 1)
          let newSq := sq + used * (m + 1) ^ 2
          if e7ComponentMagnitudeFeasible parity (m + 1)
              newRemaining newSum newSq then
            e7EnumerateComponentsByMagnitudeAux parity m newRemaining
              newSum newSq
              (negatives ++
                List.replicate negativeCount (-((m + 1 : ℕ) : ℤ)))
              (List.replicate positiveCount ((m + 1 : ℕ) : ℤ) ++
                positives)
          else
            []

def e7EnumeratedComponentProfiles : List (Array ℤ) :=
  e7EnumerateComponentsByMagnitudeAux 0 17 8 0 0 [] [] ++
    e7EnumerateComponentsByMagnitudeAux 1 17 8 0 0 [] []

end SRG266
