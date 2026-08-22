/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Hosts.A15CentroidSolution
import Mathlib.Data.List.GetD

/-!
# Lightweight reduced A15 profiles

This is the common coordinate interface between the lattice branch, the
mined search and the enumerator. It contains no enumeration data.
-/

namespace SRG266

/-- View a compact 16-coordinate array as a centroid function. -/
def a15EnumerationProfile (coordinates : Array ℤ) : Fin 16 → ℤ :=
  fun i => coordinates.getD i.1 0

/-- Convert reduced coordinates `aᵢ` to scaled coordinates `4aᵢ + r`. -/
def a15ScaleReducedProfile (residue : ℤ) (coordinates : List ℤ) :
    Array ℤ :=
  (coordinates.map fun z => 4 * z + residue).toArray

def a15ReducedTargetSum (residue : ℤ) : ℤ :=
  if residue = 0 then 0 else -8

def a15ReducedTargetSq (residue : ℤ) : ℕ :=
  if residue = 0 then 300 else 304

/-- Coordinatewise meaning of scaling a length-16 reduced profile. -/
theorem a15EnumerationProfile_scale_apply
    (residue : ℤ) (coordinates : List ℤ)
    (hlength : coordinates.length = 16)
    (i : Fin 16) :
    a15EnumerationProfile
        (a15ScaleReducedProfile residue coordinates) i =
      4 * coordinates.getD i.1 0 + residue := by
  unfold a15EnumerationProfile a15ScaleReducedProfile
  have hi : i.1 < coordinates.length := by
    rw [hlength]
    exact i.2
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getElem?_map, List.getElem?_eq_getElem hi]
  simp only [Option.map_some, Option.getD_some]
  rw [List.getD_eq_getElem coordinates 0 hi]

end SRG266
