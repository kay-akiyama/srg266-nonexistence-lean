/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import Mathlib.Data.List.Sort

/-!
# Canonical ordering for E7 component coordinates

E7 payload construction needs only a sorted permutation of its eight reduced
coordinates.  Using the library merge sort keeps that interface independent
of the signed-magnitude completeness proof used by the enumerator.
-/

namespace SRG266
namespace Lattice

/-- The nondecreasing ordering of a reduced E7 coordinate list. -/
def e7CanonicalReducedCoordinates (coordinates : List ℤ) : List ℤ :=
  coordinates.mergeSort (· ≤ ·)

theorem e7CanonicalReducedCoordinates_perm (coordinates : List ℤ) :
    (e7CanonicalReducedCoordinates coordinates).Perm coordinates := by
  exact List.mergeSort_perm coordinates (· ≤ ·)

theorem e7CanonicalReducedCoordinates_pairwise (coordinates : List ℤ) :
    (e7CanonicalReducedCoordinates coordinates).Pairwise (· ≤ ·) := by
  exact List.pairwise_mergeSort' (· ≤ ·) coordinates

end Lattice
end SRG266
