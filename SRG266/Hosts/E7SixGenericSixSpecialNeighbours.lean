/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Hosts.E7SixGenericSixSpecialTotal

/-! # Critical-neighbour transport in the residual `6g × 6s` E7 shell -/

open scoped BigOperators Matrix

namespace SRG266
namespace E7SixGenericSixSpecial

open E7SixGenericSixSpecialData

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem critical_neighbour_sum_eq_global
    (packing : E7ShellPacking d₆g d₆s) (i : CriticalIndex) :
    ∑ j ∈ criticalNeighbours i,
        packing.multiplicity (criticalVertex j) =
      ∑ w ∈ globalNeighbours i, packing.multiplicity w := by
  let critical : Finset Shell :=
    Finset.univ.filter fun w =>
      e7ResidualEvaluation d₆g w.1.1 = 0
  have hequiv :
      (∑ j : CriticalIndex,
          if e7ShellInner (criticalVertex i).1 (criticalVertex j).1 = 2
            then packing.multiplicity (criticalVertex j) else 0) =
        ∑ w : CriticalShell,
          if e7ShellInner (criticalVertex i).1 w.1.1 = 2
            then packing.multiplicity w.1 else 0 := by
    simpa only [criticalEquiv_apply] using
      criticalEquiv.sum_comp
        (fun w : CriticalShell =>
          if e7ShellInner (criticalVertex i).1 w.1.1 = 2
            then packing.multiplicity w.1 else 0)
  have hleft :
      (∑ j ∈ criticalNeighbours i,
          packing.multiplicity (criticalVertex j)) =
        ∑ j : CriticalIndex,
          if e7ShellInner (criticalVertex i).1 (criticalVertex j).1 = 2
            then packing.multiplicity (criticalVertex j) else 0 := by
    rw [criticalNeighbours, Finset.sum_filter]
  have hsubtype :
      (∑ w : CriticalShell,
          if e7ShellInner (criticalVertex i).1 w.1.1 = 2
            then packing.multiplicity w.1 else 0) =
        ∑ w ∈ critical,
          if e7ShellInner (criticalVertex i).1 w.1 = 2
            then packing.multiplicity w else 0 := by
    symm
    apply Finset.sum_subtype
    intro w
    simp [critical]
  have hcritical_filter :
      (∑ w ∈ critical,
          if e7ShellInner (criticalVertex i).1 w.1 = 2
            then packing.multiplicity w else 0) =
        ∑ w ∈ globalNeighbours i, packing.multiplicity w := by
    simp only [critical, globalNeighbours, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro w _
    by_cases hinner : e7ShellInner (criticalVertex i).1 w.1 = 2
    · have hcritical := inner_two_closed i w hinner
      simp [hinner, hcritical]
    · simp [hinner]
  rw [hleft, hequiv, hsubtype, hcritical_filter]

theorem critical_row_eq_thirty
    (packing : E7ShellPacking d₆g d₆s) (i : CriticalIndex)
    (hi : 0 < packing.multiplicity (criticalVertex i)) :
    ∑ j : CriticalIndex,
        criticalC i j * packing.multiplicity (criticalVertex j) = 30 := by
  have hprofile := packing.twoProfile (criticalVertex i) hi
  have hneighbours :
      (∑ j : CriticalIndex,
          (if e7ShellInner (criticalVertex i).1 (criticalVertex j).1 = 2
            then 1 else 0) *
            packing.multiplicity (criticalVertex j)) =
        ∑ j ∈ criticalNeighbours i,
          packing.multiplicity (criticalVertex j) := by
    rw [criticalNeighbours, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    split <;> simp_all
  have hdiagonal :
      (∑ j : CriticalIndex, (if i = j then 3 else 0) *
          packing.multiplicity (criticalVertex j)) =
        3 * packing.multiplicity (criticalVertex i) := by
    simp
  simp only [criticalC, add_mul, Finset.sum_add_distrib]
  rw [hneighbours, hdiagonal,
    critical_neighbour_sum_eq_global packing i]
  simpa only [globalNeighbours] using hprofile

end E7SixGenericSixSpecial
end SRG266
