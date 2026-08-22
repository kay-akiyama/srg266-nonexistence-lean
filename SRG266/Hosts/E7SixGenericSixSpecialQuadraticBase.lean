/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Hosts.E7SixGenericSixSpecialNeighbours

/-! # The critical quadratic count for the residual `6g × 6s` E7 shell -/

open scoped BigOperators Matrix

namespace SRG266
namespace E7SixGenericSixSpecial

open E7SixGenericSixSpecialData

def criticalQuadratic (packing : E7ShellPacking d₆g d₆s) : ℕ :=
  ∑ i : CriticalIndex,
    packing.multiplicity (criticalVertex i) *
      ∑ j : CriticalIndex,
        criticalC i j * packing.multiplicity (criticalVertex j)

theorem criticalQuadratic_eq
    (packing : E7ShellPacking d₆g d₆s) :
    criticalQuadratic packing = 30 * criticalTotal packing := by
  rw [criticalQuadratic, criticalTotal, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : packing.multiplicity (criticalVertex i) = 0
  · simp [hi]
  · have hpos := Nat.pos_of_ne_zero hi
    rw [critical_row_eq_thirty packing i hpos]
    ring

end E7SixGenericSixSpecial
end SRG266
