/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Hosts.E7SixGenericSixSpecialQuadraticBase

/-! # Cast and double-sum lemmas for the residual `6g × 6s` E7 shell -/

open scoped BigOperators Matrix

namespace SRG266
namespace E7SixGenericSixSpecial

open E7SixGenericSixSpecialData

set_option maxHeartbeats 2000000

theorem criticalQuadratic_cast
    (packing : E7ShellPacking d₆g d₆s) :
    (criticalQuadratic packing : ℚ) =
      ∑ i : CriticalIndex, ∑ j : CriticalIndex,
        (packing.multiplicity (criticalVertex i) : ℚ) *
          criticalC i j *
          (packing.multiplicity (criticalVertex j) : ℚ) := by
  simp only [criticalQuadratic]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem criticalTotal_cast
    (packing : E7ShellPacking d₆g d₆s) :
    (criticalTotal packing : ℚ) =
      ∑ i : CriticalIndex,
        (packing.multiplicity (criticalVertex i) : ℚ) := by
  rw [criticalTotal]
  push_cast
  rfl

theorem double_sum_product_eq_square (x : CriticalIndex → ℚ) :
    (∑ i : CriticalIndex, ∑ j : CriticalIndex, x i * x j) =
      (∑ i : CriticalIndex, x i) ^ 2 := by
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]

end E7SixGenericSixSpecial
end SRG266
