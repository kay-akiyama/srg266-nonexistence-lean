/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Hosts.E7FourEightSpecialCapacity

/-!
# The special `4 × 8` residual `E₇ ⊕ E₇` shell

The shell, affine column identities, and cross-independence capacity argument
are developed in separate modules.  This facade combines their bounds into
the final contradiction `110 ≤ 6 · 15`.
-/

open scoped BigOperators

namespace SRG266
namespace E7FourEightSpecial

/-- The special `4 × 8` residual shell cannot contain the required packing. -/
theorem no_packing : IsEmpty (E7ShellPacking d₄ d₈) := by
  refine ⟨fun packing => ?_⟩
  have hsum := representative_column_total packing
  have hbound :
      (∑ r : PairIndex,
        columnTotal packing (positiveColumn r)) ≤
        ∑ _r : PairIndex, 15 :=
    Finset.sum_le_sum fun r _ => paired_column_total_le_fifteen packing r
  rw [hsum] at hbound
  have hpairs : Fintype.card PairIndex = 6 := by
    rfl
  simp [hpairs] at hbound

end E7FourEightSpecial
end SRG266
