/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Hosts.E7ResidualCore
import Mathlib.Data.Fintype.Card
import Lean.Elab.Tactic.Omega

/-! # Bounded empty-shell check for the excluded mined E7 pair -/

namespace SRG266

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def e7MinedPairEligibleCount (pair : List ℤ × List ℤ) : ℕ :=
  Fintype.card
    (E7ResidualEligibleIndex
      (fun i => pair.1.getD i.1 0) (fun i => pair.2.getD i.1 0))

def e7MinedSixSpecialProfile (i : Fin 8) : ℤ :=
  [-3, -3, 1, 1, 1, 1, 1, 1].getD i.1 0

/-- The only norm-complementary pair not already named by `E7ResidualType`. -/
def e7MinedExcludedSixSpecialPair : List ℤ × List ℤ :=
  ([-3, -3, 1, 1, 1, 1, 1, 1],
    [-3, -3, 1, 1, 1, 1, 1, 1])

/-- Every minuscule weight evaluates oddly on the special norm-six
representative. -/
theorem e7MinedSixSpecialProfile_evaluation_odd
    (w : E7WeightIndex) :
    e7ResidualEvaluation e7MinedSixSpecialProfile w % 2 = 1 := by
  have hall : ∀ v : E7WeightIndex,
      e7ResidualEvaluation e7MinedSixSpecialProfile v % 2 = 1 := by
    decide +kernel
  exact hall w

/-- The sole extra norm-complementary pair has no eligible shell columns. -/
theorem e7MinedExcludedSixSpecialPair_eligibleCount :
    e7MinedPairEligibleCount e7MinedExcludedSixSpecialPair = 0 := by
  unfold e7MinedPairEligibleCount
  rw [Fintype.card_eq_zero_iff]
  refine ⟨fun w => ?_⟩
  have hleft := e7MinedSixSpecialProfile_evaluation_odd w.1.1
  have hright := e7MinedSixSpecialProfile_evaluation_odd w.1.2
  have heligible := w.2
  change e7ResidualEvaluation e7MinedSixSpecialProfile w.1.1 +
      e7ResidualEvaluation e7MinedSixSpecialProfile w.1.2 = 3 at heligible
  omega

end SRG266
