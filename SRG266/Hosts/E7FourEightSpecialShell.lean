/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Certificates.E7FourEightSpecialCrossMaskBridge

/-!
# Shell coordinates for the special `4 × 8` E7 residual

This module isolates the product description of the eligible shell and the
transport of the right centroid equations to second-factor column totals.
-/

open scoped BigOperators

namespace SRG266
namespace E7FourEightSpecial

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def d₄ : Fin 8 → ℤ :=
  E7FourEightSpecialCrossData.d₄

def d₈ : Fin 8 → ℤ :=
  ![-4, 0, 0, 0, 0, 0, 0, 4]

abbrev FirstWeight := E7FourEightSpecialCrossData.FirstWeight

abbrev SecondWeight :=
  {w : E7WeightIndex // e7ResidualEvaluation d₈ w = 2}

instance : Fintype SecondWeight :=
  Fintype.subtype
    (Finset.univ.filter fun w => e7ResidualEvaluation d₈ w = 2)
    (by simp)

abbrev Shell := E7ResidualEligibleIndex d₄ d₈

theorem pair_eligible (a : FirstWeight) (b : SecondWeight) :
    e7ResidualEligible d₄ d₈ (a.1, b.1) := by
  simp only [e7ResidualEligible, b.2]
  change e7ResidualEvaluation E7FourEightSpecialCrossData.d₄ a.1 + 2 = 3
  rw [a.2]
  norm_num

private theorem d₄_evaluation_upper (u : E7WeightIndex) :
    e7ResidualEvaluation d₄ u ≤ 2 := by
  revert u
  decide +kernel

private theorem d₈_evaluation_cases (v : E7WeightIndex) :
    e7ResidualEvaluation d₈ v = -2 ∨
      e7ResidualEvaluation d₈ v = 0 ∨
      e7ResidualEvaluation d₈ v = 2 := by
  revert v
  decide +kernel

theorem eligible_labels (w : Shell) :
    e7ResidualEvaluation d₄ w.1.1 = 1 ∧
      e7ResidualEvaluation d₈ w.1.2 = 2 := by
  have hleft := d₄_evaluation_upper w.1.1
  have hright := d₈_evaluation_cases w.1.2
  have heligible := w.2
  unfold e7ResidualEligible at heligible
  rcases hright with hright | hright | hright <;> omega

/-- Product coordinates for every eligible shell vector. -/
def shellEquiv : SecondWeight × FirstWeight ≃ Shell where
  toFun x := ⟨(x.2.1, x.1.1), pair_eligible x.2 x.1⟩
  invFun w :=
    (⟨w.1.2, (eligible_labels w).2⟩,
     ⟨w.1.1, (eligible_labels w).1⟩)
  left_inv x := by
    rcases x with ⟨b, a⟩
    rfl
  right_inv w := by
    apply Subtype.ext
    rfl

/-- Multiplicity in one of the 12 second-factor columns. -/
def columnTotal (packing : E7ShellPacking d₄ d₈)
    (b : SecondWeight) : ℕ :=
  ∑ a : FirstWeight,
    packing.multiplicity (shellEquiv (b, a))

theorem weighted_column_sum
    (packing : E7ShellPacking d₄ d₈) (f : SecondWeight → ℤ) :
    ∑ w : Shell, (packing.multiplicity w : ℤ) *
        f ⟨w.1.2, (eligible_labels w).2⟩ =
      ∑ b : SecondWeight, (columnTotal packing b : ℤ) * f b := by
  calc
    (∑ w : Shell, (packing.multiplicity w : ℤ) *
        f ⟨w.1.2, (eligible_labels w).2⟩) =
        ∑ x : SecondWeight × FirstWeight,
          (packing.multiplicity (shellEquiv x) : ℤ) * f x.1 := by
      symm
      exact shellEquiv.sum_comp fun w =>
        (packing.multiplicity w : ℤ) *
          f ⟨w.1.2, (eligible_labels w).2⟩
    _ = ∑ b : SecondWeight, ∑ a : FirstWeight,
          (packing.multiplicity (shellEquiv (b, a)) : ℤ) * f b := by
      rw [Fintype.sum_prod_type]
    _ = ∑ b : SecondWeight, (columnTotal packing b : ℤ) * f b := by
      apply Finset.sum_congr rfl
      intro b _
      rw [columnTotal]
      push_cast
      rw [Finset.sum_mul]

theorem right_affine_by_columns
    (packing : E7ShellPacking d₄ d₈)
    (q₀ : ℤ) (q : Fin 8 → ℤ) :
    ∑ b : SecondWeight, (columnTotal packing b : ℤ) *
        (q₀ + integerDot q (e7Weight4 b.1)) =
      q₀ * 220 + 110 * integerDot q d₈ := by
  rw [← weighted_column_sum packing
    (fun b => q₀ + integerDot q (e7Weight4 b.1))]
  simpa only using packing.right_affine_sum q₀ q

end E7FourEightSpecial
end SRG266
