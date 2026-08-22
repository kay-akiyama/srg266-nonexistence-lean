/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Certificates.Farkas

/-!
# Exact Farkas certificates for nonnegative rational systems

For an integer system `A x = b`, a vector `q` satisfying

`Aᵀ q ≥ 0` and `b · q < 0`

rules out every nonnegative rational solution.  This is the elementary finite
sum argument used by the fractional near-frame certificates.  The theorem is
proved once here; generated modules only evaluate integer dot products.
-/

open scoped BigOperators Matrix

namespace SRG266

/-- Exact strict separation for the nonnegative orthant. -/
abbrev NonnegativeFarkasSeparates
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℤ) (b q : ι → ℤ) : Prop :=
  (∀ j, 0 ≤ integerDot q (fun i => A i j)) ∧ integerDot q b < 0

/-- Soundness of an integer Farkas separator against nonnegative rational
solutions. -/
theorem no_nonnegative_rational_solution_of_integer_farkas
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℤ) (b q : ι → ℤ)
    (hsep : NonnegativeFarkasSeparates A b q) :
    ¬∃ x : κ → ℚ,
      (∀ j, 0 ≤ x j) ∧
      (∀ i, ∑ j, (A i j : ℚ) * x j = (b i : ℚ)) := by
  rintro ⟨x, hx, hAx⟩
  have hdot : ((integerDot q b : ℤ) : ℚ) =
      ∑ j, x j * ((integerDot q (fun i => A i j) : ℤ) : ℚ) := by
    calc
      ((integerDot q b : ℤ) : ℚ) =
          ∑ i, (q i : ℚ) * (b i : ℚ) := by
            simp only [integerDot, Int.cast_sum, Int.cast_mul]
      _ = ∑ i, (q i : ℚ) * ∑ j, (A i j : ℚ) * x j := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hAx i]
      _ = ∑ i, ∑ j, (q i : ℚ) * ((A i j : ℚ) * x j) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
      _ = ∑ j, ∑ i, (q i : ℚ) * ((A i j : ℚ) * x j) := by
            rw [Finset.sum_comm]
      _ = ∑ j, x j * ((integerDot q (fun i => A i j) : ℤ) : ℚ) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [integerDot, Int.cast_sum, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            rw [Int.cast_mul]
            ring
  have hright : 0 ≤
      ∑ j, x j * ((integerDot q (fun i => A i j) : ℤ) : ℚ) := by
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (hx j) (by exact_mod_cast hsep.1 j)
  have hleft : ((integerDot q b : ℤ) : ℚ) < 0 := by
    exact_mod_cast hsep.2
  rw [hdot] at hleft
  exact (not_lt_of_ge hright) hleft

/-- Boolean checker for generated nonnegative Farkas certificates. -/
def checkNonnegativeFarkas
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι κ ℤ) (b q : ι → ℤ) : Bool :=
  decide (NonnegativeFarkasSeparates A b q)

theorem checkNonnegativeFarkas_sound
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι κ ℤ) (b q : ι → ℤ)
    (hcheck : checkNonnegativeFarkas A b q = true) :
    ¬∃ x : κ → ℚ,
      (∀ j, 0 ≤ x j) ∧
      (∀ i, ∑ j, (A i j : ℚ) * x j = (b i : ℚ)) := by
  apply no_nonnegative_rational_solution_of_integer_farkas A b q
  exact of_decide_eq_true (by
    simpa only [checkNonnegativeFarkas] using hcheck)

end SRG266
