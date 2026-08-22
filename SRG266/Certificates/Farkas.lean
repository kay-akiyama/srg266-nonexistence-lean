/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Certificates.IntegerDot
import Mathlib.Tactic

/-!
# Exact bounded integer Farkas certificates

The shell certificates use systems `A m = b` with integer multiplicities
`0 ≤ m_j ≤ 3`.  A separator `q` rules out such a solution when

`q · b > 3 * ∑ j max 0 (q · A_j)`.

This file proves that rule once and for all using exact integer arithmetic.
Certificate modules may evaluate the finite inequality with bounded kernel
decisions; no linear-programming solver is trusted.
-/

open scoped BigOperators Matrix

namespace SRG266

/-- Positive part used in the bounded Farkas support function. -/
def integerPositivePart (z : ℤ) : ℤ :=
  max 0 z

/-- Exact strict-separation predicate for multiplicities bounded by three. -/
abbrev BoundedFarkasSeparates
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℤ) (b q : ι → ℤ) : Prop :=
  3 * ∑ j, integerPositivePart (integerDot q (fun i => A i j)) <
    integerDot q b

theorem bounded_mul_le_three_positivePart
    (m a : ℤ)
    (hm0 : 0 ≤ m) (hm3 : m ≤ 3) :
    m * a ≤ 3 * integerPositivePart a := by
  by_cases ha : a ≤ 0
  · have hma : m * a ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hm0 ha
    simp [integerPositivePart, max_eq_left ha]
    exact hma
  · have ha0 : 0 ≤ a := by omega
    have hmul := mul_le_mul_of_nonneg_right hm3 ha0
    simpa [integerPositivePart, max_eq_right ha0] using hmul

/-- Soundness of an exact bounded integer Farkas separator. -/
theorem no_bounded_solution_of_farkas
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℤ) (b q : ι → ℤ)
    (hsep : BoundedFarkasSeparates A b q) :
    ¬∃ m : κ → ℤ,
      (∀ j, 0 ≤ m j) ∧
      (∀ j, m j ≤ 3) ∧
      A *ᵥ m = b := by
  rintro ⟨m, hm0, hm3, hAm⟩
  have hdot :
      integerDot q b =
        ∑ j, m j * integerDot q (fun i => A i j) := by
    calc
      integerDot q b = integerDot q (A *ᵥ m) := by rw [hAm]
      _ = ∑ i, q i * ∑ j, A i j * m j := by
        simp only [integerDot, Matrix.mulVec_apply, dotProduct,
          Matrix.row_apply]
      _ = ∑ i, ∑ j, q i * (A i j * m j) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
      _ = ∑ j, ∑ i, q i * (A i j * m j) := by
        rw [Finset.sum_comm]
      _ = ∑ j, m j * integerDot q (fun i => A i j) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [integerDot, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hbound :
      (∑ j, m j * integerDot q (fun i => A i j)) ≤
        3 * ∑ j,
          integerPositivePart (integerDot q (fun i => A i j)) := by
    calc
      (∑ j, m j * integerDot q (fun i => A i j)) ≤
          ∑ j, 3 *
            integerPositivePart (integerDot q (fun i => A i j)) := by
        apply Finset.sum_le_sum
        intro j _
        exact bounded_mul_le_three_positivePart
          (m j) (integerDot q (fun i => A i j)) (hm0 j) (hm3 j)
      _ = 3 * ∑ j,
          integerPositivePart (integerDot q (fun i => A i j)) := by
        rw [Finset.mul_sum]
  rw [← hdot] at hbound
  exact (not_lt_of_ge hbound) hsep

/-- Boolean checker used by generated certificate modules. -/
def checkBoundedFarkas
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι κ ℤ) (b q : ι → ℤ) : Bool :=
  decide (BoundedFarkasSeparates A b q)

theorem checkBoundedFarkas_sound
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι κ ℤ) (b q : ι → ℤ)
    (hcheck : checkBoundedFarkas A b q = true) :
    ¬∃ m : κ → ℤ,
      (∀ j, 0 ≤ m j) ∧
      (∀ j, m j ≤ 3) ∧
      A *ᵥ m = b := by
  apply no_bounded_solution_of_farkas A b q
  exact of_decide_eq_true (by
    simpa only [checkBoundedFarkas] using hcheck)

end SRG266
