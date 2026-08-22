/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.CocliqueDesign

/-!
# Excluding the `D₁₂⁺` host

The norm-three shell of `D₁₂⁺` is represented by half-integral sign vectors
`ε / 2`.  After normalizing the centroid to a sign vector `d`, eligibility is
`d · ε = 6`.  The coordinates where `ε` differs from `d` form a binary
weight-three vector.

This file packages only the exact coordinate data needed from that shell
description.  It proves natively that every such realization is a
one-integral factorization of the local Gram matrix.  Consequently it is
impossible under the named quasi-symmetric-design nonexistence input.
-/

open scoped BigOperators Matrix

namespace SRG266

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A normalized realization of the local Gram vectors in the norm-three
spinor shell of `D₁₂⁺`.  The equation `spinor_gram` is cleared of the common
denominator four. -/
structure D12PlusGramRealization (x : V) where
  centroidSign : Fin 12 → ℤ
  spinorSign :
    Matrix (Fin 12) (SecondSubconstituent G x) ℤ
  centroidSign_cases :
    ∀ j, centroidSign j = -1 ∨ centroidSign j = 1
  spinorSign_cases :
    ∀ j B, spinorSign j B = -1 ∨ spinorSign j B = 1
  eligibility :
    ∀ B, ∑ j, centroidSign j * spinorSign j B = 6
  spinor_gram :
    ∀ B C, ∑ j, spinorSign j B * spinorSign j C =
      4 * localGramMatrix G x B C

/-- Binary coordinate recording disagreement between a spinor sign and the
centroid sign. -/
def d12BinaryFactor
    {x : V}
    (r : D12PlusGramRealization G x) :
    Matrix (Fin 12) (SecondSubconstituent G x) ℤ :=
  fun j B =>
    if r.centroidSign j * r.spinorSign j B = -1 then 1 else 0

theorem d12_centroidSign_sq
    {x : V}
    (r : D12PlusGramRealization G x)
    (j : Fin 12) :
    r.centroidSign j * r.centroidSign j = 1 := by
  rcases r.centroidSign_cases j with hneg | hpos
  · simp [hneg]
  · simp [hpos]

theorem d12_sign_product_cases
    {x : V}
    (r : D12PlusGramRealization G x)
    (j : Fin 12) (B : SecondSubconstituent G x) :
    r.centroidSign j * r.spinorSign j B = -1 ∨
      r.centroidSign j * r.spinorSign j B = 1 := by
  rcases r.centroidSign_cases j with hdneg | hdpos
  · rcases r.spinorSign_cases j B with heneg | hepos
    · right
      rw [hdneg, heneg]
      norm_num
    · left
      rw [hdneg, hepos]
      norm_num
  · rcases r.spinorSign_cases j B with heneg | hepos
    · left
      rw [hdpos, heneg]
      norm_num
    · right
      rw [hdpos, hepos]
      norm_num

theorem two_mul_d12BinaryFactor
    {x : V}
    (r : D12PlusGramRealization G x)
    (j : Fin 12) (B : SecondSubconstituent G x) :
    2 * d12BinaryFactor G r j B =
      1 - r.centroidSign j * r.spinorSign j B := by
  rcases d12_sign_product_cases G r j B with hneg | hpos
  · simp [d12BinaryFactor, hneg]
  · simp [d12BinaryFactor, hpos]

theorem d12BinaryFactor_gram
    {x : V}
    (r : D12PlusGramRealization G x) :
    (d12BinaryFactor G r).transpose * d12BinaryFactor G r =
      localGramMatrix G x := by
  ext B C
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  let W := d12BinaryFactor G r
  have hB :
      ∀ j, 2 * W j B =
        1 - r.centroidSign j * r.spinorSign j B := by
    intro j
    exact two_mul_d12BinaryFactor G r j B
  have hC :
      ∀ j, 2 * W j C =
        1 - r.centroidSign j * r.spinorSign j C := by
    intro j
    exact two_mul_d12BinaryFactor G r j C
  have heligB := r.eligibility B
  have heligC := r.eligibility C
  have hgram := r.spinor_gram B C
  have hfour :
      4 * (∑ j, W j B * W j C) =
        ∑ j, r.spinorSign j B * r.spinorSign j C := by
    calc
      4 * (∑ j, W j B * W j C) =
          ∑ j, (2 * W j B) * (2 * W j C) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = ∑ j,
          (1 - r.centroidSign j * r.spinorSign j B) *
            (1 - r.centroidSign j * r.spinorSign j C) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hB j, hC j]
      _ = (12 : ℤ) -
          (∑ j, r.centroidSign j * r.spinorSign j B) -
          (∑ j, r.centroidSign j * r.spinorSign j C) +
          (∑ j, r.spinorSign j B * r.spinorSign j C) := by
        have hcross :
            (∑ j,
                (r.centroidSign j * r.spinorSign j B) *
                  (r.centroidSign j * r.spinorSign j C)) =
              ∑ j, r.spinorSign j B * r.spinorSign j C := by
          apply Finset.sum_congr rfl
          intro j _
          calc
            (r.centroidSign j * r.spinorSign j B) *
                (r.centroidSign j * r.spinorSign j C) =
              (r.centroidSign j * r.centroidSign j) *
                (r.spinorSign j B * r.spinorSign j C) := by ring
            _ = r.spinorSign j B * r.spinorSign j C := by
              rw [d12_centroidSign_sq G r j]
              ring
        have hones : (∑ _j : Fin 12, (1 : ℤ)) = 12 := by norm_num
        simp_rw [sub_mul, mul_sub]
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
          Finset.sum_sub_distrib]
        simp only [one_mul, mul_one]
        rw [hcross, hones]
        ring
      _ = ∑ j, r.spinorSign j B * r.spinorSign j C := by
        rw [heligB, heligC]
        norm_num
  change (∑ j, W j B * W j C) = localGramMatrix G x B C
  rw [hgram] at hfour
  omega

theorem localGram_oneIntegrable_of_d12PlusRealization
    {x : V}
    (r : D12PlusGramRealization G x) :
    LocalGramIsOneIntegrable G x := by
  exact ⟨12, d12BinaryFactor G r, d12BinaryFactor_gram G r⟩

/-- Exclusion of the `D₁₂⁺` branch from quasi-symmetric design
nonexistence. -/
theorem no_d12PlusRealization
    (hMT : NoQuasiSymmetricDesign56.{u})
    (hG : IsHypothetical G) (x : V) :
    ¬Nonempty (D12PlusGramRealization G x) := by
  rintro ⟨r⟩
  exact
    (localGram_not_oneIntegrable_of_noQuasiSymmetricDesign
      G hMT hG x)
      (localGram_oneIntegrable_of_d12PlusRealization G r)

end SRG266
