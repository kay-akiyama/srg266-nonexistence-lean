/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic

/-!
# Exact rational LDLᵀ certificates

Finite residual shell arguments need positive-semidefinite lower bounds for
small explicit integer matrices.  A generator may discover an exact rational
factorization

`Dᵢⱼ = ∑ₖ Lᵢₖ dₖ Lⱼₖ`, with every `dₖ ≥ 0`.

This file supplies a Boolean checker and proves once that a checked
factorization makes the associated quadratic form nonnegative.  The
generator and floating-point spectral calculations are not trusted.
-/

open scoped BigOperators Matrix

namespace SRG266

/-- Quadratic form of a finite rational matrix. -/
def rationalQuadraticForm
    {ι : Type*} [Fintype ι]
    (D : Matrix ι ι ℚ) (x : ι → ℚ) : ℚ :=
  ∑ i, ∑ j, x i * D i j * x j

/-- Reflective checker for an exact rational `L diag(d) Lᵀ`
factorization. -/
def checkRationalLDLT
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (D : Matrix ι ι ℚ) (L : Matrix ι κ ℚ) (d : κ → ℚ) : Bool :=
  decide (
    (∀ k, 0 ≤ d k) ∧
    ∀ i j, D i j = ∑ k, L i k * d k * L j k)

/-- Row-wise form of the checker, useful for chunking larger exact
factorizations. -/
def checkRationalLDLTRow
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (D : Matrix ι ι ℚ) (L : Matrix ι κ ℚ) (d : κ → ℚ)
    (i : ι) : Bool :=
  decide (
    (∀ k, 0 ≤ d k) ∧
    ∀ j, D i j = ∑ k, L i k * d k * L j k)

theorem checkRationalLDLT_of_rows
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [Nonempty ι]
    (D : Matrix ι ι ℚ) (L : Matrix ι κ ℚ) (d : κ → ℚ)
    (hrows : ∀ i, checkRationalLDLTRow D L d i = true) :
    checkRationalLDLT D L d = true := by
  apply decide_eq_true
  constructor
  · intro k
    have hi :
        (∀ k, 0 ≤ d k) ∧
          ∀ j, D (Classical.arbitrary ι) j =
            ∑ k, L (Classical.arbitrary ι) k * d k * L j k :=
      of_decide_eq_true (by
        simpa only [checkRationalLDLTRow] using
          hrows (Classical.arbitrary ι))
    exact hi.1 k
  · intro i j
    have hi :
        (∀ k, 0 ≤ d k) ∧
          ∀ j, D i j = ∑ k, L i k * d k * L j k :=
      of_decide_eq_true (by
        simpa only [checkRationalLDLTRow] using hrows i)
    exact hi.2 j

/-- Integer checker for a scaled Gram factorization
`scale * D = L diag(weight) Lᵀ`. Keeping certificate evaluation in `ℤ`
is substantially faster than normalizing thousands of rational expressions. -/
def checkIntegerScaledGram
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (D : Matrix ι ι ℤ) (L : Matrix ι κ ℤ)
    (weight : κ → ℤ) (scale : ℤ) : Bool :=
  decide (
    0 < scale ∧
    (∀ k, 0 ≤ weight k) ∧
    ∀ i j, scale * D i j =
      ∑ k, L i k * weight k * L j k)

/-- Row-wise integer scaled-Gram checker. -/
def checkIntegerScaledGramRow
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (D : Matrix ι ι ℤ) (L : Matrix ι κ ℤ)
    (weight : κ → ℤ) (scale : ℤ) (i : ι) : Bool :=
  decide (
    0 < scale ∧
    (∀ k, 0 ≤ weight k) ∧
    ∀ j, scale * D i j =
      ∑ k, L i k * weight k * L j k)

theorem checkIntegerScaledGram_of_rows
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [Nonempty ι]
    (D : Matrix ι ι ℤ) (L : Matrix ι κ ℤ)
    (weight : κ → ℤ) (scale : ℤ)
    (hrows : ∀ i,
      checkIntegerScaledGramRow D L weight scale i = true) :
    checkIntegerScaledGram D L weight scale = true := by
  apply decide_eq_true
  have hbase :
      0 < scale ∧ (∀ k, 0 ≤ weight k) ∧
        ∀ j, scale * D (Classical.arbitrary ι) j =
          ∑ k, L (Classical.arbitrary ι) k * weight k * L j k :=
    of_decide_eq_true (by
      simpa only [checkIntegerScaledGramRow] using
        hrows (Classical.arbitrary ι))
  exact ⟨hbase.1, hbase.2.1, fun i j => by
    have hi :
        0 < scale ∧ (∀ k, 0 ≤ weight k) ∧
          ∀ j, scale * D i j =
            ∑ k, L i k * weight k * L j k :=
      of_decide_eq_true (by
        simpa only [checkIntegerScaledGramRow] using hrows i)
    exact hi.2.2 j⟩

/-- A checked integer scaled-Gram factorization yields the corresponding
rational LDLᵀ checker result. -/
theorem checkRationalLDLT_of_integer_scaled
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (D : Matrix ι ι ℤ) (L : Matrix ι κ ℤ)
    (weight : κ → ℤ) (scale : ℤ)
    (hcheck : checkIntegerScaledGram D L weight scale = true) :
    checkRationalLDLT
      (fun i j => (D i j : ℚ))
      (fun i k => (L i k : ℚ))
      (fun k => (weight k : ℚ) / (scale : ℚ)) = true := by
  have hdata :
      0 < scale ∧
      (∀ k, 0 ≤ weight k) ∧
      ∀ i j, scale * D i j =
        ∑ k, L i k * weight k * L j k :=
    of_decide_eq_true (by
      simpa only [checkIntegerScaledGram] using hcheck)
  rcases hdata with ⟨hscale, hweight, hfactor⟩
  apply decide_eq_true
  constructor
  · intro k
    exact div_nonneg (by exact_mod_cast hweight k)
      (by exact_mod_cast le_of_lt hscale)
  · intro i j
    have hscaleQ : (scale : ℚ) ≠ 0 := by
      exact_mod_cast ne_of_gt hscale
    calc
      (D i j : ℚ) =
          ((scale * D i j : ℤ) : ℚ) / (scale : ℚ) := by
        push_cast
        field_simp
      _ = ((∑ k, L i k * weight k * L j k : ℤ) : ℚ) /
          (scale : ℚ) := by rw [hfactor i j]
      _ = (∑ k, ((L i k * weight k * L j k : ℤ) : ℚ)) /
          (scale : ℚ) := by
        push_cast
        rfl
      _ = ∑ k, (L i k : ℚ) *
          ((weight k : ℚ) / (scale : ℚ)) * (L j k : ℚ) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro k _
        push_cast
        field_simp

theorem rationalQuadraticForm_nonnegative_of_ldlt
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (D : Matrix ι ι ℚ) (L : Matrix ι κ ℚ) (d : κ → ℚ)
    (hcheck : checkRationalLDLT D L d = true)
    (x : ι → ℚ) :
    0 ≤ rationalQuadraticForm D x := by
  have hdata := of_decide_eq_true (by
    simpa only [checkRationalLDLT] using hcheck)
  rcases hdata with ⟨hd, hfactor⟩
  have hrewrite :
      rationalQuadraticForm D x =
        ∑ k, d k * (∑ i, x i * L i k) ^ 2 := by
    simp only [rationalQuadraticForm, hfactor]
    calc
      (∑ i, ∑ j, x i * (∑ k, L i k * d k * L j k) * x j) =
          ∑ i, ∑ j, ∑ k,
            x i * (L i k * d k * L j k) * x j := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum, Finset.sum_mul]
      _ = ∑ i, ∑ k, ∑ j,
            x i * (L i k * d k * L j k) * x j := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = ∑ k, ∑ i, ∑ j,
            x i * (L i k * d k * L j k) * x j := by
        rw [Finset.sum_comm]
      _ = ∑ k, d k * (∑ i, x i * L i k) ^ 2 := by
        apply Finset.sum_congr rfl
        intro k _
        calc
          (∑ i, ∑ j, x i * (L i k * d k * L j k) * x j) =
              d k * ∑ i, ∑ j,
                (x i * L i k) * (x j * L j k) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
          _ = d k * ((∑ i, x i * L i k) *
              ∑ j, x j * L j k) := by
            apply congrArg (d k * ·)
            symm
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
          _ = d k * (∑ i, x i * L i k) ^ 2 := by
            rw [pow_two]
  rw [hrewrite]
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg (hd k) (sq_nonneg _)

end SRG266
