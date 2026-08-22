/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Hosts.A15PackingReduction
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# The coordinate support projector of an A15 shell realization

For a direct A15 realization, let `A` be the integral `16 × 220` matrix whose
columns are four times the oriented shell vectors.  This module proves
directly from the local Gram identity that

`Aᵀ A = 16 L`

and that

`(5 A Aᵀ - 2 d dᵀ) / 3600`

is the orthogonal projector onto the 12-dimensional support of the local Gram
configuration.  Subtracting it from the projector
`I - J / 16` onto the A15 ambient hyperplane gives a symmetric idempotent,
hence positive-semidefinite, rank-three complement projector.

This is the non-computational input to the later orbit-averaging bridge.
-/

open scoped BigOperators Matrix

namespace SRG266

set_option maxRecDepth 100000
set_option maxHeartbeats 0

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The integral matrix of four-times-shell coordinates. -/
def A15ShellGramRealization.factorMatrix
    {x : V} {d : Fin 16 → ℤ}
    (realization : A15ShellGramRealization G x d) :
    Matrix (Fin 16) (SecondSubconstituent G x) ℤ :=
  fun i B => a15ShellVector4 d (realization.shell B) i

/-- The coordinate matrix has the scaled local Gram matrix. -/
theorem A15ShellGramRealization.factorMatrix_gram
    {x : V} {d : Fin 16 → ℤ}
    (realization : A15ShellGramRealization G x d) :
    (realization.factorMatrix G).transpose *
        realization.factorMatrix G =
      (16 : ℕ) • localGramMatrix G x := by
  ext B C
  change
    integerDot
        (a15ShellVector4 d (realization.shell B))
        (a15ShellVector4 d (realization.shell C)) =
      16 * localGramMatrix G x B C
  rw [a15ShellVector4_dot_eq, realization.gram]

/-- The sum of the 16 coordinates of every four-subset shell vector is zero. -/
theorem a15ShellVector4_sum
    (d : Fin 16 → ℤ) (s : A15EligibleIndex d) :
    ∑ i, a15ShellVector4 d s i = 0 := by
  have hcard :
      (a15FourSubsetAsFinset s.1).card = 4 := by
    unfold a15FourSubsetAsFinset A15FourSubset.asFinset
    rw [List.toFinset_card_of_nodup
      (a15FourSubsetAt_coordinates_nodup s.1)]
    rfl
  have hindicator :
      (∑ i : Fin 16,
        if i ∈ a15FourSubsetAsFinset s.1 then (1 : ℤ) else 0) = 4 := by
    simp [hcard]
  have hraw :
      (∑ i : Fin 16,
        if i ∈ a15FourSubsetAsFinset s.1 then (-3 : ℤ) else 1) = 0 := by
    have huniv : (∑ _i : Fin 16, (1 : ℤ)) = 16 := by norm_num
    calc
      _ = ∑ i : Fin 16,
          ((1 : ℤ) -
            4 * if i ∈ a15FourSubsetAsFinset s.1 then (1 : ℤ) else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i ∈ a15FourSubsetAsFinset s.1 <;> simp [hi]
      _ = (∑ _i : Fin 16, (1 : ℤ)) -
          4 * ∑ i : Fin 16,
            if i ∈ a15FourSubsetAsFinset s.1 then (1 : ℤ) else 0 := by
        rw [Finset.sum_sub_distrib, Finset.mul_sum]
      _ = 0 := by rw [huniv, hindicator]; norm_num
  by_cases hs : a15SubsetSum d s.1 = 60
  · simp only [a15ShellVector4, a15ShellCoordinate4, hs, if_true]
    rw [Finset.sum_neg_distrib, hraw, neg_zero]
  · simpa [a15ShellVector4, a15ShellCoordinate4, hs] using hraw

/-- The centroid profile pairs to 240 with every four-times-shell vector. -/
theorem a15ShellVector4_pairing
    (d : Fin 16 → ℤ) (hdSum : ∑ i, d i = 0)
    (s : A15EligibleIndex d) :
    integerDot d (a15ShellVector4 d s) = 240 := by
  have hsubset :
      ∑ i ∈ a15FourSubsetAsFinset s.1, d i =
        a15SubsetSum d s.1 := by
    exact (a15FourSubset_valueSum_eq_finset_sum d s.1).symm
  have hraw :
      (∑ i : Fin 16,
        d i *
          (if i ∈ a15FourSubsetAsFinset s.1 then (-3 : ℤ) else 1)) =
        -4 * a15SubsetSum d s.1 := by
    calc
      _ = ∑ i : Fin 16,
          (d i -
            4 * if i ∈ a15FourSubsetAsFinset s.1 then d i else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i ∈ a15FourSubsetAsFinset s.1
        · simp [hi]
          ring
        · simp [hi]
      _ = (∑ i, d i) -
          4 * ∑ i,
            if i ∈ a15FourSubsetAsFinset s.1 then d i else 0 := by
        rw [Finset.sum_sub_distrib, Finset.mul_sum]
      _ = (∑ i, d i) -
          4 * (∑ i ∈ a15FourSubsetAsFinset s.1, d i) := by
        congr 1
        rw [← Finset.sum_filter]
        simp
      _ = -4 * (∑ i ∈ a15FourSubsetAsFinset s.1, d i) := by
        rw [hdSum]
        ring
      _ = -4 * a15SubsetSum d s.1 := by rw [hsubset]
  rcases s.2 with hneg | hpos
  · have hneg' : a15SubsetSum d s.1 = -60 := by
      simpa only [a15Eligible, a15DataEligible, a15SubsetSum] using hneg
    have hnot : a15SubsetSum d s.1 ≠ 60 := by omega
    unfold integerDot
    simp only [a15ShellVector4, a15ShellCoordinate4, hnot, if_false]
    rw [hraw, hneg']
    norm_num
  · have hpos' : a15SubsetSum d s.1 = 60 := by
      simpa only [a15Eligible, a15DataEligible, a15SubsetSum] using hpos
    unfold integerDot
    simp only [a15ShellVector4, a15ShellCoordinate4, hpos', if_true]
    calc
      (∑ i, d i *
        -(if i ∈ a15FourSubsetAsFinset s.1 then (-3 : ℤ) else 1)) =
          -(∑ i, d i *
            (if i ∈ a15FourSubsetAsFinset s.1 then (-3 : ℤ) else 1)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 240 := by rw [hraw, hpos']; norm_num

/-- The row sums of the factor matrix are the scaled centroid equations. -/
theorem A15ShellGramRealization.factorMatrix_row_sum
    {x : V} {d : Fin 16 → ℤ}
    (realization : A15ShellGramRealization G x d) (i : Fin 16) :
    ∑ B, realization.factorMatrix G i B = 11 * d i :=
  realization.centroid i

/-- The coordinate columns lie in the A15 sum-zero hyperplane. -/
theorem A15ShellGramRealization.factorMatrix_column_sum
    {x : V} {d : Fin 16 → ℤ}
    (realization : A15ShellGramRealization G x d)
    (B : SecondSubconstituent G x) :
    ∑ i, realization.factorMatrix G i B = 0 :=
  a15ShellVector4_sum d (realization.shell B)

/-- If the centroid coordinates sum to zero, each factor column pairs to
240 with the integral centroid vector. -/
theorem A15ShellGramRealization.factorMatrix_pairing
    {x : V} {d : Fin 16 → ℤ}
    (realization : A15ShellGramRealization G x d)
    (hdSum : ∑ i, d i = 0)
    (B : SecondSubconstituent G x) :
    ∑ i, d i * realization.factorMatrix G i B = 240 :=
  a15ShellVector4_pairing d hdSum (realization.shell B)

/-- The direct shell equations force the squared norm of the integral
centroid profile to be 4800. -/
theorem A15ShellGramRealization.centroid_norm
    (hG : IsHypothetical G) (x : V) {d : Fin 16 → ℤ}
    (realization : A15ShellGramRealization G x d)
    (hdSum : ∑ i, d i = 0) :
    ∑ i, d i * d i = 4800 := by
  have htotal :
      11 * (∑ i, d i * d i) = 52800 := by
    calc
      11 * (∑ i, d i * d i) =
          ∑ i, d i * (11 * d i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = ∑ i, d i *
          (∑ B, realization.factorMatrix G i B) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [realization.factorMatrix_row_sum G]
      _ = ∑ B, ∑ i,
          d i * realization.factorMatrix G i B := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
      _ = ∑ _B : SecondSubconstituent G x, (240 : ℤ) := by
        apply Finset.sum_congr rfl
        intro B _
        rw [realization.factorMatrix_pairing G hdSum]
      _ = 52800 := by
        simp [secondSubconstituent_card G hG x]
  omega

/-- The scaled coordinate factor satisfies the same local frame relation as
an unscaled Gram factor:

`A L = 45 A + 6 d 1ᵀ`.
-/
theorem A15ShellGramRealization.factorMatrix_mul_localGramMatrix
    (hG : IsHypothetical G) (x : V) {d : Fin 16 → ℤ}
    (realization : A15ShellGramRealization G x d) :
    realization.factorMatrix G * localGramMatrix G x =
      (45 : ℕ) • realization.factorMatrix G +
        (6 : ℕ) • Matrix.vecMulVec d
          (1 : SecondSubconstituent G x → ℤ) := by
  let A := realization.factorMatrix G
  have hgram :
      A.transpose * A = (16 : ℕ) • localGramMatrix G x := by
    exact realization.factorMatrix_gram G
  ext i B
  let q : SecondSubconstituent G x → ℤ :=
    fun C =>
      11 * localGramMatrix G x C B -
        495 * (if C = B then 1 else 0) - 6
  have hLq : localGramMatrix G x *ᵥ q = 0 := by
    funext D
    have hsq := localGramMatrix_sq_apply G hG x D B
    have hrow := localGramMatrix_row_sum G hG x D
    change
      ∑ C, localGramMatrix G x D C *
        (11 * localGramMatrix G x C B -
          495 * (if C = B then 1 else 0) - 6) = 0
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    have hfirst :
        (∑ C, localGramMatrix G x D C *
          (11 * localGramMatrix G x C B)) =
          11 * (45 * localGramMatrix G x D B + 90) := by
      calc
        _ = 11 * ∑ C,
            localGramMatrix G x D C *
              localGramMatrix G x C B := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro C _
          ring
        _ = _ := by
          rw [← Matrix.mul_apply, hsq]
    have hdelta :
        (∑ C, localGramMatrix G x D C *
          (495 * (if C = B then 1 else 0))) =
          495 * localGramMatrix G x D B := by
      calc
        _ = 495 * ∑ C,
            localGramMatrix G x D C *
              (if C = B then 1 else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro C _
          ring
        _ = _ := by simp
    have hconstant :
        (∑ C, localGramMatrix G x D C * 6) = 990 := by
      rw [← Finset.sum_mul, hrow]
      norm_num
    rw [hfirst, hdelta, hconstant]
    ring
  have hgramq :
      (A.transpose * A) *ᵥ q = 0 := by
    rw [hgram]
    funext D
    change
      (∑ C, (16 * localGramMatrix G x D C) * q C) = 0
    calc
      _ = 16 * ∑ C, localGramMatrix G x D C * q C := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro C _
        ring
      _ = 16 * (localGramMatrix G x *ᵥ q) D := by
        rfl
      _ = 0 := by rw [hLq]; norm_num
  have hAq : A *ᵥ q = 0 :=
    factor_mulVec_eq_zero_of_gram_mulVec_eq_zero A q hgramq
  have hi := congrFun hAq i
  change
    ∑ C, A i C *
      (11 * localGramMatrix G x C B -
        495 * (if C = B then 1 else 0) - 6) = 0 at hi
  have hrow := realization.factorMatrix_row_sum G i
  change
    (A * localGramMatrix G x) i B =
      ((45 : ℕ) • A +
        (6 : ℕ) • Matrix.vecMulVec d
          (1 : SecondSubconstituent G x → ℤ)) i B
  simp only [Matrix.add_apply, nsmulMatrix_apply,
    Matrix.vecMulVec_apply, Pi.one_apply, mul_one]
  change
    (∑ C, A i C * localGramMatrix G x C B) =
      45 * A i B + 6 * d i
  have hdelta :
      (∑ C, A i C *
        (495 * (if C = B then 1 else 0))) = 495 * A i B := by
    calc
      _ = 495 * ∑ C, A i C * (if C = B then 1 else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro C _
        ring
      _ = _ := by simp
  have hfirst :
      (∑ C, A i C * (11 * localGramMatrix G x C B)) =
        11 * ∑ C, A i C * localGramMatrix G x C B := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro C _
    ring
  have hconstant :
      (∑ C, A i C * 6) = 66 * d i := by
    rw [← Finset.sum_mul, hrow]
    ring
  simp_rw [mul_sub] at hi
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    hfirst, hdelta, hconstant] at hi
  omega

/-- The integral row-frame matrix `A Aᵀ`. -/
def A15ShellGramRealization.frame
    {x : V} {d : Fin 16 → ℤ}
    (realization : A15ShellGramRealization G x d) :
    Matrix (Fin 16) (Fin 16) ℤ :=
  factorFrame (realization.factorMatrix G)

/-- The rank-one centroid matrix `d dᵀ`. -/
def a15CentroidOuter (d : Fin 16 → ℤ) :
    Matrix (Fin 16) (Fin 16) ℤ :=
  Matrix.vecMulVec d d

/-- The scaled A15 frame identity. -/
theorem A15ShellGramRealization.frame_sq
    (hG : IsHypothetical G) (x : V) {d : Fin 16 → ℤ}
    (realization : A15ShellGramRealization G x d) :
    realization.frame G * realization.frame G =
      (720 : ℕ) • realization.frame G +
        (1056 : ℕ) • a15CentroidOuter d := by
  let A := realization.factorMatrix G
  have hgram :
      A.transpose * A = (16 : ℕ) • localGramMatrix G x := by
    exact realization.factorMatrix_gram G
  calc
    realization.frame G * realization.frame G =
        (A * (A.transpose * A)) * A.transpose := by
      simp [A15ShellGramRealization.frame, factorFrame, A,
        Matrix.mul_assoc]
    _ = (A * ((16 : ℕ) • localGramMatrix G x)) * A.transpose := by
      rw [hgram]
    _ = (16 : ℕ) •
        ((A * localGramMatrix G x) * A.transpose) := by
      ext i j
      simp only [Matrix.mul_apply, nsmulMatrix_apply]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro B _
      change
        (∑ C, A i C * (16 * localGramMatrix G x C B)) *
            A j B =
          16 * ((∑ C, A i C * localGramMatrix G x C B) * A j B)
      have hsum :
          (∑ C, A i C * (16 * localGramMatrix G x C B)) =
            16 * ∑ C, A i C * localGramMatrix G x C B := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro C _
        ring
      rw [hsum]
      ring
    _ = (720 : ℕ) • realization.frame G +
        (1056 : ℕ) • a15CentroidOuter d := by
      rw [realization.factorMatrix_mul_localGramMatrix G hG x]
      ext i j
      simp only [Matrix.mul_apply, Matrix.add_apply, nsmulMatrix_apply,
        Matrix.vecMulVec_apply, Pi.one_apply, mul_one,
        A15ShellGramRealization.frame, factorFrame,
        a15CentroidOuter, Matrix.transpose_apply]
      change
        16 * (∑ B, (45 * A i B + 6 * d i) * A j B) =
          720 * (∑ B, A i B * A j B) + 1056 * (d i * d j)
      have hrow := realization.factorMatrix_row_sum G j
      calc
        16 * (∑ B, (45 * A i B + 6 * d i) * A j B) =
            16 * ((∑ B, 45 * (A i B * A j B)) +
              ∑ B, (6 * d i) * A j B) := by
          congr 1
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro B _
          ring
        _ = 16 * (45 * ∑ B, A i B * A j B +
              6 * d i * ∑ B, A j B) := by
          rw [Finset.mul_sum, Finset.mul_sum]
        _ = _ := by rw [hrow]; ring

/-- The frame sends the centroid vector to `2640 d`. -/
theorem A15ShellGramRealization.frame_mulVec_centroid
    (x : V) {d : Fin 16 → ℤ}
    (realization : A15ShellGramRealization G x d)
    (hdSum : ∑ i, d i = 0) :
    realization.frame G *ᵥ d = fun i => 2640 * d i := by
  let A := realization.factorMatrix G
  calc
    realization.frame G *ᵥ d =
        A *ᵥ (A.transpose *ᵥ d) := by
      change (A * A.transpose) *ᵥ d =
        A *ᵥ (A.transpose *ᵥ d)
      rw [← Matrix.mulVec_mulVec]
    _ = A *ᵥ (fun _ => (240 : ℤ)) := by
      congr 1
      funext B
      change ∑ i, A i B * d i = 240
      calc
        _ = ∑ i, d i * A i B := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = 240 := realization.factorMatrix_pairing G hdSum B
    _ = fun i => 2640 * d i := by
      funext i
      change (∑ B, A i B * 240) = 2640 * d i
      rw [← Finset.sum_mul, realization.factorMatrix_row_sum G]
      ring

/-- The frame and centroid outer product multiply to `2640 d dᵀ`. -/
theorem A15ShellGramRealization.frame_mul_centroidOuter
    (x : V) {d : Fin 16 → ℤ}
    (realization : A15ShellGramRealization G x d)
    (hdSum : ∑ i, d i = 0) :
    realization.frame G * a15CentroidOuter d =
      (2640 : ℕ) • a15CentroidOuter d := by
  ext i j
  change
    (∑ k, realization.frame G i k * (d k * d j)) =
      2640 * (d i * d j)
  calc
    _ = (∑ k, realization.frame G i k * d k) * d j := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by
      change (realization.frame G *ᵥ d) i * d j = _
      rw [realization.frame_mulVec_centroid G x hdSum]
      ring

/-- The reverse frame/centroid product has the same value. -/
theorem A15ShellGramRealization.centroidOuter_mul_frame
    (x : V) {d : Fin 16 → ℤ}
    (realization : A15ShellGramRealization G x d)
    (hdSum : ∑ i, d i = 0) :
    a15CentroidOuter d * realization.frame G =
      (2640 : ℕ) • a15CentroidOuter d := by
  have hframeSymm : (realization.frame G).IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    simp [A15ShellGramRealization.frame, factorFrame,
      Matrix.mul_apply, mul_comm]
  ext i j
  change
    (∑ k, (d i * d k) * realization.frame G k j) =
      2640 * (d i * d j)
  calc
    _ = d i * ∑ k, realization.frame G j k * d k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [hframeSymm.apply k j]
      ring
    _ = _ := by
      change d i * (realization.frame G *ᵥ d) j = _
      rw [realization.frame_mulVec_centroid G x hdSum]
      ring

/-- The centroid outer product squares to `4800 d dᵀ`. -/
theorem A15ShellGramRealization.centroidOuter_sq
    (hG : IsHypothetical G) (x : V) {d : Fin 16 → ℤ}
    (realization : A15ShellGramRealization G x d)
    (hdSum : ∑ i, d i = 0) :
    a15CentroidOuter d * a15CentroidOuter d =
      (4800 : ℕ) • a15CentroidOuter d := by
  have hnorm := realization.centroid_norm G hG x hdSum
  ext i j
  change
    (∑ k, (d i * d k) * (d k * d j)) =
      4800 * (d i * d j)
  calc
    _ = d i * (∑ k, d k * d k) * d j := by
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by rw [hnorm]; ring

/-- The integral numerator of the A15 support projector. -/
def A15ShellGramRealization.supportNumerator
    {x : V} {d : Fin 16 → ℤ}
    (realization : A15ShellGramRealization G x d) :
    Matrix (Fin 16) (Fin 16) ℤ :=
  (5 : ℕ) • realization.frame G -
    (2 : ℕ) • a15CentroidOuter d

/-- The support numerator squares to 3600 times itself. -/
theorem A15ShellGramRealization.supportNumerator_sq
    (hG : IsHypothetical G) (x : V) {d : Fin 16 → ℤ}
    (realization : A15ShellGramRealization G x d)
    (hdSum : ∑ i, d i = 0) :
    realization.supportNumerator G * realization.supportNumerator G =
      (3600 : ℕ) • realization.supportNumerator G := by
  let F := realization.frame G
  let C := a15CentroidOuter d
  have hFF : F * F = (720 : ℕ) • F + (1056 : ℕ) • C := by
    simpa [F, C] using realization.frame_sq G hG x
  have hFC : F * C = (2640 : ℕ) • C := by
    simpa [F, C] using
      realization.frame_mul_centroidOuter G x hdSum
  have hCF : C * F = (2640 : ℕ) • C := by
    simpa [F, C] using
      realization.centroidOuter_mul_frame G x hdSum
  have hCC : C * C = (4800 : ℕ) • C := by
    simpa [C] using realization.centroidOuter_sq G hG x hdSum
  change
    ((5 : ℕ) • F - (2 : ℕ) • C) *
        ((5 : ℕ) • F - (2 : ℕ) • C) =
      (3600 : ℕ) • ((5 : ℕ) • F - (2 : ℕ) • C)
  noncomm_ring [hFF, hFC, hCF, hCC]

/-- The rational projector onto the support of the local Gram vectors. -/
noncomputable def A15ShellGramRealization.supportProjector
    {x : V} {d : Fin 16 → ℤ}
    (realization : A15ShellGramRealization G x d) :
    Matrix (Fin 16) (Fin 16) ℚ :=
  fun i j => (realization.supportNumerator G i j : ℚ) / 3600

/-- The A15 support projector is idempotent. -/
theorem A15ShellGramRealization.supportProjector_idempotent
    (hG : IsHypothetical G) (x : V) {d : Fin 16 → ℤ}
    (realization : A15ShellGramRealization G x d)
    (hdSum : ∑ i, d i = 0) :
    realization.supportProjector G * realization.supportProjector G =
      realization.supportProjector G := by
  ext i j
  rw [Matrix.mul_apply]
  have hcast :
      (∑ k,
        (realization.supportNumerator G i k : ℚ) *
          (realization.supportNumerator G k j : ℚ)) =
        ((realization.supportNumerator G *
          realization.supportNumerator G) i j : ℤ) := by
    rw [Matrix.mul_apply]
    norm_cast
  change
    (∑ k,
      (realization.supportNumerator G i k : ℚ) / 3600 *
        ((realization.supportNumerator G k j : ℚ) / 3600)) =
      (realization.supportNumerator G i j : ℚ) / 3600
  calc
    _ = (∑ k,
        (realization.supportNumerator G i k : ℚ) *
          (realization.supportNumerator G k j : ℚ)) / 12960000 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = ((realization.supportNumerator G *
          realization.supportNumerator G) i j : ℤ) / 12960000 := by
      rw [hcast]
    _ = (realization.supportNumerator G i j : ℚ) / 3600 := by
      have hsq := congrFun (congrFun
        (realization.supportNumerator_sq G hG x hdSum) i) j
      change
        (realization.supportNumerator G *
          realization.supportNumerator G) i j =
          3600 * realization.supportNumerator G i j at hsq
      rw [hsq]
      push_cast
      ring

/-- The A15 support projector is symmetric. -/
theorem A15ShellGramRealization.supportProjector_isSymm
    {x : V} {d : Fin 16 → ℤ}
    (realization : A15ShellGramRealization G x d) :
    (realization.supportProjector G).IsSymm := by
  have hF : (realization.frame G).IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    simp [A15ShellGramRealization.frame, factorFrame,
      Matrix.mul_apply, mul_comm]
  have hC : (a15CentroidOuter d).IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    simp [a15CentroidOuter, Matrix.vecMulVec_apply, mul_comm]
  have hN : (realization.supportNumerator G).IsSymm :=
    (hF.smul (5 : ℕ)).sub (hC.smul (2 : ℕ))
  apply Matrix.IsSymm.ext
  intro i j
  change
    (realization.supportNumerator G j i : ℚ) / 3600 =
      (realization.supportNumerator G i j : ℚ) / 3600
  rw [hN.apply i j]

/-- Every column of the integral support numerator has coordinate sum zero. -/
theorem A15ShellGramRealization.supportNumerator_column_sum
    {x : V} {d : Fin 16 → ℤ}
    (realization : A15ShellGramRealization G x d)
    (hdSum : ∑ i, d i = 0) (j : Fin 16) :
    ∑ i, realization.supportNumerator G i j = 0 := by
  let A := realization.factorMatrix G
  have hframe :
      ∑ i, realization.frame G i j = 0 := by
    change ∑ i, ∑ B, A i B * A j B = 0
    calc
      _ = ∑ B, (∑ i, A i B) * A j B := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro B _
        rw [Finset.sum_mul]
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro B _
        rw [realization.factorMatrix_column_sum G]
        norm_num
  have hcentroid :
      ∑ i, a15CentroidOuter d i j = 0 := by
    change ∑ i, d i * d j = 0
    rw [← Finset.sum_mul, hdSum, zero_mul]
  simp only [A15ShellGramRealization.supportNumerator,
    Matrix.sub_apply, nsmulMatrix_apply]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    hframe, hcentroid]
  norm_num

/-- Every row of the rational support projector has sum zero. -/
theorem A15ShellGramRealization.supportProjector_row_sum
    {x : V} {d : Fin 16 → ℤ}
    (realization : A15ShellGramRealization G x d)
    (hdSum : ∑ i, d i = 0) (i : Fin 16) :
    ∑ j, realization.supportProjector G i j = 0 := by
  have hsymm := realization.supportProjector_isSymm G
  calc
    _ = ∑ j, realization.supportProjector G j i := by
      apply Finset.sum_congr rfl
      intro j _
      exact (hsymm.apply i j).symm
    _ = (∑ j, (realization.supportNumerator G j i : ℚ)) / 3600 := by
      simp only [A15ShellGramRealization.supportProjector]
      rw [Finset.sum_div]
    _ = 0 := by
      have hzero :=
        realization.supportNumerator_column_sum G hdSum i
      have hzeroQ :
          (∑ j, (realization.supportNumerator G j i : ℚ)) = 0 := by
        exact_mod_cast hzero
      rw [hzeroQ]
      norm_num

/-- Every column of the rational support projector has sum zero. -/
theorem A15ShellGramRealization.supportProjector_column_sum
    {x : V} {d : Fin 16 → ℤ}
    (realization : A15ShellGramRealization G x d)
    (hdSum : ∑ i, d i = 0) (j : Fin 16) :
    ∑ i, realization.supportProjector G i j = 0 := by
  calc
    _ = (∑ i, (realization.supportNumerator G i j : ℚ)) / 3600 := by
      simp only [A15ShellGramRealization.supportProjector]
      rw [Finset.sum_div]
    _ = 0 := by
      have hzero :=
        realization.supportNumerator_column_sum G hdSum j
      have hzeroQ :
          (∑ i, (realization.supportNumerator G i j : ℚ)) = 0 := by
        exact_mod_cast hzero
      rw [hzeroQ]
      norm_num

/-- The orthogonal projector onto the A15 coordinate hyperplane. -/
def a15AmbientProjector : Matrix (Fin 16) (Fin 16) ℚ :=
  fun i j => (if i = j then 1 else 0) - 1 / 16

theorem a15AmbientProjector_isSymm :
    a15AmbientProjector.IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp only [a15AmbientProjector, eq_comm]

theorem a15AmbientProjector_idempotent :
    a15AmbientProjector * a15AmbientProjector =
      a15AmbientProjector := by
  let J : Matrix (Fin 16) (Fin 16) ℚ := fun _ _ => 1
  have hdef :
      a15AmbientProjector = 1 - (1 / 16 : ℚ) • J := by
    ext i j
    by_cases hij : i = j <;>
      simp [a15AmbientProjector, J, hij]
  have hJJ : J * J = (16 : ℚ) • J := by
    ext i j
    simp [Matrix.mul_apply, J]
  have hscaled :
      ((1 / 16 : ℚ) • J) * ((1 / 16 : ℚ) • J) =
        (1 / 16 : ℚ) • J := by
    calc
      _ = ((1 / 16 : ℚ) * (1 / 16 : ℚ)) • (J * J) :=
        smul_mul_smul_comm _ _ _ _
      _ = (1 / 16 : ℚ) • J := by
        rw [hJJ, smul_smul]
        norm_num
  rw [hdef]
  simp only [sub_mul, mul_sub, one_mul, mul_one, hscaled]
  abel

/-- The ambient hyperplane projector acts identically on the support
projector. -/
theorem A15ShellGramRealization.ambient_mul_supportProjector
    {x : V} {d : Fin 16 → ℤ}
    (realization : A15ShellGramRealization G x d)
    (hdSum : ∑ i, d i = 0) :
    a15AmbientProjector * realization.supportProjector G =
      realization.supportProjector G := by
  ext i j
  rw [Matrix.mul_apply]
  change
    (∑ k,
      ((if i = k then (1 : ℚ) else 0) - 1 / 16) *
        realization.supportProjector G k j) =
      realization.supportProjector G i j
  calc
    _ = (∑ k,
        (if i = k then (1 : ℚ) else 0) *
          realization.supportProjector G k j) -
        (1 / 16) *
          ∑ k, realization.supportProjector G k j := by
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = _ := by
      rw [realization.supportProjector_column_sum G hdSum]
      simp

/-- The support projector also acts trivially through the ambient
hyperplane projector on the right. -/
theorem A15ShellGramRealization.supportProjector_mul_ambient
    {x : V} {d : Fin 16 → ℤ}
    (realization : A15ShellGramRealization G x d)
    (hdSum : ∑ i, d i = 0) :
    realization.supportProjector G * a15AmbientProjector =
      realization.supportProjector G := by
  ext i j
  rw [Matrix.mul_apply]
  change
    (∑ k,
      realization.supportProjector G i k *
        ((if k = j then (1 : ℚ) else 0) - 1 / 16)) =
      realization.supportProjector G i j
  calc
    _ = (∑ k,
        realization.supportProjector G i k *
          (if k = j then (1 : ℚ) else 0)) -
        (∑ k, realization.supportProjector G i k) * (1 / 16) := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, Finset.sum_mul]
    _ = _ := by
      rw [realization.supportProjector_row_sum G hdSum]
      simp

/-- The rank-three complement projector before orbit averaging. -/
noncomputable def A15ShellGramRealization.complementProjector
    {x : V} {d : Fin 16 → ℤ}
    (realization : A15ShellGramRealization G x d) :
    Matrix (Fin 16) (Fin 16) ℚ :=
  a15AmbientProjector - realization.supportProjector G

theorem A15ShellGramRealization.complementProjector_isSymm
    {x : V} {d : Fin 16 → ℤ}
    (realization : A15ShellGramRealization G x d) :
    (realization.complementProjector G).IsSymm :=
  a15AmbientProjector_isSymm.sub
    (realization.supportProjector_isSymm G)

theorem A15ShellGramRealization.complementProjector_idempotent
    (hG : IsHypothetical G) (x : V) {d : Fin 16 → ℤ}
    (realization : A15ShellGramRealization G x d)
    (hdSum : ∑ i, d i = 0) :
    realization.complementProjector G *
        realization.complementProjector G =
      realization.complementProjector G := by
  have hU := a15AmbientProjector_idempotent
  have hP :=
    realization.supportProjector_idempotent G hG x hdSum
  have hUP :=
    realization.ambient_mul_supportProjector G hdSum
  have hPU :=
    realization.supportProjector_mul_ambient G hdSum
  change
    (a15AmbientProjector - realization.supportProjector G) *
        (a15AmbientProjector - realization.supportProjector G) =
      a15AmbientProjector - realization.supportProjector G
  noncomm_ring [hU, hP, hUP, hPU]

/-- A symmetric idempotent rational matrix is positive semidefinite. -/
theorem rationalMatrix_posSemidef_of_isSymm_idempotent
    {n : Type*} [Fintype n]
    (P : Matrix n n ℚ) (hsymm : P.IsSymm)
    (hidempotent : P * P = P) :
    P.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · simpa only [Matrix.isHermitian_iff_isSymm] using hsymm
  · intro x
    simp only [star_trivial]
    rw [← hidempotent, ← Matrix.mulVec_mulVec]
    calc
      x ⬝ᵥ (P *ᵥ (P *ᵥ x)) =
          x ⬝ᵥ (P.transpose *ᵥ (P *ᵥ x)) := by
        rw [hsymm.eq]
      _ = (P *ᵥ x) ⬝ᵥ (P *ᵥ x) :=
        Matrix.dotProduct_transpose_mulVec P x (P *ᵥ x)
      _ ≥ 0 := by
        unfold dotProduct
        exact Finset.sum_nonneg fun i _ =>
          mul_self_nonneg ((P *ᵥ x) i)

/-- The direct A15 complement projector is positive semidefinite. -/
theorem A15ShellGramRealization.complementProjector_posSemidef
    (hG : IsHypothetical G) (x : V) {d : Fin 16 → ℤ}
    (realization : A15ShellGramRealization G x d)
    (hdSum : ∑ i, d i = 0) :
    (realization.complementProjector G).PosSemidef :=
  rationalMatrix_posSemidef_of_isSymm_idempotent
    (realization.complementProjector G)
    (realization.complementProjector_isSymm G)
    (realization.complementProjector_idempotent G hG x hdSum)

end SRG266
