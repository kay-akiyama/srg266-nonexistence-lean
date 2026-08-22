/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.KernelReduction
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# The one-integrability obstruction

This file begins the native reduction from a one-integral factorization of the
local Gram matrix to the forbidden coclique configuration.

The first layer is independent of the later frame-operator argument.  It
defines one-integrability, proves that every column in an integral
factorization has exactly three non-zero entries and that those entries are
signs, and isolates the integer inequality forcing every centroid coordinate
to have absolute value at most five.
-/

open scoped Matrix

namespace SRG266

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A matrix is one-integrable when it is the Gram matrix of finitely many
integral coordinate vectors. -/
def Matrix.IsOneIntegrable
    {ι : Type*} [Fintype ι] (L : Matrix ι ι ℤ) : Prop :=
  ∃ n : ℕ, ∃ W : Matrix (Fin n) ι ℤ, W.transpose * W = L

/-- One-integrability of the local Gram matrix. -/
abbrev LocalGramIsOneIntegrable (x : V) : Prop :=
  Matrix.IsOneIntegrable (localGramMatrix G x)

/-- The support of a column of an integral factorization. -/
def factorColumnSupport
    {ι : Type*} [Fintype ι] {n : ℕ}
    (W : Matrix (Fin n) ι ℤ) (B : ι) : Finset (Fin n) :=
  Finset.univ.filter fun j => W j B ≠ 0

theorem factor_column_sq_sum_eq_three
    (hG : IsHypothetical G) (x : V)
    {n : ℕ}
    (W : Matrix (Fin n) (SecondSubconstituent G x) ℤ)
    (hW : W.transpose * W = localGramMatrix G x)
    (B : SecondSubconstituent G x) :
    ∑ j, W j B * W j B = 3 := by
  have h := congrFun (congrFun hW B) B
  rw [localGramMatrix_diagonal G hG x B] at h
  simpa [Matrix.mul_apply] using h

theorem factor_column_entry_cases
    (hG : IsHypothetical G) (x : V)
    {n : ℕ}
    (W : Matrix (Fin n) (SecondSubconstituent G x) ℤ)
    (hW : W.transpose * W = localGramMatrix G x)
    (B : SecondSubconstituent G x) (j : Fin n) :
    W j B = -1 ∨ W j B = 0 ∨ W j B = 1 := by
  have hsum :=
    factor_column_sq_sum_eq_three G hG x W hW B
  have hle :
      W j B * W j B ≤ ∑ k, W k B * W k B := by
    exact Finset.single_le_sum
      (fun k _ => mul_self_nonneg (W k B))
      (Finset.mem_univ j)
  rw [hsum] at hle
  have hlower : -2 < W j B := by nlinarith
  have hupper : W j B < 2 := by nlinarith
  omega

theorem factor_column_support_card
    (hG : IsHypothetical G) (x : V)
    {n : ℕ}
    (W : Matrix (Fin n) (SecondSubconstituent G x) ℤ)
    (hW : W.transpose * W = localGramMatrix G x)
    (B : SecondSubconstituent G x) :
    (factorColumnSupport W B).card = 3 := by
  have hsum :=
    factor_column_sq_sum_eq_three G hG x W hW B
  have hsquares :
      (∑ j, W j B * W j B) =
        ∑ j, if W j B ≠ 0 then (1 : ℤ) else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    rcases factor_column_entry_cases G hG x W hW B j with
      hneg | hzero | hone
    · simp [hneg]
    · simp [hzero]
    · simp [hone]
  have hcard :
      (∑ j, if W j B ≠ 0 then (1 : ℤ) else 0) =
        ((factorColumnSupport W B).card : ℤ) := by
    simpa [factorColumnSupport] using
      (Finset.sum_boole
        (R := ℤ) (fun j : Fin n => W j B ≠ 0) Finset.univ)
  have hcard' : ((factorColumnSupport W B).card : ℤ) = 3 := by
    omega
  exact_mod_cast hcard'

/-- A vector killed by `WᵀW` is already killed by `W`, over the integers. -/
theorem factor_mulVec_eq_zero_of_gram_mulVec_eq_zero
    {ι : Type*} [Fintype ι] {n : ℕ}
    (W : Matrix (Fin n) ι ℤ) (z : ι → ℤ)
    (hz : (W.transpose * W) *ᵥ z = 0) :
    W *ᵥ z = 0 := by
  rw [← Matrix.mulVec_mulVec] at hz
  replace hz := congrArg (dotProduct z) hz
  rwa [Matrix.dotProduct_mulVec, dotProduct_zero,
    Matrix.vecMul_transpose, dotProduct_self_eq_zero] at hz

/-- The set of columns using a fixed coordinate of an integral
factorization. -/
def factorRowSupport
    {ι : Type*} [Fintype ι] {n : ℕ}
    (W : Matrix (Fin n) ι ℤ) (j : Fin n) : Finset ι :=
  Finset.univ.filter fun B => W j B ≠ 0

/-- Exact centroid data inside an integral Gram factorization. -/
structure FactorCentroidData
    (x : V) {n : ℕ}
    (W : Matrix (Fin n) (SecondSubconstituent G x) ℤ) where
  /-- Coordinates of the integral centroid. -/
  c : Fin n → ℤ
  /-- The centroid lies in the span of the factor columns. -/
  span_witness :
    ∃ a : SecondSubconstituent G x → ℤ, c = W *ᵥ a
  /-- The sum of every factor row is eleven times its centroid coordinate. -/
  row_sum : ∀ j, ∑ B, W j B = 11 * c j
  /-- The centroid pairs to 15 with every Gram vector. -/
  pairing : ∀ B, ∑ j, c j * W j B = 15
  /-- The centroid has squared norm 300. -/
  norm : ∑ j, c j * c j = 300

theorem exists_factorCentroidData
    (hG : IsHypothetical G) (x : V)
    {n : ℕ}
    (W : Matrix (Fin n) (SecondSubconstituent G x) ℤ)
    (hW : W.transpose * W = localGramMatrix G x) :
    Nonempty (FactorCentroidData G x W) := by
  obtain ⟨z, hzRelation, hzMod⟩ := hasMod11KernelLift G hG x
  choose a ha using hzMod
  have hone :
      (1 : SecondSubconstituent G x → ℤ) =
        z + (11 : ℤ) • a := by
    funext B
    have hB := ha B
    change 1 = z B + 11 * a B
    omega
  have hzKernel :
      localGramMatrix G x *ᵥ z = 0 := by
    have hzMem : z ∈ integralGramKernel G x := by
      rw [integralGramKernel_eq_relations G x]
      exact hzRelation
    exact LinearMap.mem_ker.mp hzMem
  have hWz : W *ᵥ z = 0 := by
    apply factor_mulVec_eq_zero_of_gram_mulVec_eq_zero W z
    rw [hW]
    exact hzKernel
  let c : Fin n → ℤ := W *ᵥ a
  have hrow : ∀ j, ∑ B, W j B = 11 * c j := by
    intro j
    have h := congrArg (fun u => (W *ᵥ u) j) hone
    calc
      (∑ B, W j B) = (W *ᵥ (1 :
          SecondSubconstituent G x → ℤ)) j := by
        simp [Matrix.mulVec_apply, dotProduct]
      _ = (W *ᵥ (z + (11 : ℤ) • a)) j := h
      _ = (W *ᵥ z) j + 11 * (W *ᵥ a) j := by
        rw [Matrix.mulVec_add, Matrix.mulVec_smul]
        rfl
      _ = 11 * c j := by simp [hWz, c]
  have hLa :
      localGramMatrix G x *ᵥ a =
        fun _ => (15 : ℤ) := by
    funext B
    have h := congrArg (fun u => (localGramMatrix G x *ᵥ u) B) hone
    have hLone :=
      congrFun (localGramMatrix_mulVec_one G hG x) B
    rw [Matrix.mulVec_add, Matrix.mulVec_smul] at h
    change
      (localGramMatrix G x *ᵥ
          (1 : SecondSubconstituent G x → ℤ)) B =
        (localGramMatrix G x *ᵥ z) B +
          11 * (localGramMatrix G x *ᵥ a) B at h
    rw [hLone, hzKernel] at h
    have hscalar :
        165 = 11 * (localGramMatrix G x *ᵥ a) B := by
      simpa using h
    change (localGramMatrix G x *ᵥ a) B = 15
    omega
  have hpair : ∀ B, ∑ j, c j * W j B = 15 := by
    intro B
    have hmul :
        W.transpose *ᵥ c =
          localGramMatrix G x *ᵥ a := by
      change W.transpose *ᵥ (W *ᵥ a) =
        localGramMatrix G x *ᵥ a
      rw [Matrix.mulVec_mulVec, hW]
    have hB := congrFun hmul B
    rw [hLa] at hB
    simpa [Matrix.mulVec_apply, dotProduct, c, mul_comm] using hB
  have hnorm : ∑ j, c j * c j = 300 := by
    have htotal :
        11 * (∑ j, c j * c j) = 3300 := by
      calc
        11 * (∑ j, c j * c j) =
            ∑ j, c j * (11 * c j) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = ∑ j, c j * (∑ B, W j B) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [hrow]
        _ = ∑ B, ∑ j, c j * W j B := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum]
        _ = ∑ _B : SecondSubconstituent G x, (15 : ℤ) := by
          apply Finset.sum_congr rfl
          intro B _
          rw [hpair]
        _ = 3300 := by
          simp [secondSubconstituent_card G hG x]
    omega
  exact ⟨⟨c, ⟨a, rfl⟩, hrow, hpair, hnorm⟩⟩

theorem FactorCentroidData.coordinate_sq_le
    {x : V} {n : ℕ}
    (W : Matrix (Fin n) (SecondSubconstituent G x) ℤ)
    (d : FactorCentroidData G x W)
    (j : Fin n) :
    d.c j * d.c j ≤ 300 := by
  rw [← d.norm]
  exact Finset.single_le_sum
    (fun k _ => mul_self_nonneg (d.c k))
    (Finset.mem_univ j)

theorem FactorCentroidData.row_lower_bound
    (hG : IsHypothetical G) (x : V)
    {n : ℕ}
    (W : Matrix (Fin n) (SecondSubconstituent G x) ℤ)
    (hW : W.transpose * W = localGramMatrix G x)
    (d : FactorCentroidData G x W)
    (j : Fin n) :
    11 * |d.c j| ≤ ((factorRowSupport W j).card : ℤ) := by
  have habs :
      |∑ B, W j B| ≤ ∑ B, |W j B| := by
    simpa using
      (Finset.abs_sum_le_sum_abs
        (fun B : SecondSubconstituent G x => W j B)
        Finset.univ)
  have hsumabs :
      (∑ B, |W j B|) =
        ∑ B, if W j B ≠ 0 then (1 : ℤ) else 0 := by
    apply Finset.sum_congr rfl
    intro B _
    rcases factor_column_entry_cases G hG x W hW B j with
      hneg | hzero | hone
    · simp [hneg]
    · simp [hzero]
    · simp [hone]
  have hcard :
      (∑ B, if W j B ≠ 0 then (1 : ℤ) else 0) =
        ((factorRowSupport W j).card : ℤ) := by
    simpa [factorRowSupport] using
      (Finset.sum_boole
        (R := ℤ)
        (fun B : SecondSubconstituent G x => W j B ≠ 0)
        Finset.univ)
  rw [d.row_sum, hsumabs, hcard] at habs
  simpa [abs_mul] using habs

theorem FactorCentroidData.transpose_mulVec
    (x : V) {n : ℕ}
    (W : Matrix (Fin n) (SecondSubconstituent G x) ℤ)
    (d : FactorCentroidData G x W) :
    W.transpose *ᵥ d.c =
      fun _ => (15 : ℤ) := by
  funext B
  simpa [Matrix.mulVec_apply, dotProduct, mul_comm] using d.pairing B

theorem factor_mul_localGramMatrix
    (hG : IsHypothetical G) (x : V)
    {n : ℕ}
    (W : Matrix (Fin n) (SecondSubconstituent G x) ℤ)
    (hW : W.transpose * W = localGramMatrix G x)
    (d : FactorCentroidData G x W) :
    W * localGramMatrix G x =
      (45 : ℕ) • W +
        (6 : ℕ) • Matrix.vecMulVec d.c
          (1 : SecondSubconstituent G x → ℤ) := by
  obtain ⟨a, ha⟩ := d.span_witness
  have hLa :
      localGramMatrix G x *ᵥ a =
        fun _ => (15 : ℤ) := by
    calc
      localGramMatrix G x *ᵥ a =
          (W.transpose * W) *ᵥ a := by rw [hW]
      _ = W.transpose *ᵥ (W *ᵥ a) := by
        rw [← Matrix.mulVec_mulVec]
      _ = W.transpose *ᵥ d.c := by rw [← ha]
      _ = fun _ => (15 : ℤ) :=
        d.transpose_mulVec G x W
  ext j B
  let q : SecondSubconstituent G x → ℤ :=
    fun C =>
      localGramMatrix G x C B -
        45 * (if C = B then 1 else 0) -
          6 * a C
  have hLq : localGramMatrix G x *ᵥ q = 0 := by
    funext D
    have hsq :=
      congrFun (congrFun (localGramMatrix_sq G hG x) D) B
    change
      (localGramMatrix G x * localGramMatrix G x) D B =
        45 * localGramMatrix G x D B + 90 at hsq
    have hLaD := congrFun hLa D
    change (localGramMatrix G x *ᵥ a) D = 15 at hLaD
    have hdelta :
        (∑ C, localGramMatrix G x D C *
          (45 * (if C = B then 1 else 0))) =
          45 * localGramMatrix G x D B := by
      calc
        (∑ C, localGramMatrix G x D C *
          (45 * (if C = B then 1 else 0))) =
            45 * ∑ C, localGramMatrix G x D C *
              (if C = B then 1 else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro C _
          ring
        _ = 45 * localGramMatrix G x D B := by simp
    have haTerm :
        (∑ C, localGramMatrix G x D C * (6 * a C)) =
          6 * (localGramMatrix G x *ᵥ a) D := by
      rw [Matrix.mulVec_apply]
      change
        (∑ C, localGramMatrix G x D C * (6 * a C)) =
          6 * ∑ C, localGramMatrix G x D C * a C
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro C _
      ring
    change
      ∑ C, localGramMatrix G x D C *
        (localGramMatrix G x C B -
          45 * (if C = B then 1 else 0) -
            6 * a C) = 0
    calc
      (∑ C, localGramMatrix G x D C *
        (localGramMatrix G x C B -
          45 * (if C = B then 1 else 0) -
            6 * a C)) =
          (localGramMatrix G x * localGramMatrix G x) D B -
            45 * localGramMatrix G x D B -
              6 * (localGramMatrix G x *ᵥ a) D := by
        rw [Matrix.mul_apply, Matrix.mulVec_apply]
        simp only [dotProduct]
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
          hdelta, haTerm]
        rfl
      _ = 0 := by omega
  have hWq : W *ᵥ q = 0 := by
    apply factor_mulVec_eq_zero_of_gram_mulVec_eq_zero W q
    rw [hW]
    exact hLq
  have hWqj := congrFun hWq j
  change
    ∑ C, W j C *
      (localGramMatrix G x C B -
        45 * (if C = B then 1 else 0) -
          6 * a C) = 0 at hWqj
  change
    (W * localGramMatrix G x) j B =
      ((45 : ℕ) • W +
        (6 : ℕ) • Matrix.vecMulVec d.c
          (1 : SecondSubconstituent G x → ℤ)) j B
  rw [Matrix.add_apply, nsmulMatrix_apply, nsmulMatrix_apply]
  simp only [Matrix.vecMulVec, Pi.one_apply, mul_one]
  change
    (∑ C, W j C * localGramMatrix G x C B) =
      45 * W j B + 6 * d.c j
  rw [ha]
  change
    (∑ C, W j C * localGramMatrix G x C B) =
      45 * W j B + 6 * (∑ C, W j C * a C)
  have hdeltaW :
      (∑ C, W j C * (45 * (if C = B then 1 else 0))) =
        45 * W j B := by
    calc
      (∑ C, W j C * (45 * (if C = B then 1 else 0))) =
          45 * ∑ C, W j C * (if C = B then 1 else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro C _
        ring
      _ = 45 * W j B := by simp
  have haW :
      (∑ C, W j C * (6 * a C)) =
        6 * ∑ C, W j C * a C := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro C _
    ring
  simp_rw [mul_sub] at hWqj
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    hdeltaW, haW] at hWqj
  omega

/-- The row-frame operator of an integral factorization. -/
def factorFrame
    {ι : Type*} [Fintype ι] {n : ℕ}
    (W : Matrix (Fin n) ι ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  W * W.transpose

/-- The rank-one matrix formed from factorization centroid coordinates. -/
def factorCentroidOuter
    (x : V) {n : ℕ}
    {W : Matrix (Fin n) (SecondSubconstituent G x) ℤ}
    (d : FactorCentroidData G x W) :
    Matrix (Fin n) (Fin n) ℤ :=
  Matrix.vecMulVec d.c d.c

theorem factorFrame_sq
    (hG : IsHypothetical G) (x : V)
    {n : ℕ}
    (W : Matrix (Fin n) (SecondSubconstituent G x) ℤ)
    (hW : W.transpose * W = localGramMatrix G x)
    (d : FactorCentroidData G x W) :
    factorFrame W * factorFrame W =
      (45 : ℕ) • factorFrame W +
        (66 : ℕ) • factorCentroidOuter G x d := by
  calc
    factorFrame W * factorFrame W =
        (W * (W.transpose * W)) * W.transpose := by
      simp [factorFrame, Matrix.mul_assoc]
    _ = (W * localGramMatrix G x) * W.transpose := by rw [hW]
    _ = ((45 : ℕ) • W +
          (6 : ℕ) • Matrix.vecMulVec d.c
            (1 : SecondSubconstituent G x → ℤ)) * W.transpose := by
      rw [factor_mul_localGramMatrix G hG x W hW d]
    _ = (45 : ℕ) • factorFrame W +
        (66 : ℕ) • factorCentroidOuter G x d := by
      ext j k
      simp only [Matrix.mul_apply, Matrix.add_apply, nsmulMatrix_apply,
        Matrix.transpose_apply, Matrix.vecMulVec_apply, Pi.one_apply,
        mul_one, factorFrame, factorCentroidOuter]
      change
        (∑ B, (45 * W j B + 6 * d.c j) * W k B) =
          45 * (∑ B, W j B * W k B) +
            66 * (d.c j * d.c k)
      have hk := d.row_sum k
      calc
        (∑ B, (45 * W j B + 6 * d.c j) * W k B) =
            (∑ B, 45 * (W j B * W k B)) +
              ∑ B, (6 * d.c j) * W k B := by
          simp_rw [add_mul]
          rw [Finset.sum_add_distrib]
          congr 1
          · apply Finset.sum_congr rfl
            intro B _
            ring
        _ = 45 * (∑ B, W j B * W k B) +
            (6 * d.c j) * ∑ B, W k B := by
          rw [Finset.mul_sum, Finset.mul_sum]
        _ = 45 * (∑ B, W j B * W k B) +
            66 * (d.c j * d.c k) := by
          rw [hk]
          ring

theorem factorFrame_mulVec_centroid
    (x : V) {n : ℕ}
    (W : Matrix (Fin n) (SecondSubconstituent G x) ℤ)
    (d : FactorCentroidData G x W) :
    factorFrame W *ᵥ d.c =
      fun j => 165 * d.c j := by
  calc
    factorFrame W *ᵥ d.c =
        W *ᵥ (W.transpose *ᵥ d.c) := by
      change (W * W.transpose) *ᵥ d.c =
        W *ᵥ (W.transpose *ᵥ d.c)
      rw [← Matrix.mulVec_mulVec]
    _ = W *ᵥ (fun _ => (15 : ℤ)) := by
      rw [d.transpose_mulVec G x W]
    _ = fun j => 165 * d.c j := by
      funext j
      change (∑ B, W j B * 15) = 165 * d.c j
      rw [← Finset.sum_mul, d.row_sum]
      ring

theorem factorFrame_mul_centroidOuter
    (x : V) {n : ℕ}
    (W : Matrix (Fin n) (SecondSubconstituent G x) ℤ)
    (d : FactorCentroidData G x W) :
    factorFrame W * factorCentroidOuter G x d =
      (165 : ℕ) • factorCentroidOuter G x d := by
  ext j k
  change
    (∑ l, factorFrame W j l * (d.c l * d.c k)) =
      165 * (d.c j * d.c k)
  calc
    (∑ l, factorFrame W j l * (d.c l * d.c k)) =
        (∑ l, factorFrame W j l * d.c l) * d.c k := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ = 165 * (d.c j * d.c k) := by
      change (factorFrame W *ᵥ d.c) j * d.c k =
        165 * (d.c j * d.c k)
      rw [factorFrame_mulVec_centroid G x W d]
      ring

theorem centroidOuter_mul_factorFrame
    (x : V) {n : ℕ}
    (W : Matrix (Fin n) (SecondSubconstituent G x) ℤ)
    (d : FactorCentroidData G x W) :
    factorCentroidOuter G x d * factorFrame W =
      (165 : ℕ) • factorCentroidOuter G x d := by
  ext j k
  change
    (∑ l, (d.c j * d.c l) * factorFrame W l k) =
      165 * (d.c j * d.c k)
  have hsymm :
      ∀ l k, factorFrame W l k = factorFrame W k l := by
    intro l k
    simp [factorFrame, Matrix.mul_apply, mul_comm]
  calc
    (∑ l, (d.c j * d.c l) * factorFrame W l k) =
        d.c j * ∑ l, factorFrame W k l * d.c l := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      rw [hsymm l k]
      ring
    _ = 165 * (d.c j * d.c k) := by
      change d.c j * (factorFrame W *ᵥ d.c) k =
        165 * (d.c j * d.c k)
      rw [factorFrame_mulVec_centroid G x W d]
      ring

theorem centroidOuter_sq
    (x : V) {n : ℕ}
    {W : Matrix (Fin n) (SecondSubconstituent G x) ℤ}
    (d : FactorCentroidData G x W) :
    factorCentroidOuter G x d * factorCentroidOuter G x d =
      (300 : ℕ) • factorCentroidOuter G x d := by
  ext j k
  change
    (∑ l, (d.c j * d.c l) * (d.c l * d.c k)) =
      300 * (d.c j * d.c k)
  calc
    (∑ l, (d.c j * d.c l) * (d.c l * d.c k)) =
        d.c j * (∑ l, d.c l * d.c l) * d.c k := by
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ = 300 * (d.c j * d.c k) := by rw [d.norm]; ring

/-- The integral numerator `5F - 2ccᵀ` of the ambient row-space
projector. -/
def factorProjectorNumerator
    (x : V) {n : ℕ}
    (W : Matrix (Fin n) (SecondSubconstituent G x) ℤ)
    (d : FactorCentroidData G x W) :
    Matrix (Fin n) (Fin n) ℤ :=
  (5 : ℕ) • factorFrame W -
    (2 : ℕ) • factorCentroidOuter G x d

theorem factorProjectorNumerator_sq
    (hG : IsHypothetical G) (x : V)
    {n : ℕ}
    (W : Matrix (Fin n) (SecondSubconstituent G x) ℤ)
    (hW : W.transpose * W = localGramMatrix G x)
    (d : FactorCentroidData G x W) :
    factorProjectorNumerator G x W d *
        factorProjectorNumerator G x W d =
      (225 : ℕ) • factorProjectorNumerator G x W d := by
  let F := factorFrame W
  let C := factorCentroidOuter G x d
  have hFF : F * F = (45 : ℕ) • F + (66 : ℕ) • C := by
    simpa [F, C] using factorFrame_sq G hG x W hW d
  have hFC : F * C = (165 : ℕ) • C := by
    simpa [F, C] using factorFrame_mul_centroidOuter G x W d
  have hCF : C * F = (165 : ℕ) • C := by
    simpa [F, C] using centroidOuter_mul_factorFrame G x W d
  have hCC : C * C = (300 : ℕ) • C := by
    simpa [C] using centroidOuter_sq G x d
  change
    ((5 : ℕ) • F - (2 : ℕ) • C) *
        ((5 : ℕ) • F - (2 : ℕ) • C) =
      (225 : ℕ) • ((5 : ℕ) • F - (2 : ℕ) • C)
  noncomm_ring [hFF, hFC, hCF, hCC]

/-- The rational ambient projector associated with an integral
factorization. -/
noncomputable def factorSupportProjector
    (x : V) {n : ℕ}
    (W : Matrix (Fin n) (SecondSubconstituent G x) ℤ)
    (d : FactorCentroidData G x W) :
    Matrix (Fin n) (Fin n) ℚ :=
  fun j k => (factorProjectorNumerator G x W d j k : ℚ) / 225

theorem factorSupportProjector_idempotent
    (hG : IsHypothetical G) (x : V)
    {n : ℕ}
    (W : Matrix (Fin n) (SecondSubconstituent G x) ℤ)
    (hW : W.transpose * W = localGramMatrix G x)
    (d : FactorCentroidData G x W) :
    factorSupportProjector G x W d *
        factorSupportProjector G x W d =
      factorSupportProjector G x W d := by
  ext j k
  rw [Matrix.mul_apply]
  have hcast :
      (∑ l,
          (factorProjectorNumerator G x W d j l : ℚ) *
            (factorProjectorNumerator G x W d l k : ℚ)) =
        ((factorProjectorNumerator G x W d *
          factorProjectorNumerator G x W d) j k : ℤ) := by
    rw [Matrix.mul_apply]
    norm_cast
  change
    (∑ l,
      (factorProjectorNumerator G x W d j l : ℚ) / 225 *
        ((factorProjectorNumerator G x W d l k : ℚ) / 225)) =
      (factorProjectorNumerator G x W d j k : ℚ) / 225
  calc
    (∑ l,
        (factorProjectorNumerator G x W d j l : ℚ) / 225 *
          ((factorProjectorNumerator G x W d l k : ℚ) / 225)) =
        (∑ l,
          (factorProjectorNumerator G x W d j l : ℚ) *
            (factorProjectorNumerator G x W d l k : ℚ)) / 50625 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ = ((factorProjectorNumerator G x W d *
          factorProjectorNumerator G x W d) j k : ℤ) / 50625 := by
      rw [hcast]
    _ = (factorProjectorNumerator G x W d j k : ℚ) / 225 := by
      have hsq :=
        congrFun
          (congrFun
            (factorProjectorNumerator_sq G hG x W hW d) j) k
      change
        (factorProjectorNumerator G x W d *
          factorProjectorNumerator G x W d) j k =
            225 * factorProjectorNumerator G x W d j k at hsq
      rw [hsq]
      push_cast
      ring

theorem factorSupportProjector_isSymm
    (x : V) {n : ℕ}
    (W : Matrix (Fin n) (SecondSubconstituent G x) ℤ)
    (d : FactorCentroidData G x W) :
    (factorSupportProjector G x W d).IsSymm := by
  have hF : (factorFrame W).IsSymm := by
    apply Matrix.IsSymm.ext
    intro j k
    simp [factorFrame, Matrix.mul_apply, mul_comm]
  have hC : (factorCentroidOuter G x d).IsSymm := by
    apply Matrix.IsSymm.ext
    intro j k
    simp [factorCentroidOuter, Matrix.vecMulVec_apply, mul_comm]
  have hN : (factorProjectorNumerator G x W d).IsSymm := by
    exact (hF.smul (5 : ℕ)).sub (hC.smul (2 : ℕ))
  apply Matrix.IsSymm.ext
  intro j k
  change
    (factorProjectorNumerator G x W d k j : ℚ) / 225 =
      (factorProjectorNumerator G x W d j k : ℚ) / 225
  rw [hN.apply j k]

theorem symmetric_idempotent_diagonal_nonneg
    {ι : Type*} [Fintype ι]
    (P : Matrix ι ι ℚ)
    (hsymm : P.IsSymm) (hidempotent : P * P = P)
    (i : ι) :
    0 ≤ P i i := by
  have hii := congrFun (congrFun hidempotent i) i
  rw [Matrix.mul_apply] at hii
  rw [← hii]
  apply Finset.sum_nonneg
  intro j _
  rw [hsymm.apply i j]
  exact mul_self_nonneg (P i j)

theorem symmetric_idempotent_diagonal_le_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℚ)
    (hsymm : P.IsSymm) (hidempotent : P * P = P)
    (i : ι) :
    P i i ≤ 1 := by
  let Q : Matrix ι ι ℚ := 1 - P
  have hQsymm : Q.IsSymm := by
    exact (Matrix.isSymm_one.sub hsymm)
  have hQidem : Q * Q = Q := by
    change (1 - P) * (1 - P) = 1 - P
    noncomm_ring [hidempotent]
  have hnonneg :=
    symmetric_idempotent_diagonal_nonneg Q hQsymm hQidem i
  change 0 ≤ (1 - P) i i at hnonneg
  simp at hnonneg
  linarith

/-- A diagonal entry of the row-frame operator counts the non-zero entries
of the corresponding row. -/
theorem factorFrame_diagonal_eq_rowSupport_card
    (hG : IsHypothetical G) (x : V)
    {n : ℕ}
    (W : Matrix (Fin n) (SecondSubconstituent G x) ℤ)
    (hW : W.transpose * W = localGramMatrix G x)
    (j : Fin n) :
    factorFrame W j j = ((factorRowSupport W j).card : ℤ) := by
  have hentries :
      (∑ B, W j B * W j B) =
        ∑ B, if W j B ≠ 0 then (1 : ℤ) else 0 := by
    apply Finset.sum_congr rfl
    intro B _
    rcases factor_column_entry_cases G hG x W hW B j with
      hneg | hzero | hone
    · simp [hneg]
    · simp [hzero]
    · simp [hone]
  have hcard :
      (∑ B, if W j B ≠ 0 then (1 : ℤ) else 0) =
        ((factorRowSupport W j).card : ℤ) := by
    simpa [factorRowSupport] using
      (Finset.sum_boole
        (R := ℤ)
        (fun B : SecondSubconstituent G x => W j B ≠ 0)
        Finset.univ)
  change (∑ B, W j B * W j B) =
    ((factorRowSupport W j).card : ℤ)
  rw [hentries, hcard]

/-- The diagonal bound for the row-space projector, cleared of
denominators. -/
theorem FactorCentroidData.row_upper_bound
    (hG : IsHypothetical G) (x : V)
    {n : ℕ}
    (W : Matrix (Fin n) (SecondSubconstituent G x) ℤ)
    (hW : W.transpose * W = localGramMatrix G x)
    (d : FactorCentroidData G x W)
    (j : Fin n) :
    5 * ((factorRowSupport W j).card : ℤ) ≤
      225 + 2 * d.c j * d.c j := by
  have hp :=
    symmetric_idempotent_diagonal_le_one
      (factorSupportProjector G x W d)
      (factorSupportProjector_isSymm G x W d)
      (factorSupportProjector_idempotent G hG x W hW d)
      j
  have hnum :
      factorProjectorNumerator G x W d j j =
        5 * factorFrame W j j - 2 * (d.c j * d.c j) := by
    simp only [factorProjectorNumerator,
      Matrix.sub_apply, nsmulMatrix_apply, factorCentroidOuter,
      Matrix.vecMulVec_apply]
    norm_num
  change
    ((factorProjectorNumerator G x W d j j : ℤ) : ℚ) / 225 ≤ 1 at hp
  rw [hnum] at hp
  have hpcast :
      ((5 * factorFrame W j j -
          2 * (d.c j * d.c j) : ℤ) : ℚ) ≤ 225 := by
    norm_num [div_eq_mul_inv] at hp ⊢
    linarith
  have hpint :
      5 * factorFrame W j j -
          2 * (d.c j * d.c j) ≤ 225 := by
    exact_mod_cast hpcast
  rw [factorFrame_diagonal_eq_rowSupport_card G hG x W hW j] at hpint
  nlinarith

/-- The exact integer form of the coordinate inequality in the
one-integrability argument. -/
theorem centroid_coordinate_abs_le_five
    (c n : ℤ)
    (hnorm : c * c ≤ 300)
    (hlower : 11 * |c| ≤ n)
    (hupper : 5 * n ≤ 225 + 2 * c * c) :
    |c| ≤ 5 := by
  let a : ℤ := |c|
  have ha0 : 0 ≤ a := abs_nonneg c
  have hasq : a * a ≤ 300 := by
    simpa [a] using hnorm
  have hac : c * c = a * a := by
    change c * c = |c| * |c|
    exact (abs_mul_abs_self c).symm
  have hpoly : 55 * a ≤ 225 + 2 * a * a := by
    calc
      55 * a = 5 * (11 * |c|) := by simp [a]; ring
      _ ≤ 5 * n := by omega
      _ ≤ 225 + 2 * c * c := hupper
      _ = 225 + 2 * (c * c) := by ring
      _ = 225 + 2 * (a * a) := by rw [hac]
      _ = 225 + 2 * a * a := by ring
  by_contra hnot
  have ha6 : 6 ≤ a := by omega
  have ha18 : a < 18 := by nlinarith
  have hnegative : (2 * a - 45) * (a - 5) < 0 := by
    nlinarith
  have hnonnegative : 0 ≤ (2 * a - 45) * (a - 5) := by
    nlinarith
  omega

/-- Every centroid coordinate in an integral factorization has absolute
value at most five. -/
theorem FactorCentroidData.coordinate_abs_le_five
    (hG : IsHypothetical G) (x : V)
    {n : ℕ}
    (W : Matrix (Fin n) (SecondSubconstituent G x) ℤ)
    (hW : W.transpose * W = localGramMatrix G x)
    (d : FactorCentroidData G x W)
    (j : Fin n) :
    |d.c j| ≤ 5 := by
  exact centroid_coordinate_abs_le_five
    (d.c j) ((factorRowSupport W j).card : ℤ)
    (FactorCentroidData.coordinate_sq_le G W d j)
    (FactorCentroidData.row_lower_bound G hG x W hW d j)
    (FactorCentroidData.row_upper_bound G hG x W hW d j)

/-- If a finite family is bounded above by five and its sum attains that
upper bound term by term, every term equals five. -/
theorem finset_term_eq_five_of_sum_eq
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℤ)
    (hle : ∀ i ∈ s, f i ≤ 5)
    (hsum : ∑ i ∈ s, f i = 5 * (s.card : ℤ))
    {i : ι} (hi : i ∈ s) :
    f i = 5 := by
  have hnonneg : ∀ k ∈ s, 0 ≤ 5 - f k := by
    intro k hk
    have := hle k hk
    omega
  have hzero : ∑ k ∈ s, (5 - f k) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, hsum]
    simp
    ring
  have hi0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hzero i hi
  omega

/-- Every non-zero entry of a factor column is sign-aligned with the
centroid, and their product is exactly five. -/
theorem FactorCentroidData.centroid_mul_factor_entry
    (hG : IsHypothetical G) (x : V)
    {n : ℕ}
    (W : Matrix (Fin n) (SecondSubconstituent G x) ℤ)
    (hW : W.transpose * W = localGramMatrix G x)
    (d : FactorCentroidData G x W)
    (B : SecondSubconstituent G x) (j : Fin n)
    (hj : j ∈ factorColumnSupport W B) :
    d.c j * W j B = 5 := by
  have hsum :
      (∑ k ∈ factorColumnSupport W B, d.c k * W k B) = 15 := by
    calc
      (∑ k ∈ factorColumnSupport W B, d.c k * W k B) =
          ∑ k, d.c k * W k B := by
        apply Finset.sum_subset
          (Finset.subset_univ (factorColumnSupport W B))
        intro k _ hk
        have hkzero : W k B = 0 := by
          by_contra hkne
          exact hk (by simp [factorColumnSupport, hkne])
        simp [hkzero]
      _ = 15 := d.pairing B
  have hle :
      ∀ k ∈ factorColumnSupport W B, d.c k * W k B ≤ 5 := by
    intro k _
    have hc :=
      FactorCentroidData.coordinate_abs_le_five G hG x W hW d k
    rcases factor_column_entry_cases G hG x W hW B k with
      hneg | hzero | hone
    · rw [hneg]
      simpa using (le_trans (neg_le_abs (d.c k)) hc)
    · simp [hzero]
    · rw [hone]
      simpa using (le_trans (le_abs_self (d.c k)) hc)
  apply finset_term_eq_five_of_sum_eq
    (factorColumnSupport W B) (fun k => d.c k * W k B) hle
  · simpa [factor_column_support_card G hG x W hW B] using hsum
  · exact hj

/-- Three integer summands bounded above by five can sum to fifteen only at
the upper bound in every coordinate. -/
theorem three_terms_eq_five
    {a b c : ℤ}
    (ha : a ≤ 5) (hb : b ≤ 5) (hc : c ≤ 5)
    (hsum : a + b + c = 15) :
    a = 5 ∧ b = 5 ∧ c = 5 := by
  omega

/-- Flip each factor row according to the sign of its centroid coordinate. -/
def alignedFactor
    (x : V) {n : ℕ}
    (W : Matrix (Fin n) (SecondSubconstituent G x) ℤ)
    (d : FactorCentroidData G x W) :
    Matrix (Fin n) (SecondSubconstituent G x) ℤ :=
  fun j B => if d.c j < 0 then -W j B else W j B

/-- Row sign changes preserve the Gram matrix. -/
theorem alignedFactor_transpose_mul
    (x : V) {n : ℕ}
    (W : Matrix (Fin n) (SecondSubconstituent G x) ℤ)
    (d : FactorCentroidData G x W) :
    (alignedFactor G x W d).transpose * alignedFactor G x W d =
      W.transpose * W := by
  ext B C
  simp only [Matrix.mul_apply, Matrix.transpose_apply, alignedFactor]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : d.c j < 0 <;> simp [hj]

/-- Centroid sign alignment makes every factor entry nonnegative. -/
theorem alignedFactor_nonneg
    (hG : IsHypothetical G) (x : V)
    {n : ℕ}
    (W : Matrix (Fin n) (SecondSubconstituent G x) ℤ)
    (hW : W.transpose * W = localGramMatrix G x)
    (d : FactorCentroidData G x W) :
    ∀ j B, 0 ≤ alignedFactor G x W d j B := by
  intro j B
  by_cases hc : d.c j < 0
  · rw [alignedFactor]
    simp only [if_pos hc]
    rcases factor_column_entry_cases G hG x W hW B j with
      hneg | hzero | hone
    · simp [hneg]
    · simp [hzero]
    · have hj : j ∈ factorColumnSupport W B := by
        simp [factorColumnSupport, hone]
      have hprod :=
        FactorCentroidData.centroid_mul_factor_entry
          G hG x W hW d B j hj
      rw [hone] at hprod
      omega
  · rw [alignedFactor]
    simp only [if_neg hc]
    rcases factor_column_entry_cases G hG x W hW B j with
      hneg | hzero | hone
    · have hj : j ∈ factorColumnSupport W B := by
        simp [factorColumnSupport, hneg]
      have hprod :=
        FactorCentroidData.centroid_mul_factor_entry
          G hG x W hW d B j hj
      rw [hneg] at hprod
      omega
    · simp [hzero]
    · simp [hone]

/-- Some row of the aligned factor has sum 55. -/
theorem exists_alignedFactor_row_sum_fifty_five
    (hG : IsHypothetical G) (x : V)
    {n : ℕ}
    (W : Matrix (Fin n) (SecondSubconstituent G x) ℤ)
    (hW : W.transpose * W = localGramMatrix G x)
    (d : FactorCentroidData G x W) :
    ∃ j : Fin n, ∑ B, alignedFactor G x W d j B = 55 := by
  have hsecond :
      (Finset.univ : Finset (SecondSubconstituent G x)).Nonempty := by
    rw [Finset.univ_nonempty_iff]
    exact Fintype.card_pos_iff.mp (by
      rw [secondSubconstituent_card G hG x]
      norm_num)
  obtain ⟨B, _⟩ := hsecond
  have hsupport :
      (factorColumnSupport W B).Nonempty := by
    apply Finset.card_pos.mp
    rw [factor_column_support_card G hG x W hW B]
    norm_num
  obtain ⟨j, hj⟩ := hsupport
  have hprod :=
    FactorCentroidData.centroid_mul_factor_entry
      G hG x W hW d B j hj
  have hentry :=
    factor_column_entry_cases G hG x W hW B j
  have hc : d.c j = -5 ∨ d.c j = 5 := by
    rcases hentry with hneg | hzero | hone
    · left
      rw [hneg] at hprod
      omega
    · rw [hzero] at hprod
      norm_num at hprod
    · right
      rw [hone] at hprod
      omega
  refine ⟨j, ?_⟩
  rcases hc with hc | hc
  · have hneg : (-5 : ℤ) < 0 := by norm_num
    simp only [alignedFactor, hc, if_pos hneg]
    rw [Finset.sum_neg_distrib, d.row_sum, hc]
    norm_num
  · have hnot : ¬(5 : ℤ) < 0 := by norm_num
    simp only [alignedFactor, hc, if_neg hnot]
    rw [d.row_sum, hc]
    norm_num

theorem factor_entry_eq_one_of_nonnegative
    (hG : IsHypothetical G) (x : V)
    {n : ℕ}
    (W : Matrix (Fin n) (SecondSubconstituent G x) ℤ)
    (hW : W.transpose * W = localGramMatrix G x)
    (hnonneg : ∀ j B, 0 ≤ W j B)
    {j : Fin n} {B : SecondSubconstituent G x}
    (hmem : B ∈ factorRowSupport W j) :
    W j B = 1 := by
  have hne : W j B ≠ 0 := by
    simpa [factorRowSupport] using hmem
  rcases factor_column_entry_cases G hG x W hW B j with
    hneg | hzero | hone
  · have := hnonneg j B
    omega
  · exact (hne hzero).elim
  · exact hone

/-- Once coordinate signs have been aligned, every row support is an
independent set in the second-subconstituent graph. -/
theorem factorRowSupport_isIndepSet
    (hG : IsHypothetical G) (x : V)
    {n : ℕ}
    (W : Matrix (Fin n) (SecondSubconstituent G x) ℤ)
    (hW : W.transpose * W = localGramMatrix G x)
    (hnonneg : ∀ j B, 0 ≤ W j B)
    (j : Fin n) :
    (secondSubconstituentGraph G x).IsIndepSet
      (factorRowSupport W j : Set (SecondSubconstituent G x)) := by
  rw [SimpleGraph.isIndepSet_iff]
  intro B hB C hC hne hBC
  have hBj :
      W j B = 1 :=
    factor_entry_eq_one_of_nonnegative G hG x W hW hnonneg hB
  have hCj :
      W j C = 1 :=
    factor_entry_eq_one_of_nonnegative G hG x W hW hnonneg hC
  have hnonnegative :
      ∀ k ∈ (Finset.univ : Finset (Fin n)),
        0 ≤ W k B * W k C := by
    intro k _
    exact mul_nonneg (hnonneg k B) (hnonneg k C)
  have hone_le :
      W j B * W j C ≤ ∑ k, W k B * W k C :=
    Finset.single_le_sum hnonnegative (Finset.mem_univ j)
  rw [hBj, hCj] at hone_le
  have hfactor := congrFun (congrFun hW B) C
  have hzero := localGramMatrix_of_adj G hG x hBC
  rw [hzero] at hfactor
  have :
      ∑ k, W k B * W k C = 0 := by
    simpa [Matrix.mul_apply] using hfactor
  omega

theorem factorRowSupport_card_of_sum
    (hG : IsHypothetical G) (x : V)
    {n : ℕ}
    (W : Matrix (Fin n) (SecondSubconstituent G x) ℤ)
    (hW : W.transpose * W = localGramMatrix G x)
    (hnonneg : ∀ j B, 0 ≤ W j B)
    (j : Fin n)
    (hsum : ∑ B, W j B = 55) :
    (factorRowSupport W j).card = 55 := by
  have hentries :
      (∑ B, W j B) =
        ∑ B, if W j B ≠ 0 then (1 : ℤ) else 0 := by
    apply Finset.sum_congr rfl
    intro B _
    by_cases hzero : W j B = 0
    · simp [hzero]
    · have hone :
          W j B = 1 :=
        factor_entry_eq_one_of_nonnegative G hG x W hW hnonneg
          (by simpa [factorRowSupport] using hzero)
      simp [hone]
  have hcard :
      (∑ B, if W j B ≠ 0 then (1 : ℤ) else 0) =
        ((factorRowSupport W j).card : ℤ) := by
    simpa [factorRowSupport] using
      (Finset.sum_boole
        (R := ℤ)
        (fun B : SecondSubconstituent G x => W j B ≠ 0)
        Finset.univ)
  have hcard' : ((factorRowSupport W j).card : ℤ) = 55 := by
    omega
  exact_mod_cast hcard'

/-- Extend a set of second-subconstituent vertices by the root. -/
def extendSecondCoclique
    (x : V) (S : Finset (SecondSubconstituent G x)) : Finset V :=
  insert x (S.image Subtype.val)

omit [Fintype V] [DecidableRel G.Adj] in
theorem extendSecondCoclique_card
    (x : V) (S : Finset (SecondSubconstituent G x)) :
    (extendSecondCoclique G x S).card = S.card + 1 := by
  have hroot : x ∉ S.image Subtype.val := by
    intro hx
    rw [Finset.mem_image] at hx
    obtain ⟨B, _, hBx⟩ := hx
    have hne : x ≠ (B : V) :=
      ((G.compl_adj x B).mp B.property).1
    exact hne hBx.symm
  rw [extendSecondCoclique, Finset.card_insert_of_notMem hroot,
    Finset.card_image_of_injective S Subtype.val_injective]

omit [Fintype V] [DecidableRel G.Adj] in
theorem extendSecondCoclique_isIndepSet
    (x : V) (S : Finset (SecondSubconstituent G x))
    (hS : (secondSubconstituentGraph G x).IsIndepSet
      (S : Set (SecondSubconstituent G x))) :
    G.IsIndepSet (extendSecondCoclique G x S : Set V) := by
  rw [SimpleGraph.isIndepSet_iff]
  intro a ha b hb hab
  simp only [extendSecondCoclique, Finset.coe_insert,
    Finset.coe_image, Set.mem_insert_iff, Set.mem_image] at ha hb
  rcases ha with hax | ⟨A, hAS, hAa⟩
  · subst a
    rcases hb with hbx | ⟨B, _, hBb⟩
    · subst b
      exact (hab rfl).elim
    · subst b
      exact ((G.compl_adj x B).mp B.property).2
  · subst a
    rcases hb with hbx | ⟨B, hBS, hBb⟩
    · subst b
      intro hAx
      exact ((G.compl_adj x A).mp A.property).2 hAx.symm
    · subst b
      have hneAB : A ≠ B := by
        intro hAB
        apply hab
        exact congrArg Subtype.val hAB
      exact hS hAS hBS hneAB

/-- An aligned factorization row of sum 55 produces a global independent set
of size 56. -/
theorem exists_global_coclique_of_aligned_factor_row
    (hG : IsHypothetical G) (x : V)
    {n : ℕ}
    (W : Matrix (Fin n) (SecondSubconstituent G x) ℤ)
    (hW : W.transpose * W = localGramMatrix G x)
    (hnonneg : ∀ j B, 0 ≤ W j B)
    (j : Fin n)
    (hsum : ∑ B, W j B = 55) :
    ∃ C : Finset V, C.card = 56 ∧
      G.IsIndepSet (C : Set V) := by
  let S := factorRowSupport W j
  refine ⟨extendSecondCoclique G x S, ?_, ?_⟩
  · rw [extendSecondCoclique_card]
    rw [factorRowSupport_card_of_sum G hG x W hW hnonneg j hsum]
  · apply extendSecondCoclique_isIndepSet G x S
    exact factorRowSupport_isIndepSet G hG x W hW hnonneg j

/-- One-integrability of the local Gram matrix forces a global coclique of
size 56. -/
theorem exists_global_coclique_of_oneIntegrable
    (hG : IsHypothetical G) (x : V)
    (hInt : LocalGramIsOneIntegrable G x) :
    ∃ C : Finset V, C.card = 56 ∧
      G.IsIndepSet (C : Set V) := by
  obtain ⟨n, W, hW⟩ := hInt
  let d : FactorCentroidData G x W :=
    Classical.choice (exists_factorCentroidData G hG x W hW)
  let A := alignedFactor G x W d
  have hA :
      A.transpose * A = localGramMatrix G x := by
    calc
      A.transpose * A = W.transpose * W := by
        exact alignedFactor_transpose_mul G x W d
      _ = localGramMatrix G x := hW
  have hnonneg : ∀ j B, 0 ≤ A j B :=
    alignedFactor_nonneg G hG x W hW d
  obtain ⟨j, hsum⟩ :=
    exists_alignedFactor_row_sum_fifty_five G hG x W hW d
  exact exists_global_coclique_of_aligned_factor_row
    G hG x A hA hnonneg j hsum

end SRG266
