/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Lattice.SchwartzPeriodization

/-!
# Local normal convergence of Schwartz periodizations

This file supplies the decay estimate required by
`SchwartzPeriodization.lean`.  It first identifies coordinate integer vectors
with Mathlib's standard `ZLattice`, so the existing lattice `p`-series theorem
can be reused without an independent counting argument.
-/

noncomputable section

namespace SRG266.Lattice

open Filter Asymptotics
open scoped FourierTransform SchwartzMap

/-- The standard coordinate lattice in real Euclidean space. -/
abbrev standardIntegerLattice (n : ℕ) :
    Submodule ℤ (Fin n → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))

/-- Integral coordinate vectors are linearly equivalent to the standard
coordinate lattice. -/
abbrev intVectorEquivStandardIntegerLattice (n : ℕ) :
    (Fin n → ℤ) ≃ₗ[ℤ] standardIntegerLattice n :=
  ((Pi.basisFun ℝ (Fin n)).restrictScalars ℤ).equivFun.symm

@[simp]
theorem coe_intVectorEquivStandardIntegerLattice {n : ℕ} (z : Fin n → ℤ) :
    ((intVectorEquivStandardIntegerLattice n z : standardIntegerLattice n) :
      Fin n → ℝ) = fun i => (z i : ℝ) := by
  classical
  rw [intVectorEquivStandardIntegerLattice,
    Module.Basis.equivFun_symm_apply]
  ext j
  simp [Pi.single_apply]

/-- The standard coordinate lattice `p`-series converges beyond its rank. -/
theorem summable_intVector_norm_rpow {n : ℕ} (r : ℝ)
    (hr : r < -(n : ℝ)) :
    Summable fun z : Fin n → ℤ => ‖intVectorToReal z‖ ^ r := by
  let L := standardIntegerLattice n
  let e := intVectorEquivStandardIntegerLattice n
  letI : DiscreteTopology L := ZSpan.discreteTopology_pi_basisFun
  have hrank : Module.finrank ℤ L = n := by
    rw [show L = standardIntegerLattice n by rfl]
    simpa using
      Module.finrank_eq_card_basis
        ((Pi.basisFun ℝ (Fin n)).restrictScalars ℤ)
  have hL : Summable fun z : L => ‖z‖ ^ r :=
    ZLattice.summable_norm_rpow L r (by simpa [hrank] using hr)
  rw [← e.toEquiv.summable_iff] at hL
  have hsup : Summable fun z : Fin n → ℤ =>
      ‖(fun i => (z i : ℝ))‖ ^ r := by
    convert hL using 1
    funext z
    change ‖(fun i => (z i : ℝ))‖ ^ r =
      ‖((e z : L) : Fin n → ℝ)‖ ^ r
    rw [show ((e z : L) : Fin n → ℝ) = fun i => (z i : ℝ) by
      simpa [e, L] using coe_intVectorEquivStandardIntegerLattice z]
  refine Summable.of_nonneg_of_le (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
    (fun z => ?_) hsup
  by_cases hz : z = 0
  · subst z
    rw [intVectorToReal_zero]
    have hzero : ‖(fun i : Fin n => ((0 : Fin n → ℤ) i : ℝ))‖ = 0 := by
      rw [norm_eq_zero]
      ext i
      simp
    rw [norm_zero, hzero]
  · apply Real.rpow_le_rpow_of_nonpos
    · apply norm_pos_iff.mpr
      intro hcast
      apply hz
      funext i
      simpa using congrFun hcast i
    · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
      intro i
      simpa [intVectorToReal] using PiLp.norm_apply_le (intVectorToReal z) i
    · exact (hr.trans_le (neg_nonpos.mpr (Nat.cast_nonneg n))).le

/-- Polynomial decay of order strictly larger than the dimension is enough
for local normal convergence of the integral periodization. -/
theorem locallyNormallySummableIntegerTranslates_of_pow_decay
    {n k : ℕ} (f : C(EuclideanSpace ℝ (Fin n), ℂ)) (hnk : n < k)
    {A : ℝ} (hA : 0 ≤ A)
    (hdecay : ∀ u : EuclideanSpace ℝ (Fin n), u ≠ 0 →
      ‖f u‖ ≤ A / ‖u‖ ^ k) :
    LocallyNormallySummableIntegerTranslates f := by
  classical
  intro K
  obtain ⟨R₀, hR₀⟩ := K.isCompact.isBounded.subset_closedBall
    (0 : EuclideanSpace ℝ (Fin n))
  let R : ℝ := max 0 R₀
  have hR : 0 ≤ R := le_max_left _ _
  have hKR : (K : Set (EuclideanSpace ℝ (Fin n))) ⊆
      Metric.closedBall 0 R :=
    hR₀.trans (Metric.closedBall_subset_closedBall (le_max_right _ _))
  let majorant : (Fin n → ℤ) → ℝ := fun z =>
    (A * 2 ^ k) * ‖intVectorToReal z‖ ^ (-(k : ℝ))
  have hk : (-(k : ℝ)) < -(n : ℝ) := by
    have hnkR : (n : ℝ) < (k : ℝ) := by exact_mod_cast hnk
    linarith
  have hmajorant : Summable majorant :=
    (summable_intVector_norm_rpow (-(k : ℝ)) hk).mul_left (A * 2 ^ k)
  apply Summable.of_norm_bounded_eventually hmajorant
  let bad : Set (Fin n → ℤ) :=
    {z | ‖intVectorToReal z‖ ≤ 2 * R}
  have hbad : bad.Finite := by
    let L := standardIntegerLattice n
    let e := intVectorEquivStandardIntegerLattice n
    have hfiniteL :
        (Metric.closedBall (0 : Fin n → ℝ) (2 * R) ∩
          (L : Set (Fin n → ℝ))).Finite :=
      ZSpan.setFinite_inter (Pi.basisFun ℝ (Fin n))
        Metric.isBounded_closedBall
    refine Set.Finite.of_finite_image
      (f := fun z => ((e z : L) : Fin n → ℝ))
      (hfiniteL.subset ?_) ?_
    · rintro _ ⟨z, hz, rfl⟩
      constructor
      · rw [Metric.mem_closedBall, dist_zero_right]
        change ‖((e z : L) : Fin n → ℝ)‖ ≤ 2 * R
        rw [show ((e z : L) : Fin n → ℝ) = fun i => (z i : ℝ) by
          simpa [e, L] using coe_intVectorEquivStandardIntegerLattice z]
        refine (show ‖(fun i => (z i : ℝ))‖ ≤ ‖intVectorToReal z‖ by
          rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
          intro i
          simpa [intVectorToReal] using PiLp.norm_apply_le (intVectorToReal z) i).trans hz
      · exact SetLike.coe_mem _
    · intro z _ w _ h
      exact e.injective (Subtype.ext h)
  filter_upwards [hbad.compl_mem_cofinite] with z hz
  have hzlarge : 2 * R < ‖intVectorToReal z‖ := by
    simpa [bad] using hz
  have hznorm : 0 < ‖intVectorToReal z‖ :=
    (mul_nonneg (by norm_num) hR).trans_lt hzlarge
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  apply (ContinuousMap.norm_le _ (by positivity)).2
  rintro ⟨x, hx⟩
  have hxR : ‖x‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hKR hx
  let u := x + intVectorToReal z
  have hu_lower : ‖intVectorToReal z‖ / 2 ≤ ‖u‖ := by
    have htri : ‖intVectorToReal z‖ - ‖x‖ ≤ ‖u‖ := by
      simpa [u, add_comm] using norm_sub_norm_le (intVectorToReal z) (-x)
    calc
      ‖intVectorToReal z‖ / 2 ≤ ‖intVectorToReal z‖ - R := by linarith
      _ ≤ ‖intVectorToReal z‖ - ‖x‖ := sub_le_sub_left hxR _
      _ ≤ ‖u‖ := htri
  have hu : 0 < ‖u‖ :=
    (div_pos hznorm (by norm_num)).trans_le hu_lower
  have hsem : ‖f u‖ ≤ A / ‖u‖ ^ k :=
    hdecay u (norm_pos_iff.mp hu)
  have hpow : (‖intVectorToReal z‖ / 2) ^ k ≤ ‖u‖ ^ k := by
    gcongr
  have hdiv : A / ‖u‖ ^ k ≤ A / (‖intVectorToReal z‖ / 2) ^ k :=
    div_le_div_of_nonneg_left hA (pow_pos (div_pos hznorm (by norm_num)) k) hpow
  calc
    ‖integerTranslate f z x‖ = ‖f u‖ := rfl
    _ ≤ A / ‖u‖ ^ k := hsem
    _ ≤ A / (‖intVectorToReal z‖ / 2) ^ k := hdiv
    _ = majorant z := by
      dsimp only [majorant]
      rw [Real.rpow_neg (norm_nonneg _) k, Real.rpow_natCast]
      field_simp
      rw [div_pow]
      field_simp

/-- Every Schwartz function has a locally normally convergent integral
periodization. -/
theorem SchwartzMap.locallyNormallySummableIntegerTranslates {n : ℕ}
    (f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) :
    LocallyNormallySummableIntegerTranslates
      (⟨f, f.continuous⟩ : C(EuclideanSpace ℝ (Fin n), ℂ)) := by
  classical
  intro K
  let k : ℕ := n + 1
  let A : ℝ := SchwartzMap.seminorm ℝ k 0 f
  have hA : 0 ≤ A := apply_nonneg _ _
  obtain ⟨R₀, hR₀⟩ := K.isCompact.isBounded.subset_closedBall
    (0 : EuclideanSpace ℝ (Fin n))
  let R : ℝ := max 0 R₀
  have hR : 0 ≤ R := le_max_left _ _
  have hKR : (K : Set (EuclideanSpace ℝ (Fin n))) ⊆
      Metric.closedBall 0 R :=
    hR₀.trans (Metric.closedBall_subset_closedBall (le_max_right _ _))
  let majorant : (Fin n → ℤ) → ℝ := fun z =>
    (A * 2 ^ k) * ‖intVectorToReal z‖ ^ (-(k : ℝ))
  have hk : (-(k : ℝ)) < -(n : ℝ) := by
    dsimp only [k]
    push_cast
    linarith
  have hmajorant : Summable majorant :=
    (summable_intVector_norm_rpow (-(k : ℝ)) hk).mul_left (A * 2 ^ k)
  apply Summable.of_norm_bounded_eventually hmajorant
  let bad : Set (Fin n → ℤ) :=
    {z | ‖intVectorToReal z‖ ≤ 2 * R}
  have hbad : bad.Finite := by
    let L := standardIntegerLattice n
    let e := intVectorEquivStandardIntegerLattice n
    have hfiniteL :
        (Metric.closedBall (0 : Fin n → ℝ) (2 * R) ∩ (L : Set (Fin n → ℝ))).Finite :=
      ZSpan.setFinite_inter (Pi.basisFun ℝ (Fin n))
        Metric.isBounded_closedBall
    refine Set.Finite.of_finite_image (f := fun z => ((e z : L) : Fin n → ℝ))
      (hfiniteL.subset ?_) ?_
    · rintro _ ⟨z, hz, rfl⟩
      constructor
      · rw [Metric.mem_closedBall, dist_zero_right]
        change ‖((e z : L) : Fin n → ℝ)‖ ≤ 2 * R
        rw [show ((e z : L) : Fin n → ℝ) = fun i => (z i : ℝ) by
          simpa [e, L] using coe_intVectorEquivStandardIntegerLattice z]
        refine (show ‖(fun i => (z i : ℝ))‖ ≤ ‖intVectorToReal z‖ by
          rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
          intro i
          simpa [intVectorToReal] using PiLp.norm_apply_le (intVectorToReal z) i).trans hz
      · exact SetLike.coe_mem _
    · intro z _ w _ h
      exact e.injective (Subtype.ext h)
  filter_upwards [hbad.compl_mem_cofinite] with z hz
  have hzlarge : 2 * R < ‖intVectorToReal z‖ := by
    simpa [bad] using hz
  have hznorm : 0 < ‖intVectorToReal z‖ :=
    (mul_nonneg (by norm_num) hR).trans_lt hzlarge
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  apply (ContinuousMap.norm_le _ (by positivity)).2
  rintro ⟨x, hx⟩
  have hxR : ‖x‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hKR hx
  let u := x + intVectorToReal z
  have hu_lower : ‖intVectorToReal z‖ / 2 ≤ ‖u‖ := by
    have htri : ‖intVectorToReal z‖ - ‖x‖ ≤ ‖u‖ := by
      simpa [u, add_comm] using norm_sub_norm_le (intVectorToReal z) (-x)
    calc
      ‖intVectorToReal z‖ / 2 ≤ ‖intVectorToReal z‖ - R := by linarith
      _ ≤ ‖intVectorToReal z‖ - ‖x‖ := sub_le_sub_left hxR _
      _ ≤ ‖u‖ := htri
  have hu : 0 < ‖u‖ :=
    (div_pos hznorm (by norm_num)).trans_le hu_lower
  have hsem : ‖f u‖ ≤ A / ‖u‖ ^ k := by
    rw [le_div_iff₀ (pow_pos hu k)]
    simpa [A, mul_comm] using f.norm_pow_mul_le_seminorm ℝ k u
  have hpow : (‖intVectorToReal z‖ / 2) ^ k ≤ ‖u‖ ^ k := by
    gcongr
  have hdiv : A / ‖u‖ ^ k ≤ A / (‖intVectorToReal z‖ / 2) ^ k :=
    div_le_div_of_nonneg_left hA (pow_pos (div_pos hznorm (by norm_num)) k) hpow
  calc
    ‖integerTranslate (⟨f, f.continuous⟩ :
        ContinuousMap (EuclideanSpace ℝ (Fin n)) ℂ) z x‖ = ‖f u‖ := rfl
    _ ≤ A / ‖u‖ ^ k := hsem
    _ ≤ A / (‖intVectorToReal z‖ / 2) ^ k := hdiv
    _ = majorant z := by
      dsimp only [majorant]
      rw [Real.rpow_neg (norm_nonneg _) k, Real.rpow_natCast]
      field_simp
      rw [div_pow]
      field_simp

/-- The Euclidean Fourier transform of a Schwartz function is absolutely
summable on the dual coordinate lattice. -/
theorem SchwartzMap.summable_fourier_intVector {n : ℕ}
    (f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) :
    Summable fun m : Fin n → ℤ =>
      𝓕 (f : EuclideanSpace ℝ (Fin n) → ℂ) (intVectorToReal m) := by
  let F : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ := 𝓕 f
  have hlocal :=
    SRG266.Lattice.SchwartzMap.locallyNormallySummableIntegerTranslates F
  have hsum := summable_integerValues_of_locallyNormal
    (⟨F, F.continuous⟩ : ContinuousMap (EuclideanSpace ℝ (Fin n)) ℂ) hlocal
  refine hsum.congr fun m => ?_
  change (𝓕 f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ)
      (intVectorToReal m) =
    𝓕 (f : EuclideanSpace ℝ (Fin n) → ℂ) (intVectorToReal m)
  exact congrFun (SchwartzMap.fourier_coe f) (intVectorToReal m)

end SRG266.Lattice
