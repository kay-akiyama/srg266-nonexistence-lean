/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.RationalSpace

/-!
# Positive definiteness of the local Gram form, and its rank

This file gives an exact integral sum-of-squares certificate for the local Gram
matrix `L`. With `P = localSupportNumerator G x = 11 L - 6 J`,
`P * P = 495 • P` (`localSupportNumerator_sq`), and therefore, over any
commutative ring,

`5445 * (aᵀ L a) = ‖P *ᵥ a‖² + 2970 * (∑ B, a B)²`.

Both summands on the right are visibly non-negative in an ordered ring, and they
vanish simultaneously only when `L *ᵥ a = 0`.  This gives positive definiteness
of the induced forms on `IntegralGramLattice G x` and on `ratGramSpace G x` with
no analysis at all, and it works verbatim over `ℤ` and over `ℚ`.

The file also proves `Module.finrank ℤ (IntegralGramLattice G x) = 12`.
-/

open scoped Matrix

namespace SRG266

/-! ### The abstract sum-of-squares certificate -/

section GenericSOS

variable {R ι : Type*} [CommRing R] [Fintype ι]

theorem allOnes_mulVec (a : ι → R) :
    (allOnesMatrix : Matrix ι ι R) *ᵥ a = fun _ => ∑ i, a i := by
  funext i
  show (∑ j, (1 : R) * a j) = ∑ i, a i
  simp

theorem dotProduct_allOnes_mulVec (a : ι → R) :
    a ⬝ᵥ ((allOnesMatrix : Matrix ι ι R) *ᵥ a) = (∑ i, a i) ^ 2 := by
  rw [allOnes_mulVec]
  show (∑ i, a i * ∑ j, a j) = (∑ i, a i) ^ 2
  rw [← Finset.sum_mul, sq]

/-- **The sum-of-squares identity.**  If `P = 11 L - 6 J` is a `495`-scaled
idempotent, the quadratic form of `L` is an explicit non-negative combination of
a sum of squares and the square of the coordinate sum. -/
theorem dotProduct_mulVec_sos {L P : Matrix ι ι R}
    (hP : P = (11 : R) • L - (6 : R) • (allOnesMatrix : Matrix ι ι R))
    (hPP : P * P = (495 : R) • P) (hPsym : P.IsSymm) (a : ι → R) :
    5445 * (a ⬝ᵥ (L *ᵥ a)) =
      (P *ᵥ a) ⬝ᵥ (P *ᵥ a) + 2970 * (∑ i, a i) ^ 2 := by
  have hswap : P *ᵥ a = a ᵥ* P := (vecMul_eq_mulVec_of_isSymm hPsym a).symm
  have hsq : (P *ᵥ a) ⬝ᵥ (P *ᵥ a) = 495 * (a ⬝ᵥ (P *ᵥ a)) := by
    calc (P *ᵥ a) ⬝ᵥ (P *ᵥ a)
        = ((P *ᵥ a) ᵥ* P) ⬝ᵥ a := Matrix.dotProduct_mulVec _ _ _
      _ = ((a ᵥ* P) ᵥ* P) ⬝ᵥ a := by rw [← hswap]
      _ = (a ᵥ* (P * P)) ⬝ᵥ a := by rw [Matrix.vecMul_vecMul]
      _ = a ⬝ᵥ ((P * P) *ᵥ a) := (Matrix.dotProduct_mulVec _ _ _).symm
      _ = a ⬝ᵥ (((495 : R) • P) *ᵥ a) := by rw [hPP]
      _ = 495 * (a ⬝ᵥ (P *ᵥ a)) := by
          rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hlin : a ⬝ᵥ (P *ᵥ a) =
      11 * (a ⬝ᵥ (L *ᵥ a)) - 6 * (∑ i, a i) ^ 2 := by
    rw [hP, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.smul_mulVec,
      dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      dotProduct_allOnes_mulVec]
  rw [hsq, hlin]
  ring

variable [LinearOrder R] [IsStrictOrderedRing R]

theorem dotProduct_mulVec_nonneg {L P : Matrix ι ι R}
    (hP : P = (11 : R) • L - (6 : R) • (allOnesMatrix : Matrix ι ι R))
    (hPP : P * P = (495 : R) • P) (hPsym : P.IsSymm) (a : ι → R) :
    0 ≤ a ⬝ᵥ (L *ᵥ a) := by
  have hsos := dotProduct_mulVec_sos hP hPP hPsym a
  have h1 : (0 : R) ≤ (P *ᵥ a) ⬝ᵥ (P *ᵥ a) :=
    Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have h2 : (0 : R) ≤ (∑ i, a i) ^ 2 := sq_nonneg _
  linarith

theorem dotProduct_mulVec_eq_zero {L P : Matrix ι ι R}
    (hP : P = (11 : R) • L - (6 : R) • (allOnesMatrix : Matrix ι ι R))
    (hPP : P * P = (495 : R) • P) (hPsym : P.IsSymm) (a : ι → R)
    (ha : a ⬝ᵥ (L *ᵥ a) = 0) : L *ᵥ a = 0 := by
  have hsos := dotProduct_mulVec_sos hP hPP hPsym a
  rw [ha, mul_zero] at hsos
  have h1 : (0 : R) ≤ (P *ᵥ a) ⬝ᵥ (P *ᵥ a) :=
    Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have h2 : (0 : R) ≤ (∑ i, a i) ^ 2 := sq_nonneg _
  have hsum : (∑ i, a i) = 0 := by
    have : (∑ i, a i) ^ 2 = 0 := by linarith
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  have hzero : (P *ᵥ a) ⬝ᵥ (P *ᵥ a) = 0 := by linarith
  have hPa : P *ᵥ a = 0 := by
    funext i
    have hterm : ∀ j ∈ (Finset.univ : Finset ι), (P *ᵥ a) j * (P *ᵥ a) j = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ => mul_self_nonneg _).mp hzero
    have := hterm i (Finset.mem_univ i)
    simpa using mul_self_eq_zero.mp this
  have hexp : P *ᵥ a = (11 : R) • (L *ᵥ a) - (6 : R) • (fun _ : ι => ∑ i, a i) := by
    rw [hP, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, allOnes_mulVec]
  rw [hexp] at hPa
  funext i
  have hi := congrFun hPa i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hsum,
    mul_zero, sub_zero] at hi
  show (L *ᵥ a) i = 0
  linarith

end GenericSOS

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### The hypotheses of the certificate, over `ℤ` and over `ℚ` -/

theorem localSupportNumerator_eq_zsmul (x : V) :
    localSupportNumerator G x =
      (11 : ℤ) • localGramMatrix G x -
        (6 : ℤ) • (allOnesMatrix :
          Matrix (SecondSubconstituent G x) (SecondSubconstituent G x) ℤ) := by
  ext B C
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, allOnesMatrix_apply,
    mul_one]
  rfl

theorem localSupportNumerator_sq_zsmul (hG : IsHypothetical G) (x : V) :
    localSupportNumerator G x * localSupportNumerator G x =
      (495 : ℤ) • localSupportNumerator G x := by
  ext B C
  rw [localSupportNumerator_sq_apply G hG x B C, Matrix.smul_apply, smul_eq_mul]

theorem localSupportNumerator_isSymm (x : V) : (localSupportNumerator G x).IsSymm :=
  Matrix.IsSymm.ext fun B C => by
    simp only [localSupportNumerator, localGramMatrix_comm G x C B]

/-- The rational scalar extension of the support numerator. -/
def localSupportNumeratorRat (x : V) :
    Matrix (SecondSubconstituent G x) (SecondSubconstituent G x) ℚ :=
  fun B C => (localSupportNumerator G x B C : ℚ)

theorem localSupportNumeratorRat_eq_smul (x : V) :
    localSupportNumeratorRat G x =
      (11 : ℚ) • localGramMatrixRat G x -
        (6 : ℚ) • (allOnesMatrix :
          Matrix (SecondSubconstituent G x) (SecondSubconstituent G x) ℚ) := by
  ext B C
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, allOnesMatrix_apply,
    mul_one]
  show ((11 * localGramMatrix G x B C - 6 : ℤ) : ℚ) =
    11 * ((localGramMatrix G x B C : ℤ) : ℚ) - 6
  push_cast
  ring

theorem localSupportNumeratorRat_sq (hG : IsHypothetical G) (x : V) :
    localSupportNumeratorRat G x * localSupportNumeratorRat G x =
      (495 : ℚ) • localSupportNumeratorRat G x := by
  ext B C
  have h := localSupportNumerator_sq_apply G hG x B C
  rw [Matrix.mul_apply] at h
  rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  show (∑ D, ((localSupportNumerator G x B D : ℤ) : ℚ) *
      ((localSupportNumerator G x D C : ℤ) : ℚ)) =
    495 * ((localSupportNumerator G x B C : ℤ) : ℚ)
  rw [show (∑ D, ((localSupportNumerator G x B D : ℤ) : ℚ) *
        ((localSupportNumerator G x D C : ℤ) : ℚ)) =
      ((∑ D, localSupportNumerator G x B D * localSupportNumerator G x D C : ℤ) : ℚ) by
    push_cast; rfl]
  rw [h]
  push_cast
  ring

theorem localSupportNumeratorRat_isSymm (x : V) :
    (localSupportNumeratorRat G x).IsSymm :=
  Matrix.IsSymm.ext fun B C => by
    show ((localSupportNumerator G x C B : ℤ) : ℚ) =
      ((localSupportNumerator G x B C : ℤ) : ℚ)
    simp only [localSupportNumerator, localGramMatrix_comm G x C B]

/-! ### The sum-of-squares identity for the local Gram matrix -/

/-- The integral sum-of-squares certificate for the local Gram form. -/
theorem localGram_sos (hG : IsHypothetical G) (x : V)
    (a : SecondSubconstituent G x → ℤ) :
    5445 * (a ⬝ᵥ (localGramMatrix G x *ᵥ a)) =
      (localSupportNumerator G x *ᵥ a) ⬝ᵥ (localSupportNumerator G x *ᵥ a) +
        2970 * (∑ B, a B) ^ 2 :=
  dotProduct_mulVec_sos (localSupportNumerator_eq_zsmul G x)
    (localSupportNumerator_sq_zsmul G hG x) (localSupportNumerator_isSymm G x) a

/-- The rational sum-of-squares certificate for the local Gram form. -/
theorem localGramRat_sos (hG : IsHypothetical G) (x : V)
    (a : SecondSubconstituent G x → ℚ) :
    5445 * (a ⬝ᵥ (localGramMatrixRat G x *ᵥ a)) =
      (localSupportNumeratorRat G x *ᵥ a) ⬝ᵥ (localSupportNumeratorRat G x *ᵥ a) +
        2970 * (∑ B, a B) ^ 2 :=
  dotProduct_mulVec_sos (localSupportNumeratorRat_eq_smul G x)
    (localSupportNumeratorRat_sq G hG x) (localSupportNumeratorRat_isSymm G x) a

theorem localGram_quadratic_nonneg (hG : IsHypothetical G) (x : V)
    (a : SecondSubconstituent G x → ℤ) :
    0 ≤ a ⬝ᵥ (localGramMatrix G x *ᵥ a) :=
  dotProduct_mulVec_nonneg (localSupportNumerator_eq_zsmul G x)
    (localSupportNumerator_sq_zsmul G hG x) (localSupportNumerator_isSymm G x) a

theorem localGram_quadratic_eq_zero_iff (hG : IsHypothetical G) (x : V)
    (a : SecondSubconstituent G x → ℤ) :
    a ⬝ᵥ (localGramMatrix G x *ᵥ a) = 0 ↔ localGramMatrix G x *ᵥ a = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, dotProduct_zero]⟩
  exact dotProduct_mulVec_eq_zero (localSupportNumerator_eq_zsmul G x)
    (localSupportNumerator_sq_zsmul G hG x) (localSupportNumerator_isSymm G x) a h

theorem localGramRat_quadratic_nonneg (hG : IsHypothetical G) (x : V)
    (a : SecondSubconstituent G x → ℚ) :
    0 ≤ a ⬝ᵥ (localGramMatrixRat G x *ᵥ a) :=
  dotProduct_mulVec_nonneg (localSupportNumeratorRat_eq_smul G x)
    (localSupportNumeratorRat_sq G hG x) (localSupportNumeratorRat_isSymm G x) a

theorem localGramRat_quadratic_eq_zero_iff (hG : IsHypothetical G) (x : V)
    (a : SecondSubconstituent G x → ℚ) :
    a ⬝ᵥ (localGramMatrixRat G x *ᵥ a) = 0 ↔ localGramMatrixRat G x *ᵥ a = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, dotProduct_zero]⟩
  exact dotProduct_mulVec_eq_zero (localSupportNumeratorRat_eq_smul G x)
    (localSupportNumeratorRat_sq G hG x) (localSupportNumeratorRat_isSymm G x) a h

/-! ### Positive definiteness of the integral pairing -/

theorem integralGramPairing_mk (x : V) (a b : SecondSubconstituent G x → ℤ) :
    integralGramPairing G x (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) =
      a ⬝ᵥ (localGramMatrix G x *ᵥ b) :=
  Matrix.toBilin'_apply' _ _ _

theorem integralGramPairing_isSymm (x : V) : (integralGramPairing G x).IsSymm := by
  constructor
  intro v w
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  exact (integralGramForm_isSymm G x).eq v w

theorem integralGramPairing_nonneg (hG : IsHypothetical G) (x : V)
    (v : IntegralGramLattice G x) : 0 ≤ integralGramPairing G x v v := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  rw [integralGramPairing_mk]
  exact localGram_quadratic_nonneg G hG x a

/-- The integral Gram pairing is positive definite. -/
theorem integralGramPairing_posDef (hG : IsHypothetical G) (x : V)
    (v : IntegralGramLattice G x) (hv : v ≠ 0) :
    0 < integralGramPairing G x v v := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  rw [integralGramPairing_mk]
  rcases lt_or_eq_of_le (localGram_quadratic_nonneg G hG x a) with h | h
  · exact h
  · refine absurd ?_ hv
    rw [Submodule.Quotient.mk_eq_zero, ← integralGramKernel_eq_relations]
    exact LinearMap.mem_ker.mpr
      ((localGram_quadratic_eq_zero_iff G hG x a).mp h.symm)

theorem integralGramPairing_nondegenerate (hG : IsHypothetical G) (x : V) :
    (integralGramPairing G x).Nondegenerate :=
  (LinearMap.BilinForm.nondegenerate_iff' (integralGramPairing G x)
      (integralGramPairing_nonneg G hG x)
      (LinearMap.BilinForm.isSymm_iff.mp (integralGramPairing_isSymm G x))).mpr
    (integralGramPairing_posDef G hG x)

/-! ### The rank of the integral Gram lattice -/

/-- **The rank of the local integral Gram lattice is `12`.** -/
theorem finrank_integralGramLattice (hG : IsHypothetical G) (x : V) :
    Module.finrank ℤ (IntegralGramLattice G x) = 12 := by
  have h :
      Module.finrank ℤ (IntegralGramLattice G x) +
          Module.finrank ℤ (integralGramRelations G x) =
        Module.finrank ℤ (SecondSubconstituent G x → ℤ) :=
    (integralGramRelations G x).finrank_quotient_add_finrank
  have hker : Module.finrank ℤ (integralGramRelations G x) = 208 := by
    rw [← integralGramKernel_eq_relations]
    exact integralGramKernel_finrank G hG x
  rw [hker, Module.finrank_pi ℤ, secondSubconstituent_card G hG x] at h
  omega

/-! ### Nondegeneracy against the distinguished generators -/

theorem mk_eq_sum_smul_generator (x : V) (a : SecondSubconstituent G x → ℤ) :
    (Submodule.Quotient.mk a : IntegralGramLattice G x) =
      ∑ B, a B • integralGramGenerator G x B := by
  have hsum : (∑ B, a B • Pi.single B (1 : ℤ)) = a := by
    funext C
    simp [Pi.single_apply, Finset.sum_ite_eq]
  calc (Submodule.Quotient.mk a : IntegralGramLattice G x)
      = (integralGramRelations G x).mkQ (∑ B, a B • Pi.single B (1 : ℤ)) := by
        rw [hsum]; rfl
    _ = ∑ B, a B • integralGramGenerator G x B := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun B _ => by rw [map_smul]; rfl

theorem integralGramPairing_apply_mk_right (x : V)
    (v : IntegralGramLattice G x) (a : SecondSubconstituent G x → ℤ) :
    integralGramPairing G x v (Submodule.Quotient.mk a) =
      ∑ B, a B * integralGramPairing G x v (integralGramGenerator G x B) := by
  rw [mk_eq_sum_smul_generator G x a, map_sum]
  exact Finset.sum_congr rfl fun B _ => by rw [map_smul, smul_eq_mul]

/-- A lattice vector orthogonal to every distinguished generator is zero. -/
theorem eq_zero_of_pairing_generators_eq_zero (hG : IsHypothetical G) (x : V)
    (v : IntegralGramLattice G x)
    (h : ∀ B, integralGramPairing G x v (integralGramGenerator G x B) = 0) :
    v = 0 := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  have hzero :
      integralGramPairing G x (Submodule.Quotient.mk a)
        (Submodule.Quotient.mk a) = 0 := by
    rw [integralGramPairing_apply_mk_right]
    exact Finset.sum_eq_zero fun B _ => by rw [h B, mul_zero]
  by_contra hv
  exact (integralGramPairing_posDef G hG x _ hv).ne' hzero

/-! ### Positive definiteness of the rational form -/

theorem ratGramForm_nonneg (hG : IsHypothetical G) (x : V) (v : ratGramSpace G x) :
    0 ≤ ratGramForm G x v v := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  rw [ratGramForm_mk]
  exact localGramRat_quadratic_nonneg G hG x a

/-- The rational Gram form is positive definite. -/
theorem ratGramForm_posDef (hG : IsHypothetical G) (x : V)
    (v : ratGramSpace G x) (hv : v ≠ 0) : 0 < ratGramForm G x v v := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  rw [ratGramForm_mk]
  rcases lt_or_eq_of_le (localGramRat_quadratic_nonneg G hG x a) with h | h
  · exact h
  · refine absurd ?_ hv
    rw [Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_ker.mpr
      ((localGramRat_quadratic_eq_zero_iff G hG x a).mp h.symm)

theorem ratGramForm_nondegenerate (hG : IsHypothetical G) (x : V) :
    (ratGramForm G x).Nondegenerate :=
  (LinearMap.BilinForm.nondegenerate_iff' (ratGramForm G x)
      (ratGramForm_nonneg G hG x)
      (LinearMap.BilinForm.isSymm_iff.mp (ratGramForm_isSymm G x))).mpr
    (ratGramForm_posDef G hG x)

end SRG266
