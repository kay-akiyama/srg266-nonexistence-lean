/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.RealLatticeCoordinates
import SRG266.Lattice.MultivariatePoisson
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# A unimodular lattice inside standard Euclidean space

The positive square root of the real Gram matrix gives a determinant-one
linear equivalence of standard Euclidean space.  Its image of `Z^n` realizes
the original integral pairing.  Unimodularity supplies an explicit integer
reindexing of the dual lattice.
-/

noncomputable section

namespace SRG266.Lattice

open scoped Matrix RealInnerProductSpace

variable {n : ℕ}

/-- The determinant-one Euclidean realization associated to the chosen
integral basis of `L`. -/
noncomputable def pdEuclideanEquiv (L : PDUnimodularLattice n) :
    EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  Matrix.toLinearEquiv (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (pdSqrtGram L)
    ((Matrix.isUnit_iff_isUnit_det (pdSqrtGram L)).mp (pdSqrtGram_isUnit L))

/-- The underlying map is multiplication by the square-root Gram matrix in
Euclidean coordinates. -/
theorem pdEuclideanEquiv_toLinearMap (L : PDUnimodularLattice n) :
    (pdEuclideanEquiv L :
      EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) =
      Matrix.toEuclideanLin (pdSqrtGram L) := by
  rfl

@[simp]
theorem pdEuclideanEquiv_apply_toLp (L : PDUnimodularLattice n)
    (x : Fin n → ℝ) :
    pdEuclideanEquiv L (WithLp.toLp 2 x) =
      WithLp.toLp 2 (Matrix.mulVec (pdSqrtGram L) x) := by
  rfl

/-- The Euclidean realization has determinant one. -/
theorem pdEuclideanEquiv_det_eq_one (L : PDUnimodularLattice n) :
    LinearMap.det (pdEuclideanEquiv L :
      EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) = 1 := by
  change LinearMap.det
      (Matrix.toLin (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin n) ℝ).toBasis (pdSqrtGram L)) = 1
  rw [LinearMap.det_toLin, pdSqrtGram_det_eq_one]

/-- The Euclidean inner product of two realized integral coordinate vectors
is the original integral Gram pairing, cast to the reals. -/
theorem inner_pdEuclideanEquiv_intVector
    (L : PDUnimodularLattice n) (x y : Fin n → ℤ) :
    inner ℝ
        (pdEuclideanEquiv L (intVectorToReal x))
      (pdEuclideanEquiv L (intVectorToReal y)) =
      (L.pairing (pdCoordEquiv L x) (pdCoordEquiv L y) : ℝ) := by
  change inner ℝ
      (pdEuclideanEquiv L (WithLp.toLp 2 (fun i => (x i : ℝ))))
      (pdEuclideanEquiv L (WithLp.toLp 2 (fun i => (y i : ℝ)))) = _
  rw [pdEuclideanEquiv_apply_toLp, pdEuclideanEquiv_apply_toLp,
    PiLp.inner_apply]
  simp only [Real.inner_apply]
  change dotProduct
      (Matrix.mulVec (pdSqrtGram L) (fun i => (x i : ℝ)))
      (Matrix.mulVec (pdSqrtGram L) (fun i => (y i : ℝ))) = _
  change dotProduct
      (pdSqrtEquiv L (fun i => (x i : ℝ)))
      (pdSqrtEquiv L (fun i => (y i : ℝ))) = _
  rw [dotProduct_pdSqrtEquiv]
  have h := pdRatForm_intCoords L x y
  simp only [pdRatForm, Matrix.toBilin'_apply, pdRealGram_apply,
    intCoordsToRat_apply] at h ⊢
  exact_mod_cast h

/-- In particular, squared Euclidean norm of a realized lattice point is
the integral norm of the corresponding lattice vector. -/
theorem norm_sq_pdEuclideanEquiv_intVector
    (L : PDUnimodularLattice n) (x : Fin n → ℤ) :
    ‖pdEuclideanEquiv L (intVectorToReal x)‖ ^ 2 =
      (L.pairing (pdCoordEquiv L x) (pdCoordEquiv L x) : ℝ) := by
  rw [@norm_sq_eq_re_inner ℝ]
  simpa using inner_pdEuclideanEquiv_intVector L x x

/-- The realization is self-adjoint because the positive square-root Gram
matrix is symmetric. -/
theorem pdEuclideanEquiv_adjoint_eq (L : PDUnimodularLattice n) :
    (pdEuclideanEquiv L :
      EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).adjoint =
      (pdEuclideanEquiv L :
        EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) := by
  have hstar : (pdSqrtGram L).conjTranspose = pdSqrtGram L := by
    ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial]
    exact (pdSqrtGram_isSymm L).apply i j
  have h := Matrix.toEuclideanLin_conjTranspose_eq_adjoint (pdSqrtGram L)
  rw [hstar] at h
  simpa only [pdEuclideanEquiv_toLinearMap] using h.symm

/-- The inverse realization is also self-adjoint. -/
theorem pdEuclideanEquiv_symm_adjoint_eq (L : PDUnimodularLattice n) :
    ((pdEuclideanEquiv L).symm :
      EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).adjoint =
      ((pdEuclideanEquiv L).symm :
        EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) := by
  let A := pdEuclideanEquiv L
  have hsymm : (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin n)).IsSymmetric := by
    intro x y
    calc
      inner ℝ (A x) y =
          inner ℝ x
            ((A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
              EuclideanSpace ℝ (Fin n)).adjoint y) :=
        (LinearMap.adjoint_inner_right
          (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
            EuclideanSpace ℝ (Fin n)) x y).symm
      _ = inner ℝ x (A y) := by
        dsimp only [A]
        rw [pdEuclideanEquiv_adjoint_eq]
        rfl
  apply LinearMap.IsSymmetric.adjoint_eq
  intro x y
  calc
    inner ℝ (A.symm x) y = inner ℝ (A.symm x) (A (A.symm y)) := by
      rw [A.apply_symm_apply]
    _ = inner ℝ (A (A.symm x)) (A.symm y) := (hsymm _ _).symm
    _ = inner ℝ x (A.symm y) := by rw [A.apply_symm_apply]

/-- Two applications of the square-root realization, with the inverse Gram
integer reindexing inserted, give back the original integer vector. -/
theorem pdEuclideanEquiv_apply_apply_inverseGram
    (L : PDUnimodularLattice n) (x : Fin n → ℤ) :
    pdEuclideanEquiv L
        (pdEuclideanEquiv L
          (intVectorToReal ((pdGramCoordEquiv L).symm x))) =
      intVectorToReal x := by
  change pdEuclideanEquiv L
      (pdEuclideanEquiv L
        (WithLp.toLp 2 (fun i => (((pdGramCoordEquiv L).symm x i : ℤ) : ℝ)))) =
    WithLp.toLp 2 (fun i => (x i : ℝ))
  rw [pdEuclideanEquiv_apply_toLp, pdEuclideanEquiv_apply_toLp]
  exact congrArg (WithLp.toLp 2)
    (pdSqrtGram_mulVec_mulVec_equiv_symm_cast L x)

/-- **Concrete self-duality.**  The adjoint inverse sends a standard integer
frequency to the realized lattice point indexed by the inverse integral Gram
automorphism. -/
theorem pdEuclideanEquiv_symm_adjoint_intVector
    (L : PDUnimodularLattice n) (x : Fin n → ℤ) :
    ((pdEuclideanEquiv L).symm :
      EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).adjoint
        (intVectorToReal x) =
      pdEuclideanEquiv L
        (intVectorToReal ((pdGramCoordEquiv L).symm x)) := by
  rw [pdEuclideanEquiv_symm_adjoint_eq]
  change (pdEuclideanEquiv L).symm (intVectorToReal x) =
    pdEuclideanEquiv L
      (intVectorToReal ((pdGramCoordEquiv L).symm x))
  apply (pdEuclideanEquiv L).injective
  simpa using (pdEuclideanEquiv_apply_apply_inverseGram L x).symm

end SRG266.Lattice
