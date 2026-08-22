/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Lattice.CoordinateRationalLattice
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Topology.Algebra.Order.Archimedean

/-!
# Euclidean coordinates for a positive-definite unimodular lattice

This file extends the rational coordinate model of an integral lattice to
real coordinates.  Unimodularity gives an integral unit determinant.  Rational
positive definiteness first gives nonnegativity over the reals by density; the
unit determinant then upgrades it to strict positive definiteness.  Finally
the positive square root of the Gram matrix realizes the lattice in standard
Euclidean space.
-/

noncomputable section

namespace SRG266.Lattice

open scoped Matrix MatrixOrder

variable {n : ℕ}

/-- The adjoint of the lattice pairing, bundled as an equivalence by
unimodularity. -/
noncomputable def pdPairingEquiv (L : PDUnimodularLattice n) :
    L.carrier ≃ₗ[ℤ] Module.Dual ℤ L.carrier :=
  LinearEquiv.ofBijective L.pairing L.unimodular

/-- In the chosen basis and its dual basis, the pairing map has the Gram
matrix.  Symmetry removes the transpose introduced by the dual convention. -/
theorem pdPairing_toMatrix (L : PDUnimodularLattice n) :
    LinearMap.toMatrix (pdFinBasis L) (pdFinBasis L).dualBasis
        L.pairing =
      pdGram L := by
  ext i j
  simp only [LinearMap.toMatrix_apply, Module.Basis.dualBasis_repr,
    pdGram, LinearMap.BilinForm.toMatrix_apply]
  exact L.symmetric.eq (pdFinBasis L j) (pdFinBasis L i)

/-- The Gram determinant of a unimodular lattice is a unit in `ℤ`. -/
theorem pdGram_det_isUnit (L : PDUnimodularLattice n) :
    IsUnit (pdGram L).det := by
  have he := (pdPairingEquiv L).isUnit_det
    (pdFinBasis L) (pdFinBasis L).dualBasis
  change IsUnit (LinearMap.toMatrix (pdFinBasis L)
    (pdFinBasis L).dualBasis L.pairing).det at he
  rw [pdPairing_toMatrix] at he
  exact he

/-- The integral Gram matrix as an automorphism of coordinate vectors. -/
noncomputable def pdGramCoordEquiv (L : PDUnimodularLattice n) :
    (Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ) :=
  (pdFinBasis L).equivFun.symm |>.trans <|
    (pdPairingEquiv L |>.trans (pdFinBasis L).dualBasis.equivFun)

/-- The coordinate pairing automorphism acts by multiplication with the Gram
matrix. -/
theorem pdGramCoordEquiv_apply (L : PDUnimodularLattice n)
    (x : Fin n → ℤ) :
    pdGramCoordEquiv L x = Matrix.mulVec (pdGram L) x := by
  have h := LinearMap.toMatrix_mulVec_repr (pdFinBasis L)
    (pdFinBasis L).dualBasis L.pairing ((pdFinBasis L).equivFun.symm x)
  rw [pdPairing_toMatrix] at h
  have hx :
      ⇑((pdFinBasis L).repr ((pdFinBasis L).equivFun.symm x)) = x := by
    simpa only [Module.Basis.equivFun_apply] using
      (pdFinBasis L).equivFun.apply_symm_apply x
  rw [hx] at h
  simpa [pdGramCoordEquiv, pdPairingEquiv] using h.symm

/-- Multiplication by the Gram matrix followed by the integral inverse
coordinate automorphism is the identity. -/
theorem pdGram_mulVec_equiv_symm (L : PDUnimodularLattice n)
    (x : Fin n → ℤ) :
    Matrix.mulVec (pdGram L) ((pdGramCoordEquiv L).symm x) = x := by
  rw [← pdGramCoordEquiv_apply]
  exact (pdGramCoordEquiv L).apply_symm_apply x

/-- The real Gram matrix in the chosen integral basis. -/
noncomputable def pdRealGram (L : PDUnimodularLattice n) :
    Matrix (Fin n) (Fin n) ℝ :=
  (pdGram L).map (Int.castRingHom ℝ)

@[simp]
theorem pdRealGram_apply (L : PDUnimodularLattice n) (i j : Fin n) :
    pdRealGram L i j = (pdGram L i j : ℝ) := rfl

/-- The real Gram determinant is nonzero (indeed it will be `1`). -/
theorem pdRealGram_det_ne_zero (L : PDUnimodularLattice n) :
    (pdRealGram L).det ≠ 0 := by
  change ((pdGram L).map (fun x : ℤ => (x : ℝ))).det ≠ 0
  rw [← Int.cast_det]
  exact_mod_cast (pdGram_det_isUnit L).ne_zero

/-- The real Gram matrix is invertible. -/
theorem pdRealGram_isUnit (L : PDUnimodularLattice n) :
    IsUnit (pdRealGram L) :=
  (Matrix.isUnit_iff_isUnit_det (pdRealGram L)).mpr
    (isUnit_iff_ne_zero.mpr (pdRealGram_det_ne_zero L))

/-- The real Gram matrix is Hermitian. -/
theorem pdRealGram_isHermitian (L : PDUnimodularLattice n) :
    (pdRealGram L).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  simp only [pdRealGram_apply]
  exact congrArg (fun z : ℤ => (z : ℝ)) <| by
    simpa only [pdGram, LinearMap.BilinForm.toMatrix_apply] using
      L.symmetric.eq (pdFinBasis L j) (pdFinBasis L i)

/-- Rational coordinate vectors are dense in real coordinate space. -/
theorem denseRange_ratPiCast :
    DenseRange (fun q : Fin n → ℚ => fun i => (q i : ℝ)) := by
  let f : (Fin n → ℚ) → (Fin n → ℝ) :=
    Pi.map fun _ : Fin n => ((↑) : ℚ → ℝ)
  have hf : DenseRange f :=
    DenseRange.piMap (fun _ : Fin n => Rat.denseRange_cast)
  have hfun : f = (fun q : Fin n → ℚ => fun i => (q i : ℝ)) := by
    funext q i
    rfl
  rwa [← hfun]

/-- The real Gram quadratic form agrees with the rational one on rational
coordinate vectors. -/
theorem pdRealGram_ratCast (L : PDUnimodularLattice n) (q : Fin n → ℚ) :
    dotProduct (fun i => (q i : ℝ))
        (Matrix.mulVec (pdRealGram L) (fun i => (q i : ℝ))) =
      (pdRatForm L q q : ℝ) := by
  simp only [dotProduct, Matrix.mulVec, pdRealGram_apply,
    pdRatForm, Matrix.toBilin'_apply]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The real Gram matrix is positive semidefinite.  Strict positivity on
rational vectors supplies nonnegativity on all real vectors by density. -/
theorem pdRealGram_posSemidef (L : PDUnimodularLattice n) :
    (pdRealGram L).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨pdRealGram_isHermitian L, ?_⟩
  simp only [star_trivial]
  intro x
  refine denseRange_ratPiCast.induction_on x ?_ ?_
  · have hcont : Continuous (fun b : Fin n → ℝ =>
        dotProduct b (Matrix.mulVec (pdRealGram L) b)) := by
      simp only [dotProduct, Matrix.mulVec]
      fun_prop
    have hset :
        {b : Fin n → ℝ | 0 ≤ dotProduct b (Matrix.mulVec (pdRealGram L) b)} =
          (fun b => dotProduct b (Matrix.mulVec (pdRealGram L) b)) ⁻¹' Set.Ici 0 := by
      ext b
      rfl
    rw [hset]
    exact isClosed_Ici.preimage hcont
  · intro q
    rw [pdRealGram_ratCast]
    by_cases hq : q = 0
    · simp [hq]
    · exact_mod_cast (pdRatForm_posDef L q hq).le

/-- The real Gram matrix is positive definite. -/
theorem pdRealGram_posDef (L : PDUnimodularLattice n) :
    (pdRealGram L).PosDef :=
  (pdRealGram_posSemidef L).posDef_iff_isUnit.mpr (pdRealGram_isUnit L)

/-- Positivity selects `+1` from the two possible integral unit
determinants. -/
theorem pdRealGram_det_eq_one (L : PDUnimodularLattice n) :
    (pdRealGram L).det = 1 := by
  have hpos := (pdRealGram_posDef L).det_pos
  rcases Int.isUnit_iff.mp (pdGram_det_isUnit L) with hdet | hdet
  · change ((pdGram L).map (fun x : ℤ => (x : ℝ))).det = 1
    rw [← Int.cast_det, hdet]
    norm_num
  · exfalso
    change 0 < ((pdGram L).map (fun x : ℤ => (x : ℝ))).det at hpos
    rw [← Int.cast_det, hdet] at hpos
    norm_num at hpos

/-- The canonical positive square root of the real Gram matrix. -/
noncomputable def pdSqrtGram (L : PDUnimodularLattice n) :
    Matrix (Fin n) (Fin n) ℝ :=
  CFC.sqrt (pdRealGram L)

theorem pdSqrtGram_sq (L : PDUnimodularLattice n) :
    pdSqrtGram L * pdSqrtGram L = pdRealGram L := by
  simpa [pdSqrtGram, pow_two] using
    CFC.sq_sqrt (pdRealGram L) (pdRealGram_posSemidef L).nonneg

/-- The positive square root of a real symmetric matrix is symmetric. -/
theorem pdSqrtGram_isSymm (L : PDUnimodularLattice n) :
    (pdSqrtGram L).IsSymm := by
  rw [← Matrix.isHermitian_iff_isSymm]
  exact (CFC.sqrt_nonneg (pdRealGram L)).isSelfAdjoint

/-- The square-root realization has determinant one, hence no covolume
factor occurs in Poisson summation. -/
theorem pdSqrtGram_det_eq_one (L : PDUnimodularLattice n) :
    (pdSqrtGram L).det = 1 := by
  have hdet := (pdRealGram_posSemidef L).det_sqrt
  simpa [pdSqrtGram, pdRealGram_det_eq_one] using hdet

theorem pdSqrtGram_isUnit (L : PDUnimodularLattice n) :
    IsUnit (pdSqrtGram L) := by
  rw [pdSqrtGram,
    CFC.isUnit_sqrt_iff (pdRealGram L) (pdRealGram_posSemidef L).nonneg]
  exact pdRealGram_isUnit L

/-- The square-root Gram matrix as a real linear equivalence. -/
noncomputable def pdSqrtEquiv (L : PDUnimodularLattice n) :
    (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
  Matrix.toLinearEquiv (Pi.basisFun ℝ (Fin n)) (pdSqrtGram L)
    ((Matrix.isUnit_iff_isUnit_det (pdSqrtGram L)).mp (pdSqrtGram_isUnit L))

@[simp]
theorem pdSqrtEquiv_apply (L : PDUnimodularLattice n) (x : Fin n → ℝ) :
    pdSqrtEquiv L x = Matrix.mulVec (pdSqrtGram L) x := by
  change Matrix.toLin (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin n))
      (pdSqrtGram L) x = Matrix.mulVec (pdSqrtGram L) x
  rw [Matrix.toLin_eq_toLin']
  rfl

/-- The linear determinant of the square-root equivalence is one. -/
theorem pdSqrtEquiv_det_eq_one (L : PDUnimodularLattice n) :
    LinearMap.det (pdSqrtEquiv L : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) = 1 := by
  change LinearMap.det
      (Matrix.toLin (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin n))
        (pdSqrtGram L)) = 1
  rw [LinearMap.det_toLin, pdSqrtGram_det_eq_one]

/-- The integral inverse Gram automorphism remains an inverse after casting
coordinates to `ℝ`. -/
theorem pdRealGram_mulVec_equiv_symm_cast (L : PDUnimodularLattice n)
    (x : Fin n → ℤ) :
    Matrix.mulVec (pdRealGram L)
        (fun i => (((pdGramCoordEquiv L).symm x i : ℤ) : ℝ)) =
      (fun i => (x i : ℝ)) := by
  ext i
  have hi := congrFun (pdGram_mulVec_equiv_symm L x) i
  simp only [Matrix.mulVec, dotProduct, pdRealGram_apply] at *
  exact_mod_cast hi

/-- Applying the square-root realization twice to an inverse-Gram integer
coordinate vector returns the original integer vector.  This is the concrete
self-duality identity needed to reindex the Fourier side of Poisson
summation. -/
theorem pdSqrtGram_mulVec_mulVec_equiv_symm_cast
    (L : PDUnimodularLattice n) (x : Fin n → ℤ) :
    Matrix.mulVec (pdSqrtGram L)
        (Matrix.mulVec (pdSqrtGram L)
          (fun i => (((pdGramCoordEquiv L).symm x i : ℤ) : ℝ))) =
      (fun i => (x i : ℝ)) := by
  rw [Matrix.mulVec_mulVec, pdSqrtGram_sq]
  exact pdRealGram_mulVec_equiv_symm_cast L x

/-- The square-root equivalence realizes the Gram form as the standard dot
product. -/
theorem dotProduct_pdSqrtEquiv (L : PDUnimodularLattice n)
    (x y : Fin n → ℝ) :
    dotProduct (pdSqrtEquiv L x) (pdSqrtEquiv L y) =
      Matrix.toBilin' (pdRealGram L) x y := by
  simp only [pdSqrtEquiv_apply, Matrix.toBilin'_apply']
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec,
    (pdSqrtGram_isSymm L).eq, pdSqrtGram_sq,
    ← Matrix.dotProduct_mulVec]

end SRG266.Lattice
