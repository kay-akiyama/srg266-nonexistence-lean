/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.EvenNeighbor
import SRG266.Lattice.CharacteristicCentroid
import Mathlib.Algebra.Module.LocalizedModule.Int
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Rational coordinates for a bundled integral lattice

The standard even-neighbour construction is most convenient inside a rational
quadratic space.  This file puts an arbitrary `PDUnimodularLattice n` into
coordinates using a finite basis and proves, without a determinant:

* the coordinate copy of `Z^n` is a full lattice;
* its rational Gram form is symmetric and positive definite;
* it is self-dual exactly because the original pairing is unimodular;
* the coordinate embedding is an isometry on integral vectors.

Strict positivity on rational vectors is obtained by clearing all finitely
many denominators with mathlib's localized-module API.
-/

namespace SRG266.Lattice

open Module

/-! ## The standard integral lattice in rational coordinate space -/

/-- Coordinatewise inclusion of integer vectors into rational vectors. -/
def intCoordsToRat {n : ℕ} : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℚ) where
  toFun v i := (v i : ℚ)
  map_add' v w := by
    ext i
    change (((v + w) i : ℤ) : ℚ) = (v i : ℚ) + (w i : ℚ)
    simp
  map_smul' a v := by
    ext i
    change (((a • v) i : ℤ) : ℚ) = a • (v i : ℚ)
    simp only [Pi.smul_apply, zsmul_eq_mul]
    push_cast
    ring

@[simp]
theorem intCoordsToRat_apply {n : ℕ} (v : Fin n → ℤ) (i : Fin n) :
    intCoordsToRat v i = (v i : ℚ) := rfl

/-- The standard copy of `Z^n` inside `Q^n`. -/
def coordinateIntegerLattice (n : ℕ) : Submodule ℤ (Fin n → ℚ) :=
  LinearMap.range intCoordsToRat

theorem mem_coordinateIntegerLattice {n : ℕ} {v : Fin n → ℚ} :
    v ∈ coordinateIntegerLattice n ↔
      ∃ z : Fin n → ℤ, ∀ i, (z i : ℚ) = v i := by
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, fun _ => rfl⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, funext fun i => hz i⟩

theorem intCoordsToRat_mem {n : ℕ} (v : Fin n → ℤ) :
    intCoordsToRat v ∈ coordinateIntegerLattice n :=
  ⟨v, rfl⟩

/-- `Z^n` is a full lattice in `Q^n`. -/
theorem coordinateIntegerLattice_isLattice (n : ℕ) :
    IsLattice ℚ (coordinateIntegerLattice n) := by
  constructor
  · have htop : (⊤ : Submodule ℤ (Fin n → ℤ)).FG := Module.Finite.fg_top
    have hmap := htop.map intCoordsToRat
    rwa [Submodule.map_top] at hmap
  · refine top_unique ?_
    rw [← (Pi.basisFun ℚ (Fin n)).span_eq]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    refine Submodule.subset_span ?_
    refine ⟨fun j => if j = i then 1 else 0, funext fun j => ?_⟩
    by_cases hj : j = i <;> simp [hj]

/-! ## Coordinates attached to `PDUnimodularLattice` -/

variable {n : ℕ}

/-- A basis indexed by the bundled rank. -/
noncomputable def pdFinBasis (L : PDUnimodularLattice n) :
    Basis (Fin n) ℤ L.carrier := by
  letI := L.moduleFree
  letI := L.moduleFinite
  exact Module.finBasisOfFinrankEq ℤ L.carrier L.rank

/-- The integer Gram matrix in `pdFinBasis`. -/
noncomputable def pdGram (L : PDUnimodularLattice n) : Matrix (Fin n) (Fin n) ℤ :=
  LinearMap.BilinForm.toMatrix (pdFinBasis L) L.pairing

/-- The rational extension of the coordinate Gram form. -/
noncomputable def pdRatForm (L : PDUnimodularLattice n) :
    LinearMap.BilinForm ℚ (Fin n → ℚ) :=
  Matrix.toBilin' fun i j => ((pdGram L i j : ℤ) : ℚ)

/-- Integer coordinate vectors interpreted in the original lattice. -/
noncomputable def pdCoordEquiv (L : PDUnimodularLattice n) :
    (Fin n → ℤ) ≃ₗ[ℤ] L.carrier :=
  (pdFinBasis L).equivFun.symm

/-- The coordinate Gram form agrees with the original pairing on integral
vectors. -/
theorem pdRatForm_intCoords (L : PDUnimodularLattice n)
    (x y : Fin n → ℤ) :
    pdRatForm L (intCoordsToRat x) (intCoordsToRat y) =
      ((L.pairing (pdCoordEquiv L x) (pdCoordEquiv L y) : ℤ) : ℚ) := by
  have h := LinearMap.BilinForm.dotProduct_toMatrix_mulVec
    (b := pdFinBasis L) L.pairing x y
  simp only [pdRatForm, Matrix.toBilin'_apply, pdGram, pdCoordEquiv]
  rw [← h]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  push_cast
  simp only [intCoordsToRat_apply]
  ring_nf

theorem pdRatForm_isSymm (L : PDUnimodularLattice n) :
    (pdRatForm L).IsSymm := by
  constructor
  intro x y
  simp only [pdRatForm, Matrix.toBilin'_apply, pdGram]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [LinearMap.BilinForm.toMatrix_apply]
  rw [L.symmetric.eq (pdFinBasis L j) (pdFinBasis L i)]
  ring

/-- A common nonzero integer clears all coordinates of a rational vector. -/
theorem exists_intCoords_multiple (v : Fin n → ℚ) :
    ∃ d : nonZeroDivisors ℤ, ∃ z : Fin n → ℤ,
      ∀ i, (z i : ℚ) = (d.1 : ℚ) * v i := by
  obtain ⟨d, hd⟩ := IsLocalizedModule.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) (Algebra.linearMap ℤ ℚ) v
  refine ⟨d, fun i => (hd i).choose, ?_⟩
  intro i
  exact (hd i).choose_spec

/-- Positive definiteness extends from integral coordinates to rational
coordinates by clearing denominators. -/
theorem pdRatForm_posDef (L : PDUnimodularLattice n) :
    ∀ v : Fin n → ℚ, v ≠ 0 → 0 < pdRatForm L v v := by
  intro v hv
  obtain ⟨d, z, hz⟩ := exists_intCoords_multiple v
  have hd0 : (d.1 : ℚ) ≠ 0 := by
    exact_mod_cast nonZeroDivisors.coe_ne_zero d
  have hzfun : intCoordsToRat z = (d.1 : ℚ) • v := by
    funext i
    exact hz i
  have hz0 : z ≠ 0 := by
    intro hzero
    apply hv
    funext i
    have hi := hz i
    rw [hzero] at hi
    simp only [Pi.zero_apply, Int.cast_zero] at hi
    exact (mul_eq_zero.mp hi.symm).resolve_left hd0
  have he0 : pdCoordEquiv L z ≠ 0 := by
    simpa using (pdCoordEquiv L).injective.ne hz0
  have hposZ := L.positiveDefinite (pdCoordEquiv L z) he0
  have hratZ : 0 < pdRatForm L (intCoordsToRat z) (intCoordsToRat z) := by
    rw [pdRatForm_intCoords]
    exact_mod_cast hposZ
  rw [hzfun] at hratZ
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at hratZ
  have hdpos : 0 < (d.1 : ℚ) ^ 2 := sq_pos_of_ne_zero hd0
  nlinarith

/-- The coordinate integral lattice is self-dual for the rational Gram form.
No determinant is used: an integral functional is transported through the
chosen basis and represented by `L.unimodular`. -/
theorem pdRatForm_dual_coordinateIntegerLattice (L : PDUnimodularLattice n) :
    (pdRatForm L).dualSubmodule (coordinateIntegerLattice n) =
      coordinateIntegerLattice n := by
  apply le_antisymm
  · intro v hv
    let coeff : Fin n → ℤ := fun i =>
      (mem_one_iff.mp (hv (intCoordsToRat (Pi.single i 1))
        (intCoordsToRat_mem (Pi.single i 1)))).choose
    have hcoeff : ∀ i,
        ((coeff i : ℤ) : ℚ) =
          pdRatForm L v (intCoordsToRat (Pi.single i 1)) := by
      intro i
      exact (mem_one_iff.mp (hv (intCoordsToRat (Pi.single i 1))
        (intCoordsToRat_mem (Pi.single i 1)))).choose_spec
    let psi : (Fin n → ℤ) →ₗ[ℤ] ℤ :=
      { toFun := fun x => ∑ i, x i * coeff i
        map_add' := by
          intro x y
          simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
        map_smul' := by
          intro a x
          simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          simp only [RingHom.id_apply]
          ring }
    have hpsi : ∀ x : Fin n → ℤ,
        ((psi x : ℤ) : ℚ) = pdRatForm L v (intCoordsToRat x) := by
      intro x
      have hxsum : intCoordsToRat x =
          ∑ i, (x i : ℚ) • (Pi.single i 1 : Fin n → ℚ) := by
        calc
          intCoordsToRat x = intCoordsToRat (∑ i, Pi.single i (x i)) :=
            congrArg intCoordsToRat (Finset.univ_sum_single x).symm
          _ = ∑ i, intCoordsToRat (Pi.single i (x i)) := by rw [map_sum]
          _ = ∑ i, (x i : ℚ) • (Pi.single i 1 : Fin n → ℚ) := by
            apply Finset.sum_congr rfl
            intro i _
            funext j
            by_cases hji : j = i <;> simp [intCoordsToRat, hji]
      rw [hxsum, map_sum]
      simp only [map_smul, smul_eq_mul]
      change (((∑ i, x i * coeff i : ℤ)) : ℚ) =
        ∑ i, (x i : ℚ) * pdRatForm L v (Pi.single i 1)
      push_cast
      apply Finset.sum_congr rfl
      intro i _
      rw [hcoeff]
      congr 2
      funext j
      by_cases hji : j = i <;> simp [hji]
    let phi : L.carrier →ₗ[ℤ] ℤ :=
      psi.comp (pdFinBasis L).equivFun.toLinearMap
    obtain ⟨y, hy⟩ := L.unimodular.2 phi
    let z : Fin n → ℤ := (pdFinBasis L).equivFun y
    have hpair : ∀ x : Fin n → ℤ,
        pdRatForm L (intCoordsToRat z) (intCoordsToRat x) =
          pdRatForm L v (intCoordsToRat x) := by
      intro x
      have hleft := pdRatForm_intCoords L z x
      have hyx : L.pairing y (pdCoordEquiv L x) = psi x := by
        have := LinearMap.congr_fun hy (pdCoordEquiv L x)
        simpa [phi, psi, pdCoordEquiv, z] using this
      calc
        pdRatForm L (intCoordsToRat z) (intCoordsToRat x) =
            ((L.pairing (pdCoordEquiv L z) (pdCoordEquiv L x) : ℤ) : ℚ) := hleft
        _ = ((psi x : ℤ) : ℚ) := by
          rw [show pdCoordEquiv L z = y by simp [pdCoordEquiv, z], hyx]
        _ = pdRatForm L v (intCoordsToRat x) := hpsi x
    have heq : intCoordsToRat z = v := by
      have hzero : ∀ x : Fin n → ℤ,
          pdRatForm L (intCoordsToRat z - v) (intCoordsToRat x) = 0 := by
        intro x
        rw [map_sub, LinearMap.sub_apply, hpair x, sub_self]
      have hcoords : ∀ i,
          pdRatForm L (intCoordsToRat z - v) (Pi.single i 1) = 0 := by
        intro i
        have hsingle : intCoordsToRat (Pi.single i 1) =
            (Pi.single i 1 : Fin n → ℚ) := by
          funext j
          by_cases hji : j = i <;> simp [intCoordsToRat, hji]
        rw [← hsingle]
        exact hzero (Pi.single i 1)
      have hall : pdRatForm L (intCoordsToRat z - v) = 0 := by
        apply LinearMap.ext
        intro q
        rw [show q = ∑ i, Pi.single i (q i) from (Finset.univ_sum_single q).symm,
          map_sum]
        apply Finset.sum_eq_zero
        intro i _
        rw [show (Pi.single i (q i) : Fin n → ℚ) =
            q i • Pi.single i 1 by
          funext j
          by_cases hji : j = i <;> simp [hji]]
        rw [map_smul, hcoords]
        simp
      have hnorm : pdRatForm L (intCoordsToRat z - v)
          (intCoordsToRat z - v) = 0 := by rw [hall]; rfl
      by_contra hne
      have := pdRatForm_posDef L (intCoordsToRat z - v) (sub_ne_zero.mpr hne)
      rw [hnorm] at this
      exact lt_irrefl 0 this
    rw [← heq]
    exact intCoordsToRat_mem z
  · intro v hv w hw
    obtain ⟨x, rfl⟩ := hv
    obtain ⟨y, rfl⟩ := hw
    rw [pdRatForm_intCoords]
    exact mem_one_iff.mpr
      ⟨L.pairing (pdCoordEquiv L x) (pdCoordEquiv L y), rfl⟩

end SRG266.Lattice
