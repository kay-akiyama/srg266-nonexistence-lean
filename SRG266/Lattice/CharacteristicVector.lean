/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Lattice.CoordinateRationalLattice

/-!
# Characteristic vectors in an integral unimodular lattice

Every integral unimodular lattice has a characteristic vector.  This file
proves existence directly: prescribe the diagonal values on an integral
basis, extend them to an integer linear functional, and represent that
functional by unimodularity.

The separate `VanDerBlijCongruenceInput` records the classical congruence
`c^2 = rank (mod 8)`.  `VanDerBlij.lean` proves it internally while retaining
this interface as a useful factorization point for the rank-24 construction.
-/

namespace SRG266.Lattice

variable {n : ℕ}

/-- The diagonal functional attached to the chosen integral basis. -/
noncomputable def diagonalFunctional (L : PDUnimodularLattice n) :
    L.carrier →ₗ[ℤ] ℤ where
  toFun x := ∑ i, (pdFinBasis L).equivFun x i *
    L.pairing (pdFinBasis L i) (pdFinBasis L i)
  map_add' x y := by
    simp only [map_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a x := by
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [RingHom.id_apply]
    ring

@[simp]
theorem diagonalFunctional_basis (L : PDUnimodularLattice n) (i : Fin n) :
    diagonalFunctional L (pdFinBasis L i) =
      L.pairing (pdFinBasis L i) (pdFinBasis L i) := by
  classical
  simp [diagonalFunctional, Finsupp.single_apply]

/-- Every integral unimodular lattice has a characteristic vector. -/
theorem exists_characteristicVector (L : PDUnimodularLattice n) :
    ∃ c : L.carrier, IsCharacteristic L.pairing c := by
  obtain ⟨c, hc⟩ := L.unimodular.2 (diagonalFunctional L)
  refine ⟨c, isCharacteristic_of_span L.symmetric c
    (S := Set.range (pdFinBasis L)) (pdFinBasis L).span_eq ?_⟩
  rintro _ ⟨i, rfl⟩
  have hi := LinearMap.congr_fun hc (pdFinBasis L i)
  rw [diagonalFunctional_basis] at hi
  rw [hi]
  simp

/-- Van der Blij's characteristic-norm congruence, in the exact positive-
definite form used by the rank-24 stabilization. -/
abbrev VanDerBlijCongruenceInput : Prop :=
  ∀ (n : ℕ) (L : PDUnimodularLattice n) (c : L.carrier),
    IsCharacteristic L.pairing c →
      ∃ a : ℤ, L.pairing c c = (n : ℤ) + 8 * a

end SRG266.Lattice
