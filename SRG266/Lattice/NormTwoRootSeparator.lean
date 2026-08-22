/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.NormTwoRootFinite
import Mathlib.Algebra.Polynomial.Roots

/-!
# An integral functional separating all norm-two roots

A finite set of nonzero vectors in a finite free integral module admits an
integer linear functional which vanishes on none of them.  Here the functional
is constructed explicitly enough for the simple-root argument.

For a basis `b`, encode the coordinates of `x` as the polynomial

`p_x(T) = sum_i b_i^*(x) T^i`.

Every root gives a nonzero polynomial.  Their finite product is nonzero, so it
has only finitely many integer roots.  Evaluation at an integer outside that
root set is the required functional.
-/

namespace SRG266
namespace Lattice

open Polynomial

/-- The basis-coordinate polynomial of a lattice vector. -/
noncomputable def coordinatePolynomial {n : ℕ}
    {L : PDUnimodularLattice n} (b : Module.Basis (Fin n) ℤ L.carrier)
    (x : L.carrier) : ℤ[X] :=
  ∑ i : Fin n, C (b.coord i x) * X ^ (i : ℕ)

/-- Reading coefficient `i` recovers basis coordinate `i`. -/
theorem coordinatePolynomial_coeff {n : ℕ}
    {L : PDUnimodularLattice n} (b : Module.Basis (Fin n) ℤ L.carrier)
    (x : L.carrier) (i : Fin n) :
    (coordinatePolynomial b x).coeff i = b.coord i x := by
  classical
  simp [coordinatePolynomial, ← Fin.ext_iff]

/-- A nonzero vector has a nonzero coordinate polynomial. -/
theorem coordinatePolynomial_ne_zero {n : ℕ}
    {L : PDUnimodularLattice n} (b : Module.Basis (Fin n) ℤ L.carrier)
    {x : L.carrier} (hx : x ≠ 0) : coordinatePolynomial b x ≠ 0 := by
  intro hp
  have hcoords : ∀ i : Fin n, b.coord i x = 0 := by
    intro i
    rw [← coordinatePolynomial_coeff b x i, hp, coeff_zero]
  apply hx
  apply b.equivFun.injective
  ext i
  simpa using hcoords i

/-- Evaluation of the coordinate polynomial as an integral linear map. -/
noncomputable def coordinateEvaluation {n : ℕ}
    {L : PDUnimodularLattice n} (b : Module.Basis (Fin n) ℤ L.carrier)
    (a : ℤ) : L.carrier →ₗ[ℤ] ℤ :=
  ∑ i : Fin n, (a ^ (i : ℕ)) • b.coord i

/-- The linear map `coordinateEvaluation` really evaluates
`coordinatePolynomial`. -/
theorem coordinateEvaluation_apply {n : ℕ}
    {L : PDUnimodularLattice n} (b : Module.Basis (Fin n) ℤ L.carrier)
    (a : ℤ) (x : L.carrier) :
    coordinateEvaluation b a x = (coordinatePolynomial b x).eval a := by
  classical
  simp [coordinateEvaluation, coordinatePolynomial, Polynomial.eval_finsetSum, mul_comm]

/-- The product of the coordinate polynomials of all norm-two roots. -/
noncomputable def rootAvoidancePolynomial {n : ℕ}
    (L : PDUnimodularLattice n)
    (b : Module.Basis (Fin n) ℤ L.carrier) : ℤ[X] :=
  ∏ r : NormTwoRoot L, coordinatePolynomial b r.1

/-- No factor of the root-avoidance polynomial is zero. -/
theorem rootAvoidancePolynomial_ne_zero {n : ℕ}
    (L : PDUnimodularLattice n)
    (b : Module.Basis (Fin n) ℤ L.carrier) :
    rootAvoidancePolynomial L b ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro r _
  exact coordinatePolynomial_ne_zero b (normTwoRootVal_ne_zero r)

/-- There is an integer additive functional which is nonzero on every
norm-two root. -/
theorem exists_rootSeparatingFunctional {n : ℕ}
    (L : PDUnimodularLattice n) :
    ∃ f : L.carrier →+ ℤ, ∀ r : NormTwoRoot L, f r.1 ≠ 0 := by
  classical
  letI := L.moduleFree
  letI := L.moduleFinite
  let b : Module.Basis (Fin n) ℤ L.carrier :=
    Module.finBasisOfFinrankEq ℤ L.carrier L.rank
  let p := rootAvoidancePolynomial L b
  have hp : p ≠ 0 := rootAvoidancePolynomial_ne_zero L b
  obtain ⟨a, _, ha⟩ := Set.infinite_univ.exists_notMem_finite
    (Polynomial.finite_setOf_isRoot hp)
  refine ⟨(coordinateEvaluation b a).toAddMonoidHom, ?_⟩
  intro r
  change coordinateEvaluation b a r.1 ≠ 0
  rw [coordinateEvaluation_apply]
  intro hr
  apply ha
  change (rootAvoidancePolynomial L b).eval a = 0
  rw [rootAvoidancePolynomial, Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ r) hr

end Lattice
end SRG266
