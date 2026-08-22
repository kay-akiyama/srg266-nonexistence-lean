/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Lattice.NormShellFinite
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Algebraic harmonic theta coefficients

For a rank-twenty-four positive-definite integral lattice, this file defines
the finite degree-two harmonic sums on every norm shell and packages them as
a formal power series.  No analytic or modularity assertion occurs here.
-/

namespace SRG266.Lattice

open scoped BigOperators

/-- The integral coefficient of the degree-two harmonic theta series.  The
`k`-th coefficient sums over the vectors of norm `2k`. -/
noncomputable def harmonicThetaCoefficient
    (N : PDUnimodularLattice 24) (x y : N.carrier) (k : ℕ) : ℤ :=
  ∑ v : NormShell N (2 * k),
    (24 * N.pairing v.1 x * N.pairing v.1 y -
      N.pairing x y * N.pairing v.1 v.1)

/-- The degree-two harmonic theta series, with its coefficients embedded in
the complex numbers. -/
noncomputable def harmonicThetaSeries
    (N : PDUnimodularLattice 24) (x y : N.carrier) : PowerSeries ℂ :=
  PowerSeries.mk fun k => (harmonicThetaCoefficient N x y k : ℂ)

@[simp]
theorem harmonicThetaSeries_coeff
    (N : PDUnimodularLattice 24) (x y : N.carrier) (k : ℕ) :
    (harmonicThetaSeries N x y).coeff k =
      (harmonicThetaCoefficient N x y k : ℂ) := by
  simp [harmonicThetaSeries]

end SRG266.Lattice
