/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Lattice.LevelOneWeight14
import SRG266.Lattice.Rank24HarmonicThetaAnalytic
import SRG266.Lattice.VanDerBlij

/-!
# The rank-24 harmonic theta theorem

For an even unimodular lattice `N` of rank twenty four and lattice vectors
`x,y`, the degree-two harmonic polynomial is represented integrally by

`24 * <v,x> * <v,y> - <x,y> * <v,v>`.

Its theta series has weight `24 / 2 + 2 = 14`.  This file defines every
coefficient as a finite lattice-shell sum.  Poisson summation proves that the
resulting analytic function is a level-one cusp form of weight fourteen.
Mathlib's dimension formula then kills the cusp form, and the coefficient of
norm two gives the scalar root second moment.
-/

namespace SRG266.Lattice

open scoped MatrixGroups BigOperators
open ModularGroup ModularForm UpperHalfPlane

/-- The exact analytic boundary for the rank-24 route. -/
abbrev Rank24HarmonicThetaModularityInput : Prop :=
  ∀ (N : PDUnimodularLattice 24),
    (∀ z : N.carrier, Even (N.pairing z z)) →
    ∀ x y : N.carrier, ∃ f : CuspForm 𝒮ℒ 14,
      qExpansion 1 f = harmonicThetaSeries N x y

/-- The explicitly defined degree-two harmonic
theta series is the q-expansion of a level-one cusp form of weight fourteen.
The witness is the analytic theta function constructed from lattice Poisson
summation. -/
theorem rank24HarmonicThetaModularity :
    Rank24HarmonicThetaModularityInput := by
  intro N heven x y
  exact ⟨harmonicThetaCuspForm N heven x y,
    harmonicThetaCuspForm_qExpansion N heven x y⟩

/-- Modularity and the vanishing of the weight-fourteen cusp space force
every harmonic-theta coefficient to vanish. -/
theorem harmonicThetaCoefficient_eq_zero
    (N : PDUnimodularLattice 24)
    (heven : ∀ z : N.carrier, Even (N.pairing z z))
    (x y : N.carrier) (k : ℕ) :
    harmonicThetaCoefficient N x y k = 0 := by
  obtain ⟨f, hf⟩ := rank24HarmonicThetaModularity N heven x y
  have hfzero : f = 0 := levelOne_weight_fourteen_cusp_eq_zero f
  have hseries : harmonicThetaSeries N x y = 0 := by
    rw [← hf, hfzero]
    simpa using UpperHalfPlane.qExpansion_zero (1 : ℝ)
  have hcoeff := congrArg (fun s : PowerSeries ℂ => s.coeff k) hseries
  have hcoeff' : (harmonicThetaCoefficient N x y k : ℂ) = 0 := by
    simpa using hcoeff
  exact_mod_cast hcoeff'

/-- The vanishing norm-two coefficient, expanded as the integral harmonic
root identity. -/
theorem harmonicRootIdentity
    (N : PDUnimodularLattice 24)
    (heven : ∀ z : N.carrier, Even (N.pairing z z))
    (x y : N.carrier) :
    24 * (∑ r : NormTwoRoot N,
      N.pairing r.1 x * N.pairing r.1 y) =
      2 * (Fintype.card (NormTwoRoot N) : ℤ) * N.pairing x y := by
  have hzero := harmonicThetaCoefficient_eq_zero N heven x y 1
  change (∑ r : NormTwoRoot N,
    (24 * N.pairing r.1 x * N.pairing r.1 y -
      N.pairing x y * N.pairing r.1 r.1)) = 0 at hzero
  have hexpand :
      (∑ r : NormTwoRoot N,
        (24 * N.pairing r.1 x * N.pairing r.1 y -
          N.pairing x y * N.pairing r.1 r.1)) =
        24 * (∑ r : NormTwoRoot N,
          N.pairing r.1 x * N.pairing r.1 y) -
          2 * (Fintype.card (NormTwoRoot N) : ℤ) * N.pairing x y := by
    simp_rw [show ∀ r : NormTwoRoot N, N.pairing r.1 r.1 = 2 from fun r => r.2]
    rw [Finset.sum_sub_distrib]
    congr 1
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring
    · rw [Finset.sum_const, Finset.card_univ]
      simp only [nsmul_eq_mul]
      ring
  rw [hexpand] at hzero
  linarith

/-! ## Direct transport to the low-rank lattice -/

/-- The harmonic root identity transports through the standard even
neighbour without first packaging its rational scalar as an integer.  The
explicit `D_(24-n)` root fixes the total number of roots, and a second
evaluation on doubled vectors of `L` gives the required low-rank moment. -/
theorem rootSecondMoment_of_harmonicTheta
    {n : ℕ} (hnlo : 12 ≤ n) (hnhi : n ≤ 15)
    (L : PDUnimodularLattice n) (E : EvenNeighbor24Data L) :
    RootSecondMomentIdentity L (thetaRootSecondMomentScalar n) := by
  classical
  let m := 24 - n
  have hmlo : 9 ≤ m := by omega
  have hmhi : m ≤ 12 := by omega
  let q : DRoot m := DRoot.test (by omega)
  let rootCount : ℤ := Fintype.card (NormTwoRoot E.neighbor)
  have hcount : rootCount = 48 * (m - 1) := by
    have htest := harmonicRootIdentity E.neighbor
      E.evenNorm (E.dRoot q) (E.dRoot q)
    rw [show
      (∑ r : NormTwoRoot E.neighbor,
        E.neighbor.pairing r.1 (E.dRoot q) *
          E.neighbor.pairing r.1 (E.dRoot q)) =
        (∑ r : NormTwoRoot L,
          E.neighbor.pairing (E.leftRoot r) (E.dRoot q) *
            E.neighbor.pairing (E.leftRoot r) (E.dRoot q)) +
          ∑ r : DRoot (24 - n),
            E.neighbor.pairing (E.dRoot r) (E.dRoot q) *
              E.neighbor.pairing (E.dRoot r) (E.dRoot q) from
      E.rootSum (fun z =>
        E.neighbor.pairing z (E.dRoot q) *
          E.neighbor.pairing z (E.dRoot q))] at htest
    have hleft :
        (∑ r : NormTwoRoot L,
          E.neighbor.pairing (E.leftRoot r) (E.dRoot q) *
            E.neighbor.pairing (E.leftRoot r) (E.dRoot q)) = 0 := by
      apply Finset.sum_eq_zero
      intro r _
      rw [E.crossRootPairing]
      simp
    have hright :
        (∑ r : DRoot m,
          E.neighbor.pairing (E.dRoot r) (E.dRoot q) *
            E.neighbor.pairing (E.dRoot r) (E.dRoot q)) =
          8 * (m - 1) := by
      simpa only [E.dRootPairing, pow_two] using
        dRoot_test_secondMoment hmlo hmhi
    rw [hleft, zero_add, hright, E.dRootPairing, DRoot.intDot_self] at htest
    change rootCount = 48 * (m - 1)
    dsimp only [rootCount]
    linarith
  intro x y
  have hxy := harmonicRootIdentity E.neighbor
    E.evenNorm (E.leftDouble x) (E.leftDouble y)
  rw [show
    (∑ r : NormTwoRoot E.neighbor,
      E.neighbor.pairing r.1 (E.leftDouble x) *
        E.neighbor.pairing r.1 (E.leftDouble y)) =
      (∑ r : NormTwoRoot L,
        E.neighbor.pairing (E.leftRoot r) (E.leftDouble x) *
          E.neighbor.pairing (E.leftRoot r) (E.leftDouble y)) +
        ∑ r : DRoot (24 - n),
          E.neighbor.pairing (E.dRoot r) (E.leftDouble x) *
            E.neighbor.pairing (E.dRoot r) (E.leftDouble y) from
    E.rootSum (fun z =>
      E.neighbor.pairing z (E.leftDouble x) *
        E.neighbor.pairing z (E.leftDouble y))] at hxy
  have hd :
      (∑ r : DRoot m,
        E.neighbor.pairing (E.dRoot r) (E.leftDouble x) *
          E.neighbor.pairing (E.dRoot r) (E.leftDouble y)) = 0 := by
    apply Finset.sum_eq_zero
    intro r _
    rw [E.neighbor.symmetric.eq (E.dRoot r) (E.leftDouble x),
      E.neighbor.symmetric.eq (E.dRoot r) (E.leftDouble y),
      E.crossDoublePairing, E.crossDoublePairing]
    simp
  rw [hd, add_zero, E.leftDoublePairing] at hxy
  simp only [E.leftRootPairing] at hxy
  have hcount' : (Fintype.card (NormTwoRoot E.neighbor) : ℤ) =
      48 * (m - 1) := hcount
  rw [hcount'] at hxy
  simp only [thetaRootSecondMomentScalar]
  have hn : ((23 - n : ℕ) : ℤ) = (m : ℤ) - 1 := by
    omega
  rw [Nat.cast_mul]
  norm_num only [Nat.cast_ofNat]
  rw [hn]
  have hsum :
      (∑ r : NormTwoRoot L,
        (2 * L.pairing r.1 x) * (2 * L.pairing r.1 y)) =
        4 * (∑ r : NormTwoRoot L,
          L.pairing r.1 x * L.pairing r.1 y) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [hsum] at hxy
  have hscaled :
      96 * (∑ r : NormTwoRoot L,
        L.pairing r.1 x * L.pairing r.1 y) =
        96 * (4 * ((m : ℤ) - 1) * L.pairing x y) := by
    linear_combination hxy
  exact mul_left_cancel₀ (by decide : (96 : ℤ) ≠ 0) hscaled

/-- Combining the algebraic even-neighbour construction with harmonic theta
modularity gives the complete second-moment input. -/
theorem thetaRootSecondMoment_of_neighbor_and_harmonicTheta
    (hNeighbor : EvenNeighbor24Input) :
    ThetaRootSecondMomentInput := by
  intro n hnlo hnhi L hfree
  exact rootSecondMoment_of_harmonicTheta hnlo hnhi L
    (hNeighbor n hnlo hnhi L hfree).some

/-- End-to-end root second moment from the internally proved van der Blij
congruence and harmonic-theta modularity theorem. -/
theorem thetaRootSecondMoment_of_harmonicTheta :
    ThetaRootSecondMomentInput :=
  thetaRootSecondMoment_of_neighbor_and_harmonicTheta
    (evenNeighbor24Input_of_vanDerBlij vanDerBlijCongruence)

end SRG266.Lattice
