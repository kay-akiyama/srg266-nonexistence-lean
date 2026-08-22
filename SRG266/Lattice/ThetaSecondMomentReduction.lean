/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.ADERootOrbitFamilyAssembly
import SRG266.Lattice.ThetaEutaxyBoundary

/-!
# Reduction of theta eutaxy to one second-moment identity

For ranks twelve through fifteen, the only modular-form statement used by the
root-system argument is the degree-two identity

`sum_r <r,x><r,y> = 4 * (23 - n) * <x,y>`.

Everything else is derived here:

* norm-two roots are finite by positive definiteness;
* the nonzero moment scalar makes their span full rank;
* a separating integral functional exists;
* the root system has regular ADE coordinates;
* checked reflection orbits contain every root;
* a componentwise integral trace fixes every Coxeter number.

The certificate selector is kept as an explicit parameter in this lightweight
module.  `ADERootOrbitData` supplies it from kernel-checked generated data.
-/

namespace SRG266

/-- The integral scalar in the root second-moment identity. -/
def thetaRootSecondMomentScalar (n : ℕ) : ℤ :=
  ((4 * (23 - n) : ℕ) : ℤ)

/-- The norm-one-free theta calculation
asserts only the exact degree-two root moment. -/
abbrev ThetaRootSecondMomentInput : Prop :=
  ∀ (n : ℕ), 12 ≤ n → n ≤ 15 → ∀ (L : PDUnimodularLattice n),
    (∀ v : L.carrier, L.pairing v v ≠ 1) →
      Lattice.RootSecondMomentIdentity L (thetaRootSecondMomentScalar n)

/-- The single theta second moment implies the theta-plus-ADE
decomposition interface once the bounded ADE orbit certificates are supplied.
No root-system classification or enumeration conclusion is assumed here. -/
theorem thetaEutacticADEDecomposition_of_secondMoment
    (select : Lattice.ADEOrbitCertificateSelectorLE15)
    (hTheta : ThetaRootSecondMomentInput) :
    ThetaEutacticADEDecompositionInput := by
  intro n hnlo hnhi L hfree
  letI := Lattice.normTwoRootFinite L
  have hmoment : Lattice.RootSecondMomentIdentity L
      (thetaRootSecondMomentScalar n) := hTheta n hnlo hnhi L hfree
  have hc : thetaRootSecondMomentScalar n ≠ 0 := by
    simp only [thetaRootSecondMomentScalar]
    omega
  have hrank : Set.finrank ℤ
      (Set.range (@Lattice.normTwoRootVal n L)) = n :=
    Lattice.normTwoRoots_fullRank_of_secondMoment L hc hmoment
  obtain ⟨f, hf⟩ := Lattice.exists_rootSeparatingFunctional L
  obtain ⟨ts, hregular, hts, coord, hgram⟩ :=
    Lattice.normTwoRoots_haveADECoordinates hnhi L f hf hrank
  have htsle : Lattice.ADEType.rankSum ts ≤ 15 := by omega
  let C : Lattice.ADEOrbitFamily ts :=
    Lattice.adeOrbitFamilyOfSelectorLE15 select ts hregular htsle
  have hcoxZ := Lattice.adeOrbit_coxeter_eq_of_secondMoment
    hf coord hgram C hmoment hregular
  have hcox : ∀ t ∈ ts, t.coxeterNumber = 2 * (23 - n) := by
    intro t ht
    have h := hcoxZ t ht
    simp only [thetaRootSecondMomentScalar] at h
    omega
  refine ⟨ts, hts, ?_, hcox⟩
  refine ⟨Lattice.coordinateRootMap coord,
    Lattice.coordinateRootMap_injective hf coord, ?_, ?_⟩
  · intro x y
    exact Lattice.coordinateRootMap_pairing hf coord
      (Lattice.adeGram ts).2 hgram x y
  · intro r hr
    exact Lattice.coordinateRootMap_covers_normTwoRoots hf coord ⟨r, hr⟩

end SRG266
