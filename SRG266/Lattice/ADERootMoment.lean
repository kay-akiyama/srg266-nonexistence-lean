/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.ADERootOrbitTransfer
import SRG266.Lattice.RootSecondMoment

/-!
# Second moments and Coxeter numbers of certified ADE components

The reflection-closed certificates identify every actual norm-two root.
This module transports the global second-moment reconstruction identity back
to ADE simple-root coordinates.  Taking a componentwise coordinate trace then
turns the identity into

`c * rank = 2 * rootCount = 2 * rank * CoxeterNumber`.

The argument is integral: no inverse Cartan matrix, rational extension, or
analytic spectral theory is required.
-/

namespace SRG266
namespace Lattice

/-- The coordinate trace contributed by one certified root is its norm. -/
theorem ADERootOrbitCertificate.coordinate_trace {t : ADEType}
    (C : ADERootOrbitCertificate t) (a : Fin C.rootCount) :
    (∑ i, C.root a i * C.reflectionPairing i a) = 2 := by
  rw [show (∑ i, C.root a i * C.reflectionPairing i a) =
      Matrix.toBilin' t.gram (C.root a) (C.root a) by
    simp_rw [C.reflectionPairing_eq]
    rw [Matrix.toBilin'_apply]
    simp only [adeSimplePairing, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring]
  exact C.norm_two a

/-- The global root reconstruction identity, reindexed by the certified ADE
orbit and pulled back through the injective simple-root coordinate map. -/
theorem adeOrbit_coordinate_reconstruction
    {n : ℕ} {L : PDUnimodularLattice n} [Finite (NormTwoRoot L)]
    {f : L.carrier →+ ℤ} {ts : List ADEType}
    (hf : ∀ r : NormTwoRoot L, f r.1 ≠ 0)
    (coord : Fin (ADEType.rankSum ts) ≃ simpleRootSet f)
    (hgram : ∀ i j,
      graphCartanMatrix (simpleRootGraph f) (coord i) (coord j) =
        (adeGram ts).2 i j)
    (C : ADEOrbitFamily ts) {c : ℤ} (hmoment : RootSecondMomentIdentity L c)
    (x : Fin (ADEType.rankSum ts) → ℤ) :
    (∑ a : ADEOrbitIndex ts C,
        (L.pairing (adeOrbitActualRoot hf coord hgram C a).1
          (coordinateRootMap coord x)) • adeOrbitRoot ts C a) =
      c • x := by
  let O := adeNormTwoRootOrbitCertificate hf coord hgram C
  letI := O.indexFintype
  let e : O.Index ≃ NormTwoRoot L := O.rootEquiv hf
  apply coordinateRootMap_injective hf coord
  simp only [map_sum, map_zsmul]
  calc
    (∑ a : O.Index,
        (L.pairing (O.root a).1 (coordinateRootMap coord x)) • (O.root a).1) =
        ∑ r : NormTwoRoot L,
          (L.pairing r.1 (coordinateRootMap coord x)) • r.1 :=
      e.sum_comp (fun r : NormTwoRoot L =>
        (L.pairing r.1 (coordinateRootMap coord x)) • r.1)
    _ = c • coordinateRootMap coord x :=
      rootSecondMoment_reconstruction L hmoment (coordinateRootMap coord x)

/-- Evaluating reconstruction at one standard simple-root coordinate gives
the diagonal moment of that coordinate. -/
theorem adeOrbit_simpleCoordinate_moment
    {n : ℕ} {L : PDUnimodularLattice n} [Finite (NormTwoRoot L)]
    {f : L.carrier →+ ℤ} {ts : List ADEType}
    (hf : ∀ r : NormTwoRoot L, f r.1 ≠ 0)
    (coord : Fin (ADEType.rankSum ts) ≃ simpleRootSet f)
    (hgram : ∀ i j,
      graphCartanMatrix (simpleRootGraph f) (coord i) (coord j) =
        (adeGram ts).2 i j)
    (C : ADEOrbitFamily ts) {c : ℤ} (hmoment : RootSecondMomentIdentity L c)
    (i : Fin (ADEType.rankSum ts)) :
    (∑ a : ADEOrbitIndex ts C,
        adeOrbitSimplePairing ts C (finADEBlockEquiv ts i) a *
          adeOrbitRoot ts C a i) = c := by
  have hpair (a : ADEOrbitIndex ts C) :
      L.pairing (adeOrbitActualRoot hf coord hgram C a).1
          (coordinateRootMap coord (Pi.single i (1 : ℤ))) =
        adeOrbitSimplePairing ts C (finADEBlockEquiv ts i) a := by
    rw [coordinateRootMap_piSingle]
    change L.pairing (adeOrbitActualRoot hf coord hgram C a).1
      (coord i).1.1 = _
    simpa using adeOrbitActualRoot_pair_simple hf coord hgram C a (coord i)
  have h := congrFun
    (adeOrbit_coordinate_reconstruction hf coord hgram C hmoment
      (Pi.single i (1 : ℤ))) i
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hpair,
    Pi.single_eq_same, mul_one] using h

/-- The same diagonal moment in recursive block coordinates. -/
theorem adeOrbit_blockCoordinate_moment
    {n : ℕ} {L : PDUnimodularLattice n} [Finite (NormTwoRoot L)]
    {f : L.carrier →+ ℤ} {ts : List ADEType}
    (hf : ∀ r : NormTwoRoot L, f r.1 ≠ 0)
    (coord : Fin (ADEType.rankSum ts) ≃ simpleRootSet f)
    (hgram : ∀ i j,
      graphCartanMatrix (simpleRootGraph f) (coord i) (coord j) =
        (adeGram ts).2 i j)
    (C : ADEOrbitFamily ts) {c : ℤ} (hmoment : RootSecondMomentIdentity L c)
    (s : ADEBlockIndex ts) :
    (∑ a : ADEOrbitIndex ts C,
        adeOrbitSimplePairing ts C s a * adeOrbitBlockRoot ts C a s) = c := by
  simpa [adeOrbitRoot] using
    adeOrbit_simpleCoordinate_moment hf coord hgram C hmoment
      ((finADEBlockEquiv ts).symm s)

/-- Componentwise trace of the diagonal moments.  Orthogonality makes the
statement recursive: head roots vanish on tail coordinates and conversely.
The checked root count then forces the same Coxeter number in every regular
component. -/
theorem adeOrbit_coxeter_eq_of_blockCoordinate_moment {c : ℤ} :
    ∀ (ts : List ADEType) (C : ADEOrbitFamily ts),
      (∀ s : ADEBlockIndex ts,
        (∑ a : ADEOrbitIndex ts C,
          adeOrbitSimplePairing ts C s a * adeOrbitBlockRoot ts C a s) = c) →
      (∀ t ∈ ts, t.IsRegular) →
      ∀ t ∈ ts, c = 2 * (t.coxeterNumber : ℤ)
  | [], _, _, _, t, ht => by simp at ht
  | t :: ts, (Ct, Cs), hcoord, hregular, u, hu => by
      have hheadCoordinate (i : Fin t.rank) :
          (∑ a : Fin Ct.rootCount,
            Ct.reflectionPairing i a * Ct.root a i) = c := by
        have h := hcoord (Sum.inl i)
        change (∑ a : Fin Ct.rootCount ⊕ ADEOrbitIndex ts Cs,
          adeOrbitSimplePairing (t :: ts) (Ct, Cs) (Sum.inl i) a *
            adeOrbitBlockRoot (t :: ts) (Ct, Cs) a (Sum.inl i)) = c at h
        simpa only [Fintype.sum_sum_type, adeOrbitSimplePairing,
          adeOrbitBlockRoot, zero_mul, Finset.sum_const_zero, add_zero] using
          h
      have htrace : (t.rank : ℤ) * c = 2 * (Ct.rootCount : ℤ) := by
        calc
          (t.rank : ℤ) * c = ∑ i : Fin t.rank, c := by simp
          _ = ∑ i : Fin t.rank, ∑ a : Fin Ct.rootCount,
                Ct.reflectionPairing i a * Ct.root a i := by
            apply Finset.sum_congr rfl
            intro i _
            exact (hheadCoordinate i).symm
          _ = ∑ a : Fin Ct.rootCount, ∑ i : Fin t.rank,
                Ct.reflectionPairing i a * Ct.root a i := Finset.sum_comm
          _ = ∑ _a : Fin Ct.rootCount, (2 : ℤ) := by
            apply Finset.sum_congr rfl
            intro a _
            simpa only [mul_comm] using Ct.coordinate_trace a
          _ = 2 * (Ct.rootCount : ℤ) := by simp [mul_comm]
      have htregular : t.IsRegular := hregular t (by simp)
      have htrank : 0 < t.rank := by
        cases t <;> simp [ADEType.IsRegular, ADEType.rank] at htregular ⊢ <;>
          omega
      have hcox : c = 2 * (t.coxeterNumber : ℤ) := by
        rw [Ct.rootCount_eq_rank_mul_coxeter] at htrace
        push_cast at htrace
        have htrankZ : (0 : ℤ) < (t.rank : ℤ) := by exact_mod_cast htrank
        nlinarith
      have hu' : u = t ∨ u ∈ ts := by simpa using hu
      rcases hu' with hut | hu
      · simpa [hut] using hcox
      · refine adeOrbit_coxeter_eq_of_blockCoordinate_moment ts Cs
          (c := c) ?_ (fun v hv => hregular v (by simp [hv])) u hu
        intro s
        have h := hcoord (Sum.inr s)
        change (∑ a : Fin Ct.rootCount ⊕ ADEOrbitIndex ts Cs,
          adeOrbitSimplePairing (t :: ts) (Ct, Cs) (Sum.inr s) a *
            adeOrbitBlockRoot (t :: ts) (Ct, Cs) a (Sum.inr s)) = c at h
        simpa only [Fintype.sum_sum_type, adeOrbitSimplePairing,
          adeOrbitBlockRoot, zero_mul, Finset.sum_const_zero, zero_add] using h

/-- The lattice second moment therefore fixes the Coxeter number of every
certified regular ADE component. -/
theorem adeOrbit_coxeter_eq_of_secondMoment
    {n : ℕ} {L : PDUnimodularLattice n} [Finite (NormTwoRoot L)]
    {f : L.carrier →+ ℤ} {ts : List ADEType}
    (hf : ∀ r : NormTwoRoot L, f r.1 ≠ 0)
    (coord : Fin (ADEType.rankSum ts) ≃ simpleRootSet f)
    (hgram : ∀ i j,
      graphCartanMatrix (simpleRootGraph f) (coord i) (coord j) =
        (adeGram ts).2 i j)
    (C : ADEOrbitFamily ts) {c : ℤ} (hmoment : RootSecondMomentIdentity L c)
    (hregular : ∀ t ∈ ts, t.IsRegular) :
    ∀ t ∈ ts, c = 2 * (t.coxeterNumber : ℤ) := by
  apply adeOrbit_coxeter_eq_of_blockCoordinate_moment ts C
  · exact adeOrbit_blockCoordinate_moment hf coord hgram C hmoment
  · exact hregular

end Lattice
end SRG266
