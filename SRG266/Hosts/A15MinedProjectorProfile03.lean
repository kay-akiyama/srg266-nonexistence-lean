/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Hosts.A15MinedProjectorTheory
import SRG266.Hosts.A15MinedNormProfileData
import SRG266.Hosts.A15MinedSearch

/-!
# Mined exclusion of A15 projector profile 3

The certificate rejects twelve orbit-total candidates with several
different one- and two-vector witnesses.  On the two class indicators for the
singleton `-40` class and the three-coordinate `-20` class, the direct
complement projector has determinant

`-(2p - 35)² / 8100`,

where `p` is an integer shell multiplicity sum.  Since `2p - 35` is odd, this
minor is strictly negative.  The proof derives the three matrix entries from
class-count and centroid equations and uses no orbit table, membership audit,
or rejection list.
-/

open scoped BigOperators Matrix

namespace SRG266

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The class-only skeleton of generated projector profile 3. -/
def a15MinedProjectorProfile03 : A15ProjectorProfile where
  centroidIndex := 3
  d := #[-40, -20, -20, -20,
    0, 0, 0, 0, 0, 0, 0,
    20, 20, 20, 20, 20]
  reportedEligible := 155
  classValues := #[-40, -20, 0, 20]
  classSizes := #[1, 3, 7, 5]
  orbits := #[]

theorem a15MinedProjectorProfile03_centroidVector :
    a15MinedProjectorProfile03.centroidVector =
      a15SmallProfile a15MinedNormProfile12 := by
  funext i
  fin_cases i <;> rfl

private theorem a15MinedProjectorProfile03_static :
    (∑ i, a15MinedProjectorProfile03.centroidVector i) = 0 ∧
    (∀ i, a15MinedProjectorProfile03.classIndexCount i = 1) ∧
    (∀ c : Fin a15MinedProjectorProfile03.classSizes.size,
      (a15MinedProjectorProfile03.classFinset c.1).card =
        a15MinedProjectorProfile03.classSizes.getD c.1 0 ∧
      ∀ i, a15MinedProjectorProfile03.inClass c.1 i →
        a15MinedProjectorProfile03.centroidVector i =
          a15MinedProjectorProfile03.classValues.getD c.1 0) := by
  decide +kernel

private theorem a15MinedProjectorProfile03_countCases
    (s : A15EligibleIndex a15MinedProjectorProfile03.centroidVector) :
    let r0 := a15ProjectorClassCount
      a15MinedProjectorProfile03.classSizes (a15FourSubsetAt s.1) 0
    let r1 := a15ProjectorClassCount
      a15MinedProjectorProfile03.classSizes (a15FourSubsetAt s.1) 1
    (a15SubsetSum a15MinedProjectorProfile03.centroidVector s.1 = 60 →
        r0 = 0 ∧ r1 = 0) ∧
      (a15SubsetSum a15MinedProjectorProfile03.centroidVector s.1 = -60 →
        (r0 = 0 ∧ r1 = 3) ∨ (r0 = 1 ∧ r1 = 1) ∨
          (r0 = 1 ∧ r1 = 2)) := by
  let r0 := a15ProjectorClassCount
    a15MinedProjectorProfile03.classSizes (a15FourSubsetAt s.1) 0
  let r1 := a15ProjectorClassCount
    a15MinedProjectorProfile03.classSizes (a15FourSubsetAt s.1) 1
  let r2 := a15ProjectorClassCount
    a15MinedProjectorProfile03.classSizes (a15FourSubsetAt s.1) 2
  let r3 := a15ProjectorClassCount
    a15MinedProjectorProfile03.classSizes (a15FourSubsetAt s.1) 3
  have hsum := a15MinedProjectorProfile03.sum_classCounts
    a15MinedProjectorProfile03_static.2.1 s.1
  have hweighted := a15MinedProjectorProfile03.weighted_classCounts
    a15MinedProjectorProfile03_static.2.1
    (fun c => (a15MinedProjectorProfile03_static.2.2 c).2) s.1
  have h0 := a15MinedProjectorProfile03.classCount_le_classSize
    ⟨0, by decide⟩ s.1
      (a15MinedProjectorProfile03_static.2.2 ⟨0, by decide⟩).1
  have h1 := a15MinedProjectorProfile03.classCount_le_classSize
    ⟨1, by decide⟩ s.1
      (a15MinedProjectorProfile03_static.2.2 ⟨1, by decide⟩).1
  have h2 := a15MinedProjectorProfile03.classCount_le_classSize
    ⟨2, by decide⟩ s.1
      (a15MinedProjectorProfile03_static.2.2 ⟨2, by decide⟩).1
  have h3 := a15MinedProjectorProfile03.classCount_le_classSize
    ⟨3, by decide⟩ s.1
      (a15MinedProjectorProfile03_static.2.2 ⟨3, by decide⟩).1
  change (∑ c : Fin 4,
    a15ProjectorClassCount #[1, 3, 7, 5]
      (a15FourSubsetAt s.1) c.1) = 4 at hsum
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hsum
  norm_num at hsum
  change (∑ c : Fin 4,
    (#[(-40 : ℤ), -20, 0, 20].getD c.1 0 : ℤ) *
      a15ProjectorClassCount #[1, 3, 7, 5]
        (a15FourSubsetAt s.1) c.1) = _ at hweighted
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hweighted
  norm_num at hweighted
  norm_num [a15MinedProjectorProfile03] at h0 h1 h2 h3
  change
    (a15SubsetSum a15MinedProjectorProfile03.centroidVector s.1 = 60 →
        a15ProjectorClassCount #[1, 3, 7, 5]
            (a15FourSubsetAt s.1) 0 = 0 ∧
          a15ProjectorClassCount #[1, 3, 7, 5]
            (a15FourSubsetAt s.1) 1 = 0) ∧
      (a15SubsetSum a15MinedProjectorProfile03.centroidVector s.1 = -60 →
        (a15ProjectorClassCount #[1, 3, 7, 5]
              (a15FourSubsetAt s.1) 0 = 0 ∧
            a15ProjectorClassCount #[1, 3, 7, 5]
              (a15FourSubsetAt s.1) 1 = 3) ∨
          (a15ProjectorClassCount #[1, 3, 7, 5]
              (a15FourSubsetAt s.1) 0 = 1 ∧
            a15ProjectorClassCount #[1, 3, 7, 5]
              (a15FourSubsetAt s.1) 1 = 1) ∨
          (a15ProjectorClassCount #[1, 3, 7, 5]
              (a15FourSubsetAt s.1) 0 = 1 ∧
            a15ProjectorClassCount #[1, 3, 7, 5]
              (a15FourSubsetAt s.1) 1 = 2))
  constructor <;> intro heligible <;> omega

private theorem a15MinedProjectorProfile03_pointwiseProducts
    (s : A15EligibleIndex a15MinedProjectorProfile03.centroidVector) :
    let z0 := a15MinedProjectorProfile03.shellDot
      (a15ClassIndicator a15MinedProjectorProfile03 0) s
    let z1 := a15MinedProjectorProfile03.shellDot
      (a15ClassIndicator a15MinedProjectorProfile03 1) s
    let e : ℤ := if a15ProjectorClassCount
      a15MinedProjectorProfile03.classSizes
        (a15FourSubsetAt s.1) 1 = 3 then 1 else 0
    z0 ^ 2 = -3 - 4 * z0 + 8 * e ∧
      z0 * z1 = -9 - 3 * z0 - 3 * z1 - 24 * e ∧
      z1 ^ 2 = -11 - 2 * z0 - 6 * z1 + 40 * e := by
  dsimp only
  rw [a15MinedProjectorProfile03.shellDot_classIndicator,
    a15MinedProjectorProfile03.shellDot_classIndicator]
  have hclass0 := a15MinedProjectorProfile03.sum_shellCoordinate_class s 0
  have hclass1 := a15MinedProjectorProfile03.sum_shellCoordinate_class s 1
  have hcases := a15MinedProjectorProfile03_countCases s
  rw [hclass0, hclass1, ← a15ProjectorClassCount_eq_card,
    ← a15ProjectorClassCount_eq_card]
  rw [show (a15MinedProjectorProfile03.classFinset 0).card = 1 by decide,
    show (a15MinedProjectorProfile03.classFinset 1).card = 3 by decide]
  dsimp only at hcases
  rcases s.2 with hneg | hpos
  · have hsum :
        a15SubsetSum a15MinedProjectorProfile03.centroidVector s.1 = -60 := by
      simpa only [a15Eligible, a15DataEligible, a15SubsetSum] using hneg
    rcases hcases.2 hsum with
      ⟨hr0, hr1⟩ | ⟨hr0, hr1⟩ | ⟨hr0, hr1⟩
    · simp [show a15SubsetSum
          a15MinedProjectorProfile03.centroidVector s.1 ≠ 60 by omega,
        hr0, hr1]
    · simp [show a15SubsetSum
          a15MinedProjectorProfile03.centroidVector s.1 ≠ 60 by omega,
        hr0, hr1]
    · simp [show a15SubsetSum
          a15MinedProjectorProfile03.centroidVector s.1 ≠ 60 by omega,
        hr0, hr1]
  · have hsum :
        a15SubsetSum a15MinedProjectorProfile03.centroidVector s.1 = 60 := by
      simpa only [a15Eligible, a15DataEligible, a15SubsetSum] using hpos
    rcases hcases.1 hsum with ⟨hr0, hr1⟩
    simp [hsum, hr0, hr1]

private theorem a15MinedProjectorProfile03_base00 :
    a15MinedProjectorProfile03.baseQForm
      (a15ClassIndicator a15MinedProjectorProfile03 0)
      (a15ClassIndicator a15MinedProjectorProfile03 0) = 263 / 144 := by
  rw [a15MinedProjectorProfile03.baseQForm_classIndicator]
  decide +kernel

private theorem a15MinedProjectorProfile03_base01 :
    a15MinedProjectorProfile03.baseQForm
      (a15ClassIndicator a15MinedProjectorProfile03 0)
      (a15ClassIndicator a15MinedProjectorProfile03 1) = 55 / 48 := by
  rw [a15MinedProjectorProfile03.baseQForm_classIndicators]
  decide +kernel

private theorem a15MinedProjectorProfile03_base11 :
    a15MinedProjectorProfile03.baseQForm
      (a15ClassIndicator a15MinedProjectorProfile03 1)
      (a15ClassIndicator a15MinedProjectorProfile03 1) = 71 / 16 := by
  rw [a15MinedProjectorProfile03.baseQForm_classIndicator]
  decide +kernel

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Profile 3 has no direct A15 shell realization. -/
theorem a15MinedProjectorProfile03_no_realization
    (hG : IsHypothetical G) (x : V)
    (realization : A15ShellGramRealization G x
      a15MinedProjectorProfile03.centroidVector) : False := by
  let finite := realization.toFiniteShell G
  let indicator0 := a15ClassIndicator a15MinedProjectorProfile03 0
  let indicator1 := a15ClassIndicator a15MinedProjectorProfile03 1
  let parameter : ℤ :=
    ∑ s : A15EligibleIndex a15MinedProjectorProfile03.centroidVector,
      (finite.multiplicity G s : ℤ) *
        (if a15ProjectorClassCount a15MinedProjectorProfile03.classSizes
          (a15FourSubsetAt s.1) 1 = 3 then 1 else 0)
  have htotal :
      (∑ s : A15EligibleIndex a15MinedProjectorProfile03.centroidVector,
        (finite.multiplicity G s : ℤ)) = 220 := by
    rw [← Nat.cast_sum, finite.sum_multiplicity G,
      secondSubconstituent_card G hG x]
    norm_num
  have hz0Total :
      (∑ s : A15EligibleIndex a15MinedProjectorProfile03.centroidVector,
        (finite.multiplicity G s : ℤ) *
          a15MinedProjectorProfile03.shellDot indicator0 s) = -440 := by
    dsimp only [indicator0]
    simp_rw [a15MinedProjectorProfile03.shellDot_classIndicator]
    rw [realization.sum_multiplicity_shellClassSum G
      a15MinedProjectorProfile03 0]
    decide
  have hz1Total :
      (∑ s : A15EligibleIndex a15MinedProjectorProfile03.centroidVector,
        (finite.multiplicity G s : ℤ) *
          a15MinedProjectorProfile03.shellDot indicator1 s) = -660 := by
    dsimp only [indicator1]
    simp_rw [a15MinedProjectorProfile03.shellDot_classIndicator]
    rw [realization.sum_multiplicity_shellClassSum G
      a15MinedProjectorProfile03 1]
    decide
  have h00Int :
      (∑ s : A15EligibleIndex a15MinedProjectorProfile03.centroidVector,
        (finite.multiplicity G s : ℤ) *
          (a15MinedProjectorProfile03.shellDot indicator0 s) ^ 2) =
        1100 + 8 * parameter := by
    have hpoint (s : A15EligibleIndex
        a15MinedProjectorProfile03.centroidVector) :=
      (a15MinedProjectorProfile03_pointwiseProducts s).1
    dsimp only [indicator0, indicator1] at hpoint ⊢
    simp_rw [hpoint]
    calc
      _ = -3 * (∑ s : A15EligibleIndex
              a15MinedProjectorProfile03.centroidVector,
            (finite.multiplicity G s : ℤ)) -
          4 * (∑ s : A15EligibleIndex
              a15MinedProjectorProfile03.centroidVector,
            (finite.multiplicity G s : ℤ) *
              a15MinedProjectorProfile03.shellDot indicator0 s) +
          8 * parameter := by
        dsimp only [parameter]
        calc
          _ = ∑ s : A15EligibleIndex
                a15MinedProjectorProfile03.centroidVector,
              (-3 * (finite.multiplicity G s : ℤ) -
                4 * ((finite.multiplicity G s : ℤ) *
                  a15MinedProjectorProfile03.shellDot indicator0 s) +
                8 * ((finite.multiplicity G s : ℤ) *
                  (if a15ProjectorClassCount
                    a15MinedProjectorProfile03.classSizes
                      (a15FourSubsetAt s.1) 1 = 3 then 1 else 0))) := by
            apply Finset.sum_congr rfl
            intro s _
            ring
          _ = _ := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
              ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = _ := by rw [htotal, hz0Total]; ring
  have h01Int :
      (∑ s : A15EligibleIndex a15MinedProjectorProfile03.centroidVector,
        (finite.multiplicity G s : ℤ) *
          a15MinedProjectorProfile03.shellDot indicator0 s *
          a15MinedProjectorProfile03.shellDot indicator1 s) =
        1320 - 24 * parameter := by
    have hpoint (s : A15EligibleIndex
        a15MinedProjectorProfile03.centroidVector) :=
      (a15MinedProjectorProfile03_pointwiseProducts s).2.1
    dsimp only [indicator0, indicator1] at hpoint ⊢
    simp_rw [mul_assoc]
    simp_rw [hpoint]
    calc
      _ = -9 * (∑ s : A15EligibleIndex
              a15MinedProjectorProfile03.centroidVector,
            (finite.multiplicity G s : ℤ)) -
          3 * (∑ s : A15EligibleIndex
              a15MinedProjectorProfile03.centroidVector,
            (finite.multiplicity G s : ℤ) *
              a15MinedProjectorProfile03.shellDot indicator0 s) -
          3 * (∑ s : A15EligibleIndex
              a15MinedProjectorProfile03.centroidVector,
            (finite.multiplicity G s : ℤ) *
              a15MinedProjectorProfile03.shellDot indicator1 s) -
          24 * parameter := by
        dsimp only [parameter]
        calc
          _ = ∑ s : A15EligibleIndex
                a15MinedProjectorProfile03.centroidVector,
              (-9 * (finite.multiplicity G s : ℤ) -
                3 * ((finite.multiplicity G s : ℤ) *
                  a15MinedProjectorProfile03.shellDot indicator0 s) -
                3 * ((finite.multiplicity G s : ℤ) *
                  a15MinedProjectorProfile03.shellDot indicator1 s) -
                24 * ((finite.multiplicity G s : ℤ) *
                  (if a15ProjectorClassCount
                    a15MinedProjectorProfile03.classSizes
                      (a15FourSubsetAt s.1) 1 = 3 then 1 else 0))) := by
            apply Finset.sum_congr rfl
            intro s _
            ring
          _ = _ := by
            rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
              Finset.sum_sub_distrib, ← Finset.mul_sum,
              ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = _ := by rw [htotal, hz0Total, hz1Total]; ring
  have h11Int :
      (∑ s : A15EligibleIndex a15MinedProjectorProfile03.centroidVector,
        (finite.multiplicity G s : ℤ) *
          (a15MinedProjectorProfile03.shellDot indicator1 s) ^ 2) =
        2420 + 40 * parameter := by
    have hpoint (s : A15EligibleIndex
        a15MinedProjectorProfile03.centroidVector) :=
      (a15MinedProjectorProfile03_pointwiseProducts s).2.2
    dsimp only [indicator0, indicator1] at hpoint ⊢
    simp_rw [hpoint]
    calc
      _ = -11 * (∑ s : A15EligibleIndex
              a15MinedProjectorProfile03.centroidVector,
            (finite.multiplicity G s : ℤ)) -
          2 * (∑ s : A15EligibleIndex
              a15MinedProjectorProfile03.centroidVector,
            (finite.multiplicity G s : ℤ) *
              a15MinedProjectorProfile03.shellDot indicator0 s) -
          6 * (∑ s : A15EligibleIndex
              a15MinedProjectorProfile03.centroidVector,
            (finite.multiplicity G s : ℤ) *
              a15MinedProjectorProfile03.shellDot indicator1 s) +
          40 * parameter := by
        dsimp only [parameter]
        calc
          _ = ∑ s : A15EligibleIndex
                a15MinedProjectorProfile03.centroidVector,
              (-11 * (finite.multiplicity G s : ℤ) -
                2 * ((finite.multiplicity G s : ℤ) *
                  a15MinedProjectorProfile03.shellDot indicator0 s) -
                6 * ((finite.multiplicity G s : ℤ) *
                  a15MinedProjectorProfile03.shellDot indicator1 s) +
                40 * ((finite.multiplicity G s : ℤ) *
                  (if a15ProjectorClassCount
                    a15MinedProjectorProfile03.classSizes
                      (a15FourSubsetAt s.1) 1 = 3 then 1 else 0))) := by
            apply Finset.sum_congr rfl
            intro s _
            ring
          _ = _ := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
              Finset.sum_sub_distrib, ← Finset.mul_sum,
              ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = _ := by rw [htotal, hz0Total, hz1Total]; ring
  have h00 :
      (∑ s : A15EligibleIndex a15MinedProjectorProfile03.centroidVector,
        (finite.multiplicity G s : ℚ) *
          (a15MinedProjectorProfile03.shellDot indicator0 s : ℚ) ^ 2) =
        1100 + 8 * (parameter : ℚ) := by
    exact_mod_cast h00Int
  have h01 :
      (∑ s : A15EligibleIndex a15MinedProjectorProfile03.centroidVector,
        (finite.multiplicity G s : ℚ) *
          (a15MinedProjectorProfile03.shellDot indicator0 s : ℚ) *
          (a15MinedProjectorProfile03.shellDot indicator1 s : ℚ)) =
        1320 - 24 * (parameter : ℚ) := by
    exact_mod_cast h01Int
  have h11 :
      (∑ s : A15EligibleIndex a15MinedProjectorProfile03.centroidVector,
        (finite.multiplicity G s : ℚ) *
          (a15MinedProjectorProfile03.shellDot indicator1 s : ℚ) ^ 2) =
        2420 + 40 * (parameter : ℚ) := by
    exact_mod_cast h11Int
  let P := realization.complementProjector G
  let v0 := a15ProjectorArrayVector indicator0
  let v1 := a15ProjectorArrayVector indicator1
  have hP : P.PosSemidef :=
    realization.complementProjector_posSemidef G hG x
      a15MinedProjectorProfile03_static.1
  have hq00 : a15RationalMatrixQForm P v0 v0 =
      (215 - 8 * (parameter : ℚ)) / 720 := by
    dsimp only [P, v0]
    rw [a15DirectQForm_expand G a15MinedProjectorProfile03 realization,
      a15MinedProjectorProfile03_base00]
    have h00' :
        (∑ s : A15EligibleIndex a15MinedProjectorProfile03.centroidVector,
          (finite.multiplicity G s : ℚ) *
            a15MinedProjectorProfile03.shellDot indicator0 s *
            a15MinedProjectorProfile03.shellDot indicator0 s) =
          1100 + 8 * (parameter : ℚ) := by
      simpa [pow_two, mul_assoc] using h00
    rw [h00']
    ring
  have hq01 : a15RationalMatrixQForm P v0 v1 =
      (8 * (parameter : ℚ) - 165) / 240 := by
    dsimp only [P, v0, v1]
    rw [a15DirectQForm_expand G a15MinedProjectorProfile03 realization,
      a15MinedProjectorProfile03_base01, h01]
    ring
  have hq11 : a15RationalMatrixQForm P v1 v1 =
      (155 - 8 * (parameter : ℚ)) / 144 := by
    dsimp only [P, v1]
    rw [a15DirectQForm_expand G a15MinedProjectorProfile03 realization,
      a15MinedProjectorProfile03_base11]
    have h11' :
        (∑ s : A15EligibleIndex a15MinedProjectorProfile03.centroidVector,
          (finite.multiplicity G s : ℚ) *
            a15MinedProjectorProfile03.shellDot indicator1 s *
            a15MinedProjectorProfile03.shellDot indicator1 s) =
          2420 + 40 * (parameter : ℚ) := by
      simpa [pow_two, mul_assoc] using h11
    rw [h11']
    ring
  have hq10 : a15RationalMatrixQForm P v1 v0 =
      (8 * (parameter : ℚ) - 165) / 240 := by
    rw [a15RationalMatrixQForm_comm_of_posSemidef hP v1 v0, hq01]
  have hminor := a15RationalMatrixQForm_minor_nonneg hP v0 v1
  rw [hq00, hq01, hq10, hq11] at hminor
  have hdet :
      ((215 - 8 * (parameter : ℚ)) / 720) *
          ((155 - 8 * (parameter : ℚ)) / 144) -
        ((8 * (parameter : ℚ) - 165) / 240) *
          ((8 * (parameter : ℚ) - 165) / 240) =
        -((2 * (parameter : ℚ) - 35) ^ 2) / 8100 := by
    ring
  rw [hdet] at hminor
  have hodd : 2 * parameter - 35 ≠ 0 := by omega
  have hoddQ : 2 * (parameter : ℚ) - 35 ≠ 0 := by
    exact_mod_cast hodd
  have hsquare : 0 < (2 * (parameter : ℚ) - 35) ^ 2 :=
    sq_pos_of_ne_zero hoddQ
  linarith

/-- Mined norm profile 12 is the class-only profile 3 and is impossible. -/
theorem a15MinedNormProfile12_no_realization
    (hG : IsHypothetical G) (x : V)
    (realization : A15ShellGramRealization G x
      (a15SmallProfile a15MinedNormProfile12)) : False := by
  have hrealization : A15ShellGramRealization G x
      a15MinedProjectorProfile03.centroidVector :=
    a15MinedProjectorProfile03_centroidVector.symm ▸ realization
  exact a15MinedProjectorProfile03_no_realization G hG x hrealization

end SRG266
